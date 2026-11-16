package tun2connect

import (
	"container/list"
	"errors"
	"math"
	"net/netip"
	"strings"
	"sync"
	"time"

	"golang.org/x/net/dns/dnsmessage"
)

// Synthetic pools. v4 is CGNAT space: link-local would be leak-proof at
// the first router (RFC 3927) but SSRF guards in HTTP clients commonly
// block 169.254/16, which would break legitimate egress. v6 is the
// discard-only prefix (RFC 6666): a flow that ever escapes through a
// stray interface is blackholed by the first conforming router instead
// of reaching a routable ULA network. The top /24 (v4) and /120 (v6) of
// each pool are never handed out: adapters place their own interface and
// resolver addresses there.
var (
	v4Pool     = netip.MustParsePrefix("100.64.0.0/10")
	v6Pool     = netip.MustParsePrefix("100::/64")
	v4Reserved = netip.MustParsePrefix("100.127.255.0/24")
	v6Reserved = netip.MustParsePrefix("100::ffff:ffff:ffff:ff00/120")
)

// maxSyntheticNames bounds the names remembered per address family. The
// guest chooses the names, and in namespace mode this state lives outside
// the sandbox, so its size must not depend on guest behavior. The least
// recently resolved or dialed name is forgotten first.
const maxSyntheticNames = 1 << 16

// DefaultTTL is short so clients soon drop an address that went stale,
// either because its name was forgotten or because the resolver restarted.
const DefaultTTL = 30 * time.Second

// ErrPoolExhausted is returned when a pool has no addresses left; the
// DNS codec turns it into SERVFAIL, which fails closed.
var ErrPoolExhausted = errors.New("tun2connect: synthetic address pool exhausted")

// VirtualDNS is the name-preservation contract. It never resolves
// upstream: it invents one synthetic address per (name, family) and
// remembers the pairing so the engine can recover the name at dial time.
//
// Addresses are never reused within one VirtualDNS lifetime. When a name
// is forgotten under the memory bound, its address stays unassigned: a
// guest dialing a cached copy gets a reverse miss, the destination is
// forwarded as a literal in the synthetic range, and the boundary denies
// it. A stale cache therefore fails closed instead of reaching the name
// that would otherwise have inherited the address.
type VirtualDNS struct {
	// TTL is sent in whole seconds. Set it before the first query.
	TTL time.Duration

	mu      sync.Mutex
	v4, v6  family
	reverse map[netip.Addr]*list.Element
}

type family struct {
	pool, reserved netip.Prefix
	last           netip.Addr
	names          map[string]*list.Element
	order          list.List // front is most recently used
}

type binding struct {
	name string
	addr netip.Addr
}

func NewVirtualDNS() *VirtualDNS {
	return &VirtualDNS{
		TTL:     DefaultTTL,
		v4:      family{pool: v4Pool, reserved: v4Reserved, last: v4Pool.Addr(), names: make(map[string]*list.Element)},
		v6:      family{pool: v6Pool, reserved: v6Reserved, last: v6Pool.Addr(), names: make(map[string]*list.Element)},
		reverse: make(map[netip.Addr]*list.Element),
	}
}

// Generations is how many equal slices NewGenerationDNS splits each pool
// into: a /14 of the IPv4 pool and a /68 of the IPv6 pool.
const Generations = 1 << generationBits

const generationBits = 4

// NewGenerationDNS returns a resolver that allocates only from slice
// (generation mod Generations) of each pool. Consecutive generations never
// hand out the same address, so a fresh adapter cannot give a name an
// address that a restored guest still caches from the previous generation
// (spec/draft/lifecycle.md Section 3, option (b)).
func NewGenerationDNS(generation uint) *VirtualDNS {
	d := NewVirtualDNS()
	slice := generation % Generations
	d.v4.pool, d.v4.last = generationSlice(v4Pool, slice)
	d.v6.pool, d.v6.last = generationSlice(v6Pool, slice)
	return d
}

// generationSlice returns slice g of pool and its first address, which
// allocation starts after.
func generationSlice(pool netip.Prefix, g uint) (netip.Prefix, netip.Addr) {
	addr := pool.Addr().AsSlice()
	for i := range generationBits {
		if g&(1<<(generationBits-1-i)) != 0 {
			bit := pool.Bits() + i
			addr[bit/8] |= 0x80 >> (bit % 8)
		}
	}
	base, _ := netip.AddrFromSlice(addr)
	return netip.PrefixFrom(base, pool.Bits()+generationBits), base
}

func canonical(name string) string {
	return strings.ToLower(strings.TrimSuffix(name, "."))
}

// Resolve4 returns the synthetic IPv4 address for name, allocating one
// if the name is new. The mapping holds while the name stays among the
// most recently used maxSyntheticNames names of its family.
func (d *VirtualDNS) Resolve4(name string) (netip.Addr, error) {
	return d.resolve(name, false)
}

// Resolve6 is Resolve4 for the IPv6 pool.
func (d *VirtualDNS) Resolve6(name string) (netip.Addr, error) {
	return d.resolve(name, true)
}

func (d *VirtualDNS) resolve(name string, v6 bool) (netip.Addr, error) {
	name = canonical(name)
	if name == "" {
		return netip.Addr{}, errors.New("tun2connect: empty name")
	}
	d.mu.Lock()
	defer d.mu.Unlock()
	f := &d.v4
	if v6 {
		f = &d.v6
	}
	if element, ok := f.names[name]; ok {
		f.order.MoveToFront(element)
		return element.Value.(*binding).addr, nil
	}
	addr := f.last.Next()
	if !f.pool.Contains(addr) || f.reserved.Contains(addr) {
		return netip.Addr{}, ErrPoolExhausted
	}
	if f.order.Len() >= maxSyntheticNames {
		oldest := f.order.Back()
		evicted := oldest.Value.(*binding)
		delete(f.names, evicted.name)
		delete(d.reverse, evicted.addr)
		f.order.Remove(oldest)
	}
	f.last = addr
	element := f.order.PushFront(&binding{name: name, addr: addr})
	f.names[name] = element
	d.reverse[addr] = element
	return addr, nil
}

// Reverse recovers the name behind a synthetic address and marks it as
// recently used. ok=false means the address was never handed out by this
// resolver or its name has since been forgotten.
func (d *VirtualDNS) Reverse(addr netip.Addr) (string, bool) {
	d.mu.Lock()
	defer d.mu.Unlock()
	element, ok := d.reverse[addr.Unmap()]
	if !ok {
		return "", false
	}
	b := element.Value.(*binding)
	f := &d.v4
	if b.addr.Is6() {
		f = &d.v6
	}
	f.order.MoveToFront(element)
	return b.name, true
}

// HandleQuery answers one guest DNS query from the synthetic pools.
// A/AAAA get an invented address; every other type gets an empty
// authoritative answer, so no record type becomes a side channel.
func (d *VirtualDNS) HandleQuery(query []byte) ([]byte, error) {
	var p dnsmessage.Parser
	hdr, err := p.Start(query)
	if err != nil {
		return nil, err
	}
	q, err := p.Question()
	if err != nil {
		return nil, err
	}

	rcode := dnsmessage.RCodeSuccess
	var addr netip.Addr
	answer := false
	if q.Class == dnsmessage.ClassINET {
		switch q.Type {
		case dnsmessage.TypeA:
			addr, err = d.Resolve4(q.Name.String())
			answer = err == nil
		case dnsmessage.TypeAAAA:
			addr, err = d.Resolve6(q.Name.String())
			answer = err == nil
		}
		if err != nil {
			rcode = dnsmessage.RCodeServerFailure
		}
	}

	b := dnsmessage.NewBuilder(make([]byte, 0, 512), dnsmessage.Header{
		ID:                 hdr.ID,
		Response:           true,
		OpCode:             hdr.OpCode,
		Authoritative:      true,
		RecursionDesired:   hdr.RecursionDesired,
		RecursionAvailable: true,
		RCode:              rcode,
	})
	b.EnableCompression()
	if err := b.StartQuestions(); err != nil {
		return nil, err
	}
	if err := b.Question(q); err != nil {
		return nil, err
	}
	if answer {
		if err := b.StartAnswers(); err != nil {
			return nil, err
		}
		rh := dnsmessage.ResourceHeader{Name: q.Name, Type: q.Type, Class: q.Class, TTL: ttlSeconds(d.TTL)}
		if q.Type == dnsmessage.TypeA {
			err = b.AResource(rh, dnsmessage.AResource{A: addr.As4()})
		} else {
			err = b.AAAAResource(rh, dnsmessage.AAAAResource{AAAA: addr.As16()})
		}
		if err != nil {
			return nil, err
		}
	}
	return b.Finish()
}

// RFC 2181 caps a DNS TTL at 2^31-1 seconds.
func ttlSeconds(ttl time.Duration) uint32 {
	return uint32(min(max(ttl/time.Second, 0), math.MaxInt32))
}
