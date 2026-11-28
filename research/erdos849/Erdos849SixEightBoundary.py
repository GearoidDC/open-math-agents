"""Certify nontorsion of the two infinity points of the reflected 6,8 pair."""

from math import gcd

from Erdos849FiveEightQuintic import distinct_powers, factor_degrees, logs, real_polynomial
from Erdos849SmallestCurve import critical_polynomial
from Erdos849ThreeFiveCurve import gcd as polynomial_gcd
from Erdos849ThreeFiveCurve import cyclotomic_indices_at_most, polynomial_from_traces, prime, trim


def counts(p, d, both_signs=False):
    log = logs(p,d)
    q = len(log)
    zero = q-1
    tables = [(bytearray(q),log[224 % p],(-5,-3,-1,1,3,5)),
              (bytearray(q),log[224 % p],(1,9,25)),
              (bytearray(q),0,(1,9,25,49))]
    if both_signs:
        tables.append((bytearray(q),0,(-7,-5,-3,-1,1,3,5,7)))
    for start in range(0,q,p):
        digits = list(log[start:start+p])*2
        for x in range(p):
            for table,shift,roots in tables:
                entries = [digits[p+x-r%p] for r in roots]
                table[zero if -1 in entries else (shift+sum(entries))%zero] += 1
    full, smaller, right = [row[0] for row in tables[:3]]
    count_small = 1+sum(x*y for x,y in zip(smaller,right))
    infinity = 2 if d%2==0 or pow(14,(p-1)//2,p)==1 else 0
    count_full = infinity+sum(x*y for x,y in zip(full,right))
    if not both_signs:
        return count_small,count_full
    other = tables[3][0]
    return (count_small,count_full,1+sum(x*y for x,y in zip(smaller,other)),
            infinity+sum(x*y for x,y in zip(full,other)))


def distinct_octic_powers(poly):
    prime_mod = 1000003
    assert prime(prime_mod)
    indices = cyclotomic_indices_at_most(56)
    sums = [8]
    for j in range(1,8*max(indices)+1):
        v = j*poly[8-j] if j<=8 else 0
        v += sum(poly[8-i]*sums[j-i] for i in range(1,min(8,j-1)+1))
        sums.append(-v % prime_mod)
    for n in indices:
        co = [1]
        for j in range(1,9):
            value = sum(co[j-i]*sums[n*i] for i in range(1,j+1))
            co.append(-value*pow(j,-1,prime_mod) % prime_mod)
        fp = co[::-1]
        der = trim([i*fp[i]%prime_mod for i in range(1,9)])
        assert len(polynomial_gcd(fp,der,prime_mod)) == 1


def full_pair():
    samples = [(18,28,28,54),(144,168,160,188),(1350,1348,1336,1290),
               (14524,14348,14748,15008),(160578,160948,160008,160314),
               (1772496,1768920,1770352,1769036)]
    assert [counts(11,d,True) for d in range(1,7)] == samples
    for dim, traces, modulus in (
        (4,[k-b for k,b,_,_ in samples],5),
        (4,[k-e for k,_,e,_ in samples],None),
        (6,[b+e-c-k for k,b,e,c in samples],41),
    ):
        top = polynomial_from_traces([2*dim]+traces[:dim])
        poly = [top[dim-i]*11**(dim-i) for i in range(dim)]+top
        if modulus:
            distinct_powers(poly,modulus)
        else:
            g = real_polynomial(poly,11)
            assert g == [-176,-88,14,10,1] and factor_degrees(g,7) == [2,2]
            for b in range(-176,177):
                if not b or -176 % b:
                    continue
                d = -176//b
                numerator = -88-10*b
                if numerator % (d-b) == 0:
                    a = numerator//(d-b)
                    assert b+d+a*(10-a) != 14
            distinct_octic_powers(poly)
        print("Absolutely simple pair component",dim,poly)


def main():
    if not __debug__:
        raise RuntimeError("Run with assertions enabled.")
    expected = {
        11: ([(18,28),(144,168),(1350,1348),(14524,14348)],39996),
        17: ([(19,32),(337,338),(4876,4928),(84053,84646)],38876),
        19: ([(32,37),(408,451),(6626,6910),(130148,129719)],104762),
    }
    for p,(samples,order) in expected.items():
        assert len(polynomial_gcd(critical_polynomial(6,p),critical_polynomial(8,p),p)) == 1
        assert [counts(p,d) for d in range(1,5)] == samples
        top = polynomial_from_traces([8]+[a-b for a,b in samples])
        poly = [top[4-i]*p**(4-i) for i in range(4)]+top
        sign = 1 if pow(14,(p-1)//2,p)==1 else -1
        assert sum(v*sign**i for i,v in enumerate(poly)) == order
        print(p,"Prym Frobenius",poly,"quadratic sign",sign,"twist order",order)
    assert gcd(*(order for _,order in expected.values())) == 2
    assert all(any(order%p for l,(_,order) in expected.items() if l!=p) for p in expected)
    full_pair()


if __name__ == "__main__":
    main()
