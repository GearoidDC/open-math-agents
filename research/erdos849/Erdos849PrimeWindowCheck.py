"""Verify finite prime-gap inputs and check the local claims at small heights."""

from bisect import bisect_right
from math import comb, isqrt


def main():
    limit=2_000_000
    is_prime=bytearray([1])*(limit+1)
    is_prime[:2]=b'\0\0'
    for p in range(2,isqrt(limit)+1):
        if is_prime[p]:
            is_prime[p*p::p]=b'\0'*((limit-p*p)//p+1)
    primes=[p for p in range(2,limit+1) if is_prime[p]]
    tested=0
    for r,q in zip(primes,primes[1:]):
        if r>=10**6:
            break
        assert (q-r-1)**2 < 4*r
        tested+=1
    assert 30*1476**3<10**11 and (1476-1)**2<4*10**6
    print(f"{tested} consecutive prime gaps with left endpoint below one million passed.")
    rows={}
    tests=0
    for n in range(4,201):
        for k in range(2,n//2+1):
            a=comb(n,k)
            p=max(r for r in primes[:bisect_right(primes,n)] if a%r==0)
            q=primes[bisect_right(primes,p)]
            prime_in_block=any(is_prime[n-k+1:n+1])
            assert prime_in_block==(p<=n<q)
            if prime_in_block:
                assert a%(p*p)
            for m,j in rows.get(a,[]):
                assert m<n and j>k
                H=n-m
                absent=[r for r in primes[:bisect_right(primes,m)] if a%r]
                assert all(4*r<=(n-r)**2 for r in absent)
                assert (m-j+1)**(j-k)*(m-j)**H<=j**(j-k)*m**H
                tests+=1
            rows.setdefault(a,[]).append((n,k))
    assert {(14,6),(15,5),(78,2)}==set(rows[3003])
    assert not any(is_prime[77:79]) and is_prime[13]
    print(f"Prime-window equivalence checked through row 200, with {tests} collision pairs.")


if __name__=='__main__':
    main()
