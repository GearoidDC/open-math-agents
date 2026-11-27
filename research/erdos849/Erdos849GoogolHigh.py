"""Verify the high-column part of the extension from 10^100 to 10^105."""

from Erdos849High import high_search
from Erdos849Interval import primes_to, self_check
from Erdos849Wheel import check_wheel


if __name__ == "__main__":
    check_wheel()
    self_check(primes_to(499))
    collisions = high_search(10**100,10**105)
    assert not collisions, "Inspect these pair collisions for further representations"
