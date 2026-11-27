"""Replay the four-column certificate for columns 5, 6, 7, and 8."""

from itertools import product
from pathlib import Path
import gzip
import json

from Erdos849PatternThree import check_hosts, check_piece
from Erdos849PatternThreeCRT import sieve


COLUMNS = (8, 7, 6, 5)
DECADE = 128
BUDGET = 35519
RATE = 36


def main():
    if not __debug__:
        raise RuntimeError("This verifier requires Python assertions.")
    with gzip.open(Path(__file__).with_suffix(".json.gz"), "rt", encoding="ascii") as f:
        pieces = json.load(f)
    expected = list(product(*(range(k) for k in COLUMNS)))
    assert sorted(tuple(offsets) for offsets, _, _ in pieces) == expected
    for offsets, order, terms in pieces:
        assert order > 0 and terms
        check_piece(COLUMNS, tuple(offsets), order, terms, DECADE, BUDGET, RATE)
    check_hosts(DECADE, BUDGET, RATE)
    print(f"Verified all {len(pieces)} branches and the 31-distinct-primes bound.", flush=True)
    sieve(large=9, join=True, decade=DECADE, budget=BUDGET, rate=RATE, columns=(5, 6, 7))


if __name__ == "__main__":
    main()
