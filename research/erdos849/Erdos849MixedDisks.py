"""Check additional prime residues excluded through a common height."""

import json
from math import isqrt
from pathlib import Path

from Erdos849ResidueDisks import fibers,verify


def exclusions():
    columns,height,certificates = json.loads(Path(__file__).with_suffix('.json').read_bytes())
    assert columns==[8,7,6,5] and height==170 and certificates
    excluded = {}
    for prime,values,records in certificates:
        assert prime>8 and all(prime%d for d in range(2,isqrt(prime)+1))
        assert prime not in excluded and len(values)==len(set(values)) and values
        grid = fibers(columns,prime,True)
        assert all(v in grid for v in values)
        expected = {s for v in values for s in grid[v]}
        assert len(records)==len(expected) and {tuple(r[0]) for r in records}==expected
        for record in records:
            verify(columns,prime,height,record)
        excluded[prime] = set(values)
        print(prime,values,len(records),'verified disks',flush=True)
    return excluded


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Run with assertions enabled')
    exclusions()
