"""Compute the largest 53-smooth lower endpoint at a positive distance at most 51.

Source: Rafael von Känel and Benjamin Matschke, S-unit equation, Table 1.
The published data file is streamed and only an aggregate and its witness are retained.
"""
from hashlib import sha256
from math import gcd
import re
from urllib.request import urlopen

url = "https://bmatschke.github.io/solving-classical-diophantine-equations/s-unit-equation/solutions_2_3_5_7_11_13_17_19_23_29_31_37_41_43_47_53.txt"
line_format = re.compile(rb"^(\d+):\s*(\d+)\s*\+\s*(\d+)\s*=\s*(\d+)\s*\(")
count = 0
maximum = (0, 0, 0, 0)
digest = sha256()
with urlopen(url, timeout=90) as response:
    for line in response:
        digest.update(line)
        if line.startswith(b"#") or not line.strip():
            continue
        match = line_format.match(line)
        if not match:
            raise ValueError("Unexpected row format")
        _, a, b, c = map(int, match.groups())
        if not (0 < a <= b and a + b == c and gcd(a,b) == 1):
            raise ValueError("Bad normalized triple")
        count += 1
        if a <= 51:
            maximum = max(maximum, ((51//a)*b, a, b, c))
if count != 1663449:
    raise ValueError(f"Expected the complete 1,663,449 rows, received {count}")
print("rows", count, "sha256", digest.hexdigest(), "maxLower and witness", maximum)
