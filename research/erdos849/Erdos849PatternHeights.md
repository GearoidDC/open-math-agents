# Finite exclusions for the two four-column patterns

No value up to $10^{136}$ occurs in all four columns $3,5,7,8$. No value up to $10^{144}$ occurs in all four columns $5,6,7,8$. These finite exclusions apply to coefficients with any factorization.

For values through $10^{128}$, either pattern would supply five distinct rows including the edge, so the earlier search applies. Above that height the search tests each possible column-eight row number against the simultaneous residue images of the three other columns. The two CRT wheels and the bit masks in the existing checker are described in the finite-search report. Controls compare the native implementation against brute force and recover the three proper occurrences of 3003. [Earlier search and algorithm](Erdos849Focused128.md) · [Verifier](Erdos849FocusedCRT.py)

| Columns | Value interval | Column-eight row numbers tested | CRT joins | After bit masks | After all local tests |
|---|---|---:|---:|---:|---:|
| $3,5,7,8$ | $(10^{128},10^{132}]$ | 81,395,712,063,470,609 | 837,851,898,923 | 150,174,772 | 0 |
| $3,5,7,8$ | $(10^{132},10^{136}]$ | 257,395,841,891,810,965 | 2,649,520,406,792 | 474,835,660 | 0 |
| $5,6,7,8$ | $(10^{128},10^{132}]$ | 81,395,712,063,470,609 | 17,606,102,002 | 62,255 | 0 |
| $5,6,7,8$ | $(10^{132},10^{144}]$ | 3,645,311,381,444,626,705 | 788,490,019,631 | 2,787,090 | 0 |

Run the following commands with a C compiler available. On Windows the verifier accepts `--cc` followed by the path to Lean's bundled Clang.

```sh
python Erdos849FocusedCRT.py --columns 3 5 7 8 --lower 128 --upper 132
python Erdos849FocusedCRT.py --columns 3 5 7 8 --lower 132 --upper 136
python Erdos849FocusedCRT.py --columns 5 6 7 8 --lower 128 --upper 132
python Erdos849FocusedCRT.py --columns 5 6 7 8 --lower 132 --upper 144
```
