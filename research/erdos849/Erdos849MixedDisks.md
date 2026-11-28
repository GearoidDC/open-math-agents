# Additional residues for the finite four-column search

For each prime and coefficient residue recorded in the archive, there is no admissible common value in columns $5,6,7,8$ up to $10^{170}$ with that residue. The verifier enumerates all tuples over that prime giving the specified residue, modulo the two even-column reflections. For each tuple, exact evaluations on its Hensel lifts force auxiliary polynomials to vanish at any integer solution. Enumeration over a second prime rules out their simultaneous vanishing. These checks impose no prime-count assumption. [Method and proof](Erdos849ResidueDisks.md)

Run `python -B Erdos849MixedDisks.py` to verify the full archive and print the excluded values at each prime. The finite search can select any verified subset. [Verifier](Erdos849MixedDisks.py) · [Coefficients and residues](Erdos849MixedDisks.json)
