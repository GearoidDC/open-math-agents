"""Rebuild the Erdős 849 deductions using an existing Lean/Mathlib installation."""

import argparse
import os
from pathlib import Path
import subprocess
import tempfile


MODULES = (
    "Erdos849Bound", "Erdos849Cases", "Erdos849FiniteBridge",
    "Erdos849FiniteData", "Erdos849Finite", "Erdos849Factors",
    "Erdos849PatternBridge", "Erdos849PrimeHosts", "Erdos849HostCofactors",
    "Erdos849HostSelection", "Erdos849NearPrimeCongruence",
    "Erdos849PowerCollision", "Erdos849TenPrimes", "Erdos849ElevenColumns",
    "Erdos849ElevenHosts", "Erdos849ElevenCollision", "Erdos849ElevenPrimes",
    "Erdos849BoundedOmega", "Erdos849SparseCollision", "Erdos849TwoColumns",
    "Erdos849EffectiveMultiplicity", "Erdos849Threshold", "Erdos849FiveSeven",
    "Erdos849FourteenGraph", "Erdos849SixteenGraph", "Erdos849Interval105",
    "Erdos849LindDiagonal", "Erdos849Interval128", "Erdos849PrimeWindow",
    "Erdos849EighteenGraph", "Erdos849NineteenGraph", "Erdos849TwentyGraph",
    "Erdos849FallingBounds",
)

THEOREMS = (
    ("Erdos849ElevenPrimes","eleven_distinct_prime_factors"),
    ("Erdos849EffectiveMultiplicity","many_primes_above_cutoff"),
    ("Erdos849BoundedOmega","finite_three_rows_with_bounded_omega"),
    ("Erdos849FiveSeven","no_collision"),
    ("Erdos849FourteenGraph","fourteen_distinct_prime_factors"),
    ("Erdos849SixteenGraph","sixteen_distinct_prime_factors"),
    ("Erdos849Interval105","five_rows_above_cutoff"),
    ("Erdos849Interval128","five_rows_above_cutoff"),
    ("Erdos849LindDiagonal","unique_on_diagonal"),
    ("Erdos849LindDiagonal","earlier_column_bound"),
    ("Erdos849PrimeWindow","contains_iff"),
    ("Erdos849PrimeWindow","gap_size"),
    ("Erdos849PrimeWindow","slope_power"),
    ("Erdos849EighteenGraph","column_bound"),
    ("Erdos849EighteenGraph","eighteen_distinct_prime_factors"),
    ("Erdos849NineteenGraph","column_bound"),
    ("Erdos849NineteenGraph","nineteen_distinct_prime_factors"),
    ("Erdos849TwentyGraph","column_bound"),
    ("Erdos849TwentyGraph","twenty_distinct_prime_factors"),
    ("Erdos849FallingBounds","row_interval"),
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean", help="Lean 4.33.1 executable")
    parser.add_argument("--project", type=Path,
                        help="existing Lake project with mathlib v4.33.1 built")
    args = parser.parse_args()
    source = Path(__file__).resolve().parent
    executable = str(Path(args.lean).resolve()) if Path(args.lean).is_file() else args.lean
    with tempfile.TemporaryDirectory(prefix="erdos849-") as tmp:
        env = os.environ.copy()
        paths = [tmp]
        if args.project:
            project = args.project.resolve()
            paths.append(str(project / ".lake/build/lib/lean"))
            paths.extend(str(p) for p in
                         sorted((project / ".lake/packages").glob("*/.lake/build/lib/lean")))
        if env.get("LEAN_PATH"):
            paths.append(env["LEAN_PATH"])
        env["LEAN_PATH"] = os.pathsep.join(paths)
        for name in MODULES:
            print(f"Checking {name}", flush=True)
            subprocess.run([executable, "-j", "1", "-o", str(Path(tmp) / (name + ".olean")),
                            name + ".lean"], cwd=source, env=env, check=True)
        imports = [f"import {module}" for module in dict.fromkeys(m for m, _ in THEOREMS)]
        audits = [f"{command} {module}.{theorem}" for module, theorem in THEOREMS
                  for command in ("#check", "#print axioms")]
        subprocess.run([executable, "-j", "1", "--stdin"], cwd=source, env=env,
                       input="\n".join(imports + audits) + "\n", text=True, check=True)


if __name__ == "__main__":
    main()
