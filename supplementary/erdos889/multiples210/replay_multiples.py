"""Verify the Erdős 889 supplementary proofs on the pinned Lean checkout.

Run python replay_multiples.py PATH_TO_FORMAL_CONJECTURES from a checkout of
this supplement. The checkout passed as the argument must be prepared with the
open-math-agents setup, including its two merged Erdős 889 reduction modules.
Use the Lean and Lake versions specified in that checkout's lean-toolchain.
"""
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time


def main():
    if len(sys.argv) not in (2, 3):
        raise SystemExit(__doc__)
    checkout = Path(sys.argv[1]).resolve()
    script = Path(__file__).resolve()
    inputs = script.parent
    if sys.argv[2:] != ["--inside-lake"]:
        commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=checkout, text=True).strip()
        if not commit.startswith("9097e2f90e66"):
            raise SystemExit(f"Expected formal-conjectures 9097e2f90e66, found {commit}")
        subprocess.run(["lake", "env", sys.executable, str(script), str(checkout), "--inside-lake"],
                       cwd=checkout, check=True)
        return
    # Compile supplementary imports first, using the names declared in the sources.
    files = {p.stem:p for p in inputs.glob("*.lean")}
    dependencies = {}
    for name, source in files.items():
        imports = [line.split()[1] for line in source.read_text(encoding="utf-8-sig").splitlines()
                   if line.startswith("import ")]
        dependencies[name] = set(imports) & files.keys()
    env = os.environ.copy()
    old = [str((checkout / p).resolve()) for p in env.get("LEAN_PATH", "").split(os.pathsep) if p]
    with tempfile.TemporaryDirectory(prefix="erdos889-multiples-") as work:
        folder = Path(work)
        env["LEAN_PATH"] = os.pathsep.join([work, *old])
        for source in files.values():
            shutil.copy2(source, folder/source.name)
        pending = set(files)
        while pending:
            ready = sorted(n for n in pending if not dependencies[n] & pending)
            if not ready:
                raise SystemExit("Cycle between supplementary module imports")
            for name in ready:
                start = time.monotonic()
                print(f"Checking {name}", flush=True)
                audit = subprocess.run(["lean", "-j1", "-DwarningAsError=true", "-o", f"{name}.olean",
                                        f"{name}.lean"], cwd=folder, env=env, timeout=1800,
                                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
                print(audit.stdout, end="", flush=True)
                audit.check_returncode()
                allowed = {"propext", "Classical.choice", "Quot.sound"}
                for entry in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", audit.stdout):
                    extra = {a.strip() for a in entry.split(",") if a.strip()} - allowed
                    if extra:
                        raise SystemExit(f"Unexpected axioms in {name}: {sorted(extra)}")
                print(f"Passed in {time.monotonic()-start:.1f} seconds", flush=True)
                pending.remove(name)


if __name__ == "__main__":
    main()
