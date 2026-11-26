#!/usr/bin/env python3
"""Verify this package: build, axiom audit, planted controls. Writes CHECK_RESULT.json.

    python3 check.py            # needs elan on PATH; runs `lake exe cache get` then `lake build`
    python3 check.py --no-build # audit + controls only, on an existing build

PASS requires ALL of:
  * `lake build` exits 0 (every module of the closure compiles);
  * AxiomAudit.lean: every declaration in AUDIT.txt reports axioms within {propext, Classical.choice, Quot.sound},
    and the set of declarations reported equals the set listed (a missing report fails; a count is never used);
  * PlantedSorry.lean: the planted `sorry` IS reported as sorryAx (the audit can fail);
  * each controls/*.lean errors at exactly the lines listed in controls/EXPECT.json (set comparison) and nowhere else;
  * every source file hashes to MANIFEST.sha256 (the check ran on the shipped bytes).
"""
import hashlib, json, os, re, subprocess, sys
os.chdir(os.path.dirname(os.path.abspath(__file__)))
STD = {"propext", "Classical.choice", "Quot.sound"}
res = {"steps": {}}

def run(cmd):
    r = subprocess.run(cmd, capture_output=True, text=True)
    return r.returncode, (r.stdout + r.stderr).replace("\r", "")

def axioms_of(out):
    """{decl: set(axioms)} from `#print axioms` output, keyed by the name Lean prints."""
    got = {}
    # one report per line; a name may contain primes (norm_le' prints as 'X.norm_le'' )
    for m in re.finditer(r"^'(.+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)\s*$", out, re.M):
        got[m.group(1)] = {a.strip() for a in (m.group(2) or "").split(",") if a.strip()}
    return got

ok = True
bad = []
for line in open("MANIFEST.sha256"):
    h, p = line.rstrip("\n").split("  ", 1)
    if hashlib.sha256(open(p, "rb").read()).hexdigest() != h:
        bad.append(p)
res["steps"]["manifest"] = {"ok": not bad, "mismatch": bad}
ok &= not bad

if "--no-build" not in sys.argv:
    rc, _ = run(["lake", "exe", "cache", "get"])
    rc, out = run(["lake", "build"])
    res["steps"]["build"] = {"ok": rc == 0, "rc": rc, "tail": out[-3000:]}
    ok &= rc == 0

want = [l.split()[2] for l in open("AUDIT.txt").read().split("\n") if l.startswith("#print axioms ")]
rc, out = run(["lake", "env", "lean", "AxiomAudit.lean"])
got = axioms_of(out)
missing = sorted(set(want) - set(got)); extra = sorted(set(got) - set(want))
nonstd = {d: sorted(a - STD) for d, a in got.items() if a - STD}
a_ok = rc == 0 and not missing and not extra and not nonstd
res["steps"]["axiom_audit"] = {"ok": a_ok, "rc": rc, "declarations": len(want), "missing": missing,
                               "extra": extra, "nonstandard": nonstd}
ok &= a_ok

rc, out = run(["lake", "env", "lean", "PlantedSorry.lean"])
pg = axioms_of(out)
p_ok = "sorryAx" in pg.get("StandalonePlant.planted", set())
res["steps"]["plant_sorry"] = {"ok": p_ok, "reported": sorted(pg.get("StandalonePlant.planted", []))}
ok &= p_ok

expect = json.load(open("controls/EXPECT.json"))
for f, lines in sorted(expect.items()):
    rc, out = run(["lake", "env", "lean", f])
    got_lines = sorted({int(m.group(1)) for m in re.finditer(r"^" + re.escape(f) + r":(\d+):\d+: error", out, re.M)})
    c_ok = rc != 0 and got_lines == sorted(lines)
    res["steps"]["control:" + f] = {"ok": c_ok, "rc": rc, "error_lines": got_lines, "want": sorted(lines)}
    ok &= c_ok

res["verdict"] = "PASS" if ok else "FAIL"
res["manifest_sha256"] = hashlib.sha256(open("MANIFEST.sha256", "rb").read()).hexdigest()
json.dump(res, open("CHECK_RESULT.json", "w"), indent=1, sort_keys=True)
print(json.dumps({k: v["ok"] for k, v in res["steps"].items()}, indent=1))
print("VERDICT", res["verdict"], "manifest", res["manifest_sha256"][:12])
sys.exit(0 if ok else 1)
