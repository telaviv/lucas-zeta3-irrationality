"""Check that every Lean declaration and file cited in paper/main.tex exists at the given commit.

Usage (from lean_fibzeta/):  python paper/check_lean_names.py [commit]   (default: HEAD)
For each \\lean{...} token in main.tex:
  * a token with '/' must be a file or folder of the repository at the commit;
  * a dotted or underscore identifier (or a capitalised one) must be declared (theorem/lemma/def/structure/...) in
    LucasU/ at the commit, with a full name equal to the token or to `LucasU.<token>`.
  * a token `theorem <name> : ...` checks <name>.
Tokens that are not Lean names (axiom names, tactic names, library names) are listed in SKIP.
Adapted from lean_chi2/paper_q/check_lean_names.py.
"""
import re
import subprocess
import sys

COMMIT = sys.argv[1] if len(sys.argv) > 1 else "HEAD"
tex = open("paper/main.tex", encoding="utf-8").read()
toks = re.findall(r"\\lean\{((?:[^{}]|\{[^{}]*\})*)\}", tex)


def clean(t):
    t = t.replace("\\slash{}", "/").replace("\\_", "_").replace("\\textunderscore", "_")
    return t.strip()


SKIP = {"propext", "Classical.choice", "Quot.sound", "sorry", "native_decide", "LucasU", "NOTICE", "lean/",
        "RatFunc.X", "Nat.fib", "deriv", "Irrational", "tsum", "Admissible a E"}

files = subprocess.run(["git", "ls-tree", "-r", "--name-only", COMMIT], capture_output=True, text=True,
                       encoding="utf-8").stdout.split("\n")
fileset = set(files)
dirs = {"/".join(f.split("/")[:i]) for f in files for i in range(1, f.count("/") + 1)}

decls = {}  # short name -> list of (full name, file)
for f in files:
    if not (f.startswith("LucasU") and f.endswith(".lean")):
        continue
    src = subprocess.run(["git", "show", f"{COMMIT}:{f}"], capture_output=True, text=True,
                         encoding="utf-8").stdout
    ns = []
    for line in src.split("\n"):
        m = re.match(r"^namespace\s+(\S+)", line)
        if m:
            ns.append(m.group(1))
            continue
        m = re.match(r"^end\s+(\S+)", line)
        if m and ns and ns[-1] == m.group(1):
            ns.pop()
            continue
        m = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(?:noncomputable\s+)?"
                     r"(theorem|lemma|def|structure|abbrev|instance|inductive)\s+([^\s(:{\[]+)", line)
        if m:
            name = m.group(2)
            full = ".".join(ns + [name])
            decls.setdefault(name.split(".")[-1], []).append((full, f))

bad = []
checked = 0
for t in toks:
    c = clean(t)
    m = re.match(r"theorem\s+(\S+)\s*:", c)
    if m:
        c = m.group(1)
    if c in SKIP or not c:
        continue
    if "/" in c or c.endswith(".lean") or c.endswith(".md"):
        path = c.rstrip("/")
        if not any(x in fileset or x in dirs for x in [path, path + ".lean"]):
            bad.append(("file", c))
        checked += 1
        continue
    if not re.fullmatch(r"[A-Za-z0-9_.']+", c):
        continue
    short = c.split(".")[-1]
    hits = decls.get(short, [])
    ok = any(full == c or full == "LucasU." + c for full, _ in hits)
    checked += 1
    if not ok:
        bad.append(("decl", c, [h[0] for h in hits][:4]))

print(f"commit {COMMIT}: checked {checked} tokens, {len(bad)} problems")
for b in bad:
    print("  ", b)
sys.exit(1 if bad else 0)
