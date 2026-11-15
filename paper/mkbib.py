"""Build refs.bib from the Fibonacci paper's bibliography (entries cited here) plus the new entries."""
import re
src = open("../../lean_fibzeta/paper/refs.bib", encoding="utf-8").read()
entries = re.split(r"\n(?=@)", src)
keep = {"AJ89", "DNNS97", "ESS07", "ESS08", "Nes96", "Wal10", "UPL", "QZ3", "Uva69", "Kra21", "Pre96", "Zud16", "Zud17"}
out = ['% Bibliography for "The reciprocal cube sums of Lucas sequences of quadratic units are irrational".\n'
       '% Style: amsplain.\n']
for e in entries:
    m = re.match(r"@\w+\{(\w+),", e)
    if m and m.group(1) in keep:
        out.append(e.strip() + "\n")
out.append(r"""@misc{Kri26,
  author  = {Krisman, S.},
  title   = {The sum of the reciprocal cubes of the {F}ibonacci numbers is irrational},
  note    = {preprint, 2026; Lean formalisation at \url{https://github.com/telaviv/fibonacci-zeta3-irrationality}},
}
""")
out.append(r"""@article{XW13,
  author  = {Xu, Z. and Wang, T.},
  title   = {The infinite sum of the cubes of reciprocal {P}ell numbers},
  journal = {Adv. Difference Equ.},
  year    = {2013},
  note    = {article 184},
}
""")
open("refs.bib", "w", encoding="utf-8").write("\n".join(out))
print(len(out) - 1, "entries")
