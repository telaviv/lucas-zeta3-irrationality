# What you have to trust

## Axioms

`lake env lean Axioms.lean` prints, for the main theorem and the corollaries,

```
'LucasU.irrational_zetaU' depends on axioms: [propext, Classical.choice, Quot.sound]
'LucasU.irrational_pell' depends on axioms: [propext, Classical.choice, Quot.sound]
'LucasU.irrational_fib_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'LucasU.hasSum_zetaU' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(full output: `scripts/axioms.txt`). These are Lean's three standard axioms, the ones Mathlib uses. The project has no
`sorry`, no `axiom` declaration, no `native_decide` and no `implemented_by`, so nothing relies on the compiler.

## The statement

The kernel checks the proof; it cannot check that the statement means what we claim. For
`LucasU.irrational_zetaU (hA : Admissible a E) : Irrational (zetaU a E)`, read three definitions in
`LucasU/Defs.lean`:

```lean
def Admissible (a : ℕ) (E : ℤ) : Prop := (E = 1 ∧ 1 ≤ a) ∨ (E = -1 ∧ 3 ≤ a)

def Useq (a : ℕ) (E : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => a * Useq a E (n + 1) + E * Useq a E n

noncomputable def zetaU (a : ℕ) (E : ℤ) : ℝ := ∑' n : ℕ, 1 / ((Useq a E (n + 1) : ℤ) : ℝ) ^ 3
```

So `zetaU a E = ∑_{n ≥ 1} 1/U_n³`. In Lucas notation U_n(P, Q) this is (a, E) = (P, −Q). A divergent `tsum` has the
junk value `0`, which is rational, so the theorem cannot be true for a degenerate reason. `LucasU.hasSum_zetaU` also
proves that the series converges to `zetaU a E`.

For the corollaries, also read `pell` (`= Useq 2 1`) and `lucasNum` in `LucasU/Corollaries.lean`, and the statements of
`irrational_pell` and `irrational_fib_mul` in `LucasU/Final.lean`.

Nothing else needs to be read to trust the theorems. To check that the formal proof follows the paper, read
`LucasU/Defs.lean` and `LucasU/Statements.lean`. An independent comparison of these with the paper is in
`FIDELITY_REFEREE.md` (verdict PASS WITH FIXES; all fixes were applied).
