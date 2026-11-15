# Irrationality of Σ 1/U_n³ for Lucas sequences of quadratic units (Lean 4 + Mathlib)

This repository formalises, in Lean 4 (v4.35.0) with Mathlib, the theorem:

> For integers a, E with E = 1, a ≥ 1, or E = −1, a ≥ 3, let U_0 = 0, U_1 = 1, U_{n+2} = a U_{n+1} + E U_n.
> Then Σ_{n ≥ 1} 1/U_n³ is irrational.

These are the Lucas sequences U_n(P, Q) = (ηⁿ − η̄ⁿ)/(η − η̄) of the units η > 1 of real quadratic orders, with
(a, E) = (P, −Q). Two corollaries are also formalised:
* the Pell numbers: Σ 1/P_n³ ∉ ℚ;
* for every k ≥ 1, Σ_{n ≥ 1} 1/F_{kn}³ ∉ ℚ.

```lean
theorem LucasU.irrational_zetaU {a : ℕ} {E : ℤ} (hA : Admissible a E) : Irrational (zetaU a E)
theorem LucasU.irrational_pell : Irrational (∑' n : ℕ, 1 / ((pell (n + 1) : ℤ) : ℝ) ^ 3)
theorem LucasU.irrational_fib_mul {k : ℕ} (hk : 1 ≤ k) :
    Irrational (∑' n : ℕ, 1 / (Nat.fib (k * (n + 1)) : ℝ) ^ 3)
```

Only the standard axioms are used (`lake env lean Axioms.lean`; output in `scripts/axioms.txt`). There is no `sorry`,
no `axiom` declaration, no `native_decide` and no `implemented_by`.

* **The statement.** To trust the theorem, read `Useq`, `zetaU` and `Admissible` in `LucasU/Defs.lean`.
  `LucasU.hasSum_zetaU` proves that the series converges. An independent comparison of the definitions and statements
  with the paper is in `FIDELITY_REFEREE.md`.
* **The paper.** `paper/main.tex`; build it with `sh build.sh` from `paper/`.
* **Build.** `lake exe cache get`, then `lake build`.
* **Provenance.** This library generalises the Fibonacci case (`FibZeta`, Σ 1/F_n³ ∉ ℚ), which in turn adapts parts of
  the Lean formalisation QZeta3 of uplift-universal-inc/qzeta_3-irrationality (Apache-2.0). Adapted files say so in
  their headers, and `NOTICE` records the reuse.
