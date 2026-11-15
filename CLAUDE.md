# lean_lucasu notes

Lean 4 + Mathlib (v4.35.0) formalisation of **Σ 1/U_n³ ∉ ℚ** for the Lucas sequence U_{n+1} = aU_n + EU_{n−1} of every
real quadratic unit: E = 1 with a ≥ 1, or E = −1 with a ≥ 3. This includes Pell, and Σ 1/F_{kn}³ for every k.
* Source proof: `../handoff/fibzeta/pell/PROOF_U.md` (refereed, `REFEREE_U1.md`). It generalises
  `../handoff/fibzeta/PROOF.md`.
* Generalises `../lean_fibzeta` (`FibZeta`, the Fibonacci case, complete). A read-only copy is in `ref_fibzeta/`
  (git-ignored).

* Started 2026-11-15. Library `LucasU`, namespace `LucasU`. Git repo on branch `main`, not pushed; the owner pushes.
* `.lake/packages` is a Windows junction to `../lean_chi2/.lake/packages`. Don't delete it.
* Build: `LEAN_NUM_THREADS=4 lake build`.
* **Architecture.** Same as FibZeta, with a sign ε (w = ετ², ρ = ετ) and a general real t ∈ (0, φ⁻¹] in the analytic
  ingredients.
  - `Defs.lean`, `Statements.lean`: frozen.
  - `Unit.lean`: α, t, σt = ε/t, Binet, √D ∉ ℚ.
  - `Main.lean`: `irrational_zetaU_of`.
  - `Roots.lean`.
  - Worker folders `Analytic/ NonVan/ Conj/ Denom/ Cost/`; the rules are in `WORKERS.md`.
