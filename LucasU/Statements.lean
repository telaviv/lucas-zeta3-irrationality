import LucasU.Defs

/-!
# The ingredients, as frozen statements (generalising `FibZeta.Statements`)

`Good ε t` is the standing hypothesis of the analytic ingredients: `ε = ±1` and `0 < t ≤ φ⁻¹`.
They are stated for every such `t`, not only for `t = 1/α`; only `LucasU.Main` uses that `t` is
the inverse of a quadratic unit.  Numbering: `handoff/fibzeta/pell/PROOF_U.md` (PROOF_U), which
follows `handoff/fibzeta/PROOF.md` (PROOF).

* `DecayBound` — PROOF Prop 2: `|Δ_K(Ξ)| ≤ C^{K²} t^{2 b_K}`.
* `ConjBound` — PROOF Prop 4: `|σΔ_K(−Ξ)| ≤ C^{K²} t^{K²(K+1)}`, where `σΔ_K` is the construction at
  `τ = ε/t` (the Galois conjugate of `t` when `t = 1/α`).
* `Integrality` — PROOF Lemma 3.1–Prop 3.4: `C_K(τ) Δ_{K,τ}` has coefficients in `ℤ[τ, τ⁻¹]`,
  uniformly in every real `τ ≠ 0` that is not a root of unity.
* `CostBound` — PROOF Lemma 3.5, Prop 3.6, with cubic constant `121/100 < 11/9`.
* `Nonvanishing` — PROOF Prop 5.
* `EntryIdentity` — PROOF Lemma 1 + partial fractions (used by the proof of `DecayBound` only).
-/

open Polynomial Finset

namespace LucasU

/-- Standing hypothesis: `ε = ±1` and `0 < t ≤ φ⁻¹`. -/
def Good (ε : ℤ) (t : ℝ) : Prop := (ε = 1 ∨ ε = -1) ∧ 0 < t ∧ t ≤ Real.goldenRatio⁻¹

/-- Proposition 2 (real decay). -/
def DecayBound (ε : ℤ) (t : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 1 ≤ K →
    |(Delta ε t K).eval (XiR ε t)| ≤ C ^ (K ^ 2) * t ^ (2 * bK K)

/-- Proposition 4 (conjugate smallness). -/
def ConjBound (ε : ℤ) (t : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 1 ≤ K →
    |(Delta ε ((ε : ℝ) / t) K).eval (-XiR ε t)| ≤ C ^ (K ^ 2) * t ^ (K ^ 2 * (K + 1))

/-- Proposition 3.4 (global denominator), at every real non-root of unity. -/
def Integrality (ε : ℤ) : Prop :=
  ∀ K i : ℕ, ∃ (n : ℕ) (A : ℤ[X]), ∀ τ : ℝ, τ ≠ 0 → (∀ m : ℕ, 0 < m → τ ^ m ≠ 1) →
    aeval τ (CKpoly ε K) * (Delta ε τ K).coeff i = aeval τ A / τ ^ n

/-- Proposition 3.6 (size of `N(C_K(t))`), with cubic constant `121/100`. -/
def CostBound (ε : ℤ) (t : ℝ) : Prop :=
  ∃ C : ℝ, ∀ K : ℕ, 1 ≤ K →
    Real.log |aeval t (CKpoly ε K) * aeval ((ε : ℝ) / t) (CKpoly ε K)| ≤
      (121 / 100 : ℝ) * (K : ℝ) ^ 3 * Real.log t⁻¹ + C * (K : ℝ) ^ 2 * (1 + Real.log K) ^ 2

/-- Proposition 5 (nonvanishing). -/
def Nonvanishing (ε : ℤ) (t : ℝ) : Prop :=
  ∀ N : ℕ, ∃ K, N ≤ K ∧ (Delta ε t K).eval (XiR ε t) ≠ 0

/-- Lemma 1 with partial fractions: `L_X(s^k/D_K)` at `τ = t`, `X = Ξ` is `L(s^k/D_K)`. -/
def EntryIdentity (ε : ℤ) (t : ℝ) : Prop :=
  ∀ K k : ℕ, 1 ≤ K → k ≤ 2 * K →
    nrm ε t K * (mConst ε t K k + XiR ε t * mLin ε t K k) = Lfun ε t (fun s => s ^ k / DK ε t K s)

end LucasU
