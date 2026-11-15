/-
Generalised from lean_fibzeta FibZeta/Analytic/All.lean (ε = ±1, general t).
-/
import LucasU.Analytic.Entry
import LucasU.Analytic.Decay

/-!
# The analytic ingredients: `LucasU.Analytic.entryIdentity`, `LucasU.Analytic.decayBound`

Both hold for every `ε = ±1` and every `0 < t ≤ φ⁻¹` (`Good ε t`); the constant of `decayBound`
is `4096`, independent of `(ε, t)`.
-/

namespace LucasU.Analytic

/-- **Entry identity** (PROOF_U Lemma 1 + partial fractions). -/
theorem entryIdentity {ε : ℤ} {t : ℝ} (h : Good ε t) : EntryIdentity ε t := by
  have : Fact (Good ε t) := ⟨h⟩
  intro K k _ _
  exact (hasL_fraction_DK K k).tsum_eq.symm

/-- **Proposition 2** (real decay): `|Δ_K(Ξ)| ≤ 4096^{K²} t^{2 b_K}`. -/
theorem decayBound {ε : ℤ} {t : ℝ} (h : Good ε t) : DecayBound ε t := by
  have : Fact (Good ε t) := ⟨h⟩
  exact decayBound_of_fact

end LucasU.Analytic
