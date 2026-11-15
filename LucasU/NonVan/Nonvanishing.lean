import LucasU.Statements
import LucasU.NonVan.Algebra
import LucasU.NonVan.Interp

-- Generalised from lean_fibzeta FibZeta/NonVan/Nonvanishing.lean (ε = ±1, general t).
-- Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/Nonvanishing.lean and
-- lean/QZeta3/Frozen/Prop51.lean (Apache-2.0, Lean formalisation by F. Solomon Admasu). Changes: assembled
-- for the formal Hankel matrix of `Defs.lean` at `τ = t`, `X = Ξ`, with nodes `x_a = w^{−a}`.

/-!
# Proposition 5: `Δ_K(Ξ) ≠ 0` for infinitely many `K` (PROOF §5, PROOF_U §5)

`nonvanishing (h : Good ε t) : Nonvanishing ε t` is proved outright: the argument only uses the
formal functional `L_Ξ` of `Defs.lean` (polynomial moments `ν_k` plus pole moments
`2t^a(Ξ − S_a)`), so the `EntryIdentity` is not needed.  Only `0 < t < 1` and `ε² = 1` are used.
-/

open Polynomial Finset Filter Topology

namespace LucasU.NonVan

variable {ε : ℤ} {t : ℝ}

/-- The interpolation nodes `x_{a+1} = w^{−(a+1)}`. -/
noncomputable def nodeSeq (ε : ℤ) (t : ℝ) (a : ℕ) : ℝ := node ε t (a + 1)

theorem nodeSeq_injective (hG : Good ε t) : Function.Injective (nodeSeq ε t) := by
  intro a b hab
  have := node_injective hG hab
  omega

theorem nodeSeq_inv_tendsto (hG : Good ε t) :
    Tendsto (fun a => (nodeSeq ε t a)⁻¹) atTop (𝓝[≠] 0) := by
  have heq : (fun a => (nodeSeq ε t a)⁻¹) = fun a => (wpar ε t) ^ (a + 1) := by
    funext a; simp [nodeSeq, node]
  rw [heq]
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall (fun a => w_pow_ne_zero hG (a + 1))⟩
  have hw : ‖wpar ε t‖ < 1 := by
    rw [Real.norm_eq_abs, abs_w hG]; exact tsq_lt_one hG
  exact (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hw).comp (tendsto_add_atTop_nat 1)

/-- Every orthogonal numerator has the required Cauchy interpolant. -/
theorem cauchy_orthogonal_interpolant (hG : Good ε t) (n : ℕ) (Q : ℝ[X])
    (horth : ∀ j : Fin n, Ln ε t n (X ^ j.val * Q) = 0) :
    ∃ P : ℝ[X],
      Tendsto (fun x => cauchyF ε t x * Q.eval x - P.eval x) atTop (𝓝 0) ∧
      ∀ a, a < n → cauchyF ε t (nodeSeq ε t a) * Q.eval (nodeSeq ε t a) -
        P.eval (nodeSeq ε t a) = 0 := by
  refine ⟨cauchyPart ε t Q, tendsto_cauchyPart_error hG Q, ?_⟩
  intro a ha
  apply cauchyPart_interpolates hG Q horth
  simp only [Finset.mem_Icc]
  omega

/-- **Proposition 5.** `Δ_K(Ξ) ≠ 0` for infinitely many `K`. -/
theorem nonvanishing {ε : ℤ} {t : ℝ} (h : Good ε t) : Nonvanishing ε t := by
  intro N
  obtain ⟨n, hn, hdet⟩ := frequently_nonsingular_of_meromorphic_nonrational (cauchyF ε t)
    (nodeSeq ε t) (nodeSeq_injective h) (nodeSeq_inv_tendsto h) (Ln ε t)
    (meromorphicAt_cauchyF_inv h) (cauchyF_nonrational h)
    (fun n _ Q _ _ horth => cauchy_orthogonal_interpolant h n Q horth) N
  refine ⟨n, hn, ?_⟩
  rw [Delta_eval]
  exact mul_ne_zero (pow_ne_zero _ (nrm_ne_zero h n)) hdet

end LucasU.NonVan
