/-
Generalised from lean_fibzeta FibZeta/Denom/Monomial.lean (ε = ±1, general t).
-/
import LucasU.Denom.Nodes

/-!
# Lemma 3.3: points without node collisions

If `w(ω)^n ≠ 1` for `1 ≤ n ≤ K` (i.e. `e(ω) > K`: no clustering), every pole part is regular
in the monomial basis, and the rank argument gives `π^{K − 1 − k₀} · coeff ∈ regularAt ω` whenever
`ν_l` is regular for `1 ≤ l < k₀` (`local_bound_monomial`).
-/

open Polynomial Finset

namespace LucasU.Denom

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {ε : ℤ}

local notation "Xr" => (RatFunc.X : RatFunc 𝕜)

omit [CharZero 𝕜] in
theorem polynomialChange_monomial (K : ℕ) :
    polynomialChange K (fun i : Fin K => (X : (RatFunc 𝕜)[X]) ^ i.val) = 1 := by
  ext i j
  simp only [polynomialChange, Matrix.of_apply, Polynomial.coeff_X_pow, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp
  · have h' : j.val ≠ i.val := fun e => h (Fin.ext e.symm)
    simp [h, h']

omit [CharZero 𝕜] in
theorem w_pow_sub_eq_one (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω : ω ≠ 0) {a b : ℕ} (hlt : b < a)
    (h : (wpar ε ω) ^ a = (wpar ε ω) ^ b) : (wpar ε ω) ^ (a - b) = 1 := by
  have hw0 : (wpar ε ω : 𝕜) ≠ 0 := wpar_ne_zero hε hω
  rw [show a = b + (a - b) by omega, pow_add] at h
  exact (mul_eq_left₀ (pow_ne_zero _ hw0)).mp h

omit [CharZero 𝕜] in
theorem collisionCount_eq_zero (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω : ω ≠ 0) (K a : ℕ) (ha : a ∈ Icc 1 K)
    (hW : ∀ n ∈ Icc 1 K, (wpar ε ω) ^ n ≠ 1) : collisionCount ε ω K a = 0 := by
  classical
  unfold collisionCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro b hb hab
  have hb' := mem_Icc.mp (mem_erase.mp hb).2
  have ha' := mem_Icc.mp ha
  rcases Nat.lt_or_gt_of_ne (mem_erase.mp hb).1 with hlt | hlt
  · exact hW (a - b) (mem_Icc.mpr ⟨by omega, by omega⟩) (w_pow_sub_eq_one hε ω hω hlt hab)
  · exact hW (b - a) (mem_Icc.mpr ⟨by omega, by omega⟩) (w_pow_sub_eq_one hε ω hω hlt hab.symm)

/-- **Lemma 3.3** (and the regular case `k₀ = K − 1`). -/
theorem local_bound_monomial (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω0 : ω ≠ 0) (K : ℕ)
    (hW : ∀ n ∈ Icc 1 K, (wpar ε ω) ^ n ≠ 1) (k₀ : ℕ)
    (hnu : ∀ l, 1 ≤ l → l < k₀ → nu ε Xr l ∈ regularAt ω) (i : ℕ) :
    uniformizer ω ^ (K - 1 - k₀) * (Delta ε Xr K).coeff i ∈ regularAt ω := by
  have h := local_bound_of_basis hε ω hω0 K (fun i : Fin K => (X : (RatFunc 𝕜)[X]) ^ i.val)
    (fun i => by rw [natDegree_X_pow]; exact i.isLt)
    (fun i j => by
      rw [coeff_X_pow]; split_ifs
      · exact (regularAt ω).one_mem
      · exact (regularAt ω).zero_mem)
    (by rw [polynomialChange_monomial, Matrix.det_one]; exact one_ne_zero)
    (by rw [polynomialChange_monomial, Matrix.det_one, inv_one]; exact (regularAt ω).one_mem)
    (fun _ => 0) (fun _ => 0)
    (fun i j => by
      simp only [add_zero, pow_zero, map_one, one_mul, properPart]
      apply (coeff_mem_iff_lifts (regularAt ω) _).mp
      intro l
      rw [finsetSum_coeff]
      apply (regularAt ω).sum_mem
      intro a ha
      have hN : ((X : (RatFunc 𝕜)[X]) ^ i.val * X ^ j.val).eval (node ε Xr a) /
          uniformizer ω ^ 0 ∈ regularAt ω := by
        rw [pow_zero, div_one]
        exact eval_mem_regularAt ω _ (fun l => by
          rw [← pow_add, coeff_X_pow]; split_ifs
          · exact (regularAt ω).one_mem
          · exact (regularAt ω).zero_mem) _ (node_mem_regularAt hε ω hω0 a)
      have hS : uniformizer ω ^ 0 * S ε Xr a ∈ regularAt ω := by
        rw [pow_zero, one_mul]
        exact S_mem_regularAt ω a (fun N hN => hW N (mem_Icc.mpr ⟨(mem_Icc.mp hN).1,
          (mem_Icc.mp hN).2.trans (mem_Icc.mp ha).2⟩))
      have := proper_term_coeff_mem hε ω hω0 K a ha _ 0 0 0 hN hS
        (by rw [collisionCount_eq_zero hε ω hω0 K a ha hW]) l
      simpa only [pow_zero, one_mul, mul_div_assoc] using this)
    k₀ hnu i
  simpa using h

end LucasU.Denom
