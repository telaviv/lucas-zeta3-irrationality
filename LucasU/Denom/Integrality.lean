/-
Generalised from lean_fibzeta FibZeta/Denom/Integrality.lean (ε = ±1, general t).
-/
import LucasU.Denom.NewtonLocal
import LucasU.Denom.Monomial
import LucasU.Denom.Descent
import LucasU.Roots

/-!
# Proposition 3.4: `C_K(τ) Δ_{K,τ}` has coefficients in `ℤ[τ, τ⁻¹]`

At a primitive `d`-th root `ω` (`d ≤ 4K`) the local exponent is `b_{K,d} = nExp ε K d`:

* `k₀ = k_min(d)` if some `1 ≤ k ≤ K − 2` has `α_k(ω) = 1`, else `k₀ = K − 1`; then
  `K − 1 − k₀ = nAlpha ε K d` and `ν_l` is regular for `1 ≤ l < k₀`;
* if `e(d) ≤ K`: Proposition 3.2 (`local_bound_cluster`), with `∑_r cost_r = nW ε K d`;
* otherwise: Lemma 3.3 (`local_bound_monomial`), `nW ε K d = 0`.

The descent (`integrality_of_local_bounds`) then gives `LucasU.Denom.integrality`, for both signs.
-/

open Polynomial Finset

namespace LucasU.Denom

theorem sum_cost_eq_nW {K e : ℕ} (he : 1 ≤ e) (heK : e ≤ K) :
    (∑ r ∈ range e, if r = 0 then cW' (clMult K e r) else cW (clMult K e r)) =
      (∑ r ∈ Icc 1 (e - 1), cW (clusterSize K e r)) + cW' (clusterSize K e e) := by
  have hrange : range e = insert 0 (Icc 1 (e - 1)) := by
    ext r; simp only [mem_range, mem_insert, mem_Icc]; omega
  rw [hrange, sum_insert (by simp), if_pos rfl, clusterSize_self he heK, add_comm]
  congr 1
  apply sum_congr rfl
  intro r hr
  have hr' := mem_Icc.mp hr
  rw [if_neg (by omega), clusterSize_eq he heK (by omega)]

/-- **The local bounds** of Proposition 3.2 / Lemma 3.3 at every primitive `d`-th root. -/
theorem localBounds {ε : ℤ} (hε : ε = 1 ∨ ε = -1) : LocalBounds ε ℂ := by
  classical
  intro K i d hd ω hω
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have hω0 : ω ≠ 0 := hω.ne_zero hd0.ne'
  have horder : orderOf (wpar ε ω) = eW ε d := orderOf_w_of_primitive hε hd0 hω
  -- the choice of `k₀`
  let k₀ : ℕ := if h : ∃ k, 1 ≤ k ∧ k ≤ K - 2 ∧ IsAlphaRoot ε d k then Nat.find h else K - 1
  have hk₀ : nAlpha ε K d = K - 1 - k₀ := by
    unfold nAlpha
    by_cases h : ∃ k, 1 ≤ k ∧ k ≤ K - 2 ∧ IsAlphaRoot ε d k
    · rw [dif_pos h]; simp only [k₀, dif_pos h]
    · rw [dif_neg h]; simp only [k₀, dif_neg h]; omega
  have hnu : ∀ l, 1 ≤ l → l < k₀ → nu ε (RatFunc.X : RatFunc ℂ) l ∈ regularAt ω := by
    intro l hl1 hlk
    apply nu_mem_of_alpha_ne
    intro h1
    have hα : IsAlphaRoot ε d l := (alpha_eq_one_iff_of_primitive hε hd0 hω l).mp h1
    by_cases h : ∃ k, 1 ≤ k ∧ k ≤ K - 2 ∧ IsAlphaRoot ε d k
    · simp only [k₀, dif_pos h] at hlk
      have hle := Nat.find_spec h
      exact Nat.find_min h hlk ⟨hl1, by omega, hα⟩
    · simp only [k₀, dif_neg h] at hlk
      exact h ⟨l, hl1, by omega, hα⟩
  unfold nExp
  rw [hk₀]
  by_cases hW : 1 ≤ eW ε d ∧ eW ε d ≤ K
  · have h := local_bound_cluster hε ω hω0 hW.1 hW.2 horder k₀ hnu i
    unfold nW
    rw [if_pos hW, ← sum_cost_eq_nW hW.1 hW.2]
    exact h
  · have hW' : ∀ n ∈ Icc 1 K, (wpar ε ω) ^ n ≠ 1 := by
      intro n hn h1
      have hdvd := orderOf_dvd_of_pow_eq_one h1
      have hn' := mem_Icc.mp hn
      have hpos : 0 < orderOf (wpar ε ω) := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hle := Nat.le_of_dvd (by omega) hdvd
      rw [horder] at hpos hle
      exact hW ⟨hpos, by omega⟩
    unfold nW
    rw [if_neg hW, zero_add]
    exact local_bound_monomial hε ω hω0 K hW' k₀ hnu i

/-- **Proposition 3.4** (frozen statement `Integrality`). -/
theorem integrality {ε : ℤ} (hε : ε = 1 ∨ ε = -1) : Integrality ε :=
  integrality_of_local_bounds hε (localBounds hε)

end LucasU.Denom
