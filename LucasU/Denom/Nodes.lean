/-
Generalised from lean_fibzeta FibZeta/Denom/Nodes.lean (ε = ±1, general t).
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/CyclotomicLocal.lean (Apache-2.0,
Lean formalisation by F. Solomon Admasu). Changes: the node collisions are those of `x_a = w^{-a}`,
`w = −τ²` (collision iff `w(ω)^a = w(ω)^b`), and the tails are `S_a = ∑ ψ_N`.
-/
import LucasU.Denom.Framework

/-!
# Local facts at a point `ω ≠ 0` (PROOF §3.1, facts (a), (b), (d))

* (a) `x_a − x_b` has at most a simple zero, and vanishes at `ω` iff `w(ω)^a = w(ω)^b`;
* (b) `π³ S_a` is regular, and `S_a` is regular if `w(ω)^N ≠ 1` for `N ≤ a`;
* the derivative `F'(x_a)` is cleared by `π^{#collisions}`;
* `proper_term_coeff_mem`: bookkeeping for a single residue term of the pole part.
-/

open Polynomial Finset

namespace LucasU.Denom

variable {𝕜 : Type*} [Field 𝕜] {ε : ℤ}

local notation "Xr" => (RatFunc.X : RatFunc 𝕜)

theorem node_sub_node_of_lt (hε : ε = 1 ∨ ε = -1) (τ : 𝕜) (hτ : τ ≠ 0) {a b : ℕ} (hab : a < b) :
    node ε τ a - node ε τ b = -(((wpar ε τ) ^ b)⁻¹ * (1 - (wpar ε τ) ^ (b - a))) := by
  have hw0 : (wpar ε τ : 𝕜) ≠ 0 := wpar_ne_zero hε hτ
  have : (wpar ε τ) ^ b = (wpar ε τ) ^ a * (wpar ε τ) ^ (b - a) := by
    rw [← pow_add]; congr 1; omega
  simp only [node]
  rw [this]
  field_simp
  ring

theorem Xr_ne_zero : Xr ≠ 0 := RatFunc.X_ne_zero

omit [Field 𝕜] in
theorem w_pow_ne_of_ne {𝕜 : Type*} [Field 𝕜] (ω : 𝕜) {a b : ℕ} (hab : a < b)
    (h : (wpar ε ω) ^ a ≠ (wpar ε ω) ^ b) : (wpar ε ω) ^ (b - a) ≠ 1 := by
  intro h1
  apply h
  rw [show b = a + (b - a) by omega, pow_add, h1, mul_one]

/-- Non-colliding node differences are units at `ω`. -/
theorem inv_node_diff_mem (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (a b : ℕ) (hab : a ≠ b)
    (h : (wpar ε ω) ^ a ≠ (wpar ε ω) ^ b) : (node ε Xr a - node ε Xr b)⁻¹ ∈ regularAt ω := by
  have hw : wpar ε Xr ∈ regularAt ω := wpar_mem _ (base_mem_regularAt ω)
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · rw [node_sub_node_of_lt hε _ Xr_ne_zero hlt, inv_neg, mul_inv, inv_inv]
    exact (regularAt ω).neg_mem ((regularAt ω).mul_mem ((regularAt ω).pow_mem hw b)
      (inv_one_sub_geom_mem ω _ (w_pow_ne_of_ne ω hlt h)))
  · rw [← neg_sub, node_sub_node_of_lt hε _ Xr_ne_zero hlt, neg_neg, mul_inv, inv_inv]
    exact (regularAt ω).mul_mem ((regularAt ω).pow_mem hw a)
      (inv_one_sub_geom_mem ω _ (w_pow_ne_of_ne ω hlt (Ne.symm h)))

/-- Colliding node differences are divisible by `π`. -/
theorem node_diff_div_uniformizer_mem (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω : ω ≠ 0) (a b : ℕ)
    (h : (wpar ε ω) ^ a = (wpar ε ω) ^ b) :
    (node ε Xr a - node ε Xr b) / uniformizer ω ∈ regularAt ω := by
  have hwinv := inv_w_mem_regularAt hε ω hω
  have hdiv (n : ℕ) (hn : (wpar ε ω) ^ n = 1) :
      (1 - (wpar ε Xr) ^ n) / uniformizer ω ∈ regularAt ω := by
    rw [one_sub_geom_X]
    exact polynomial_div_uniformizer_mem ω _ (by rw [eval_one_sub_geom, hn, sub_self])
  rcases lt_trichotomy a b with hlt | rfl | hlt
  · rw [node_sub_node_of_lt hε _ Xr_ne_zero hlt, neg_div, mul_div_assoc, ← inv_pow]
    refine (regularAt ω).neg_mem ((regularAt ω).mul_mem ((regularAt ω).pow_mem hwinv b)
      (hdiv _ ?_))
    have hw0 : (wpar ε ω : 𝕜) ≠ 0 := wpar_ne_zero hε hω
    have := h
    rw [show b = a + (b - a) by omega, pow_add] at this
    exact (mul_eq_left₀ (pow_ne_zero _ hw0)).mp this.symm
  · rw [sub_self, zero_div]; exact (regularAt ω).zero_mem
  · rw [← neg_sub, node_sub_node_of_lt hε _ Xr_ne_zero hlt, neg_neg, mul_div_assoc, ← inv_pow]
    refine (regularAt ω).mul_mem ((regularAt ω).pow_mem hwinv a) (hdiv _ ?_)
    have hw0 : (wpar ε ω : 𝕜) ≠ 0 := wpar_ne_zero hε hω
    have := h
    rw [show a = b + (a - b) by omega, pow_add] at this
    exact (mul_eq_left₀ (pow_ne_zero _ hw0)).mp this

theorem node_mem_regularAt (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω : ω ≠ 0) (a : ℕ) : node ε Xr a ∈ regularAt ω := by
  rw [node_eq]; exact (regularAt ω).pow_mem (inv_w_mem_regularAt hε ω hω) a

variable [CharZero 𝕜]

/-- Every node collision is at most a simple zero. -/
theorem uniformizer_div_node_diff_mem (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω : ω ≠ 0) (a b : ℕ) (hab : a ≠ b) :
    uniformizer ω / (node ε Xr a - node ε Xr b) ∈ regularAt ω := by
  have hw : wpar ε Xr ∈ regularAt ω := wpar_mem _ (base_mem_regularAt ω)
  rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
  · rw [node_sub_node_of_lt hε _ Xr_ne_zero hlt]
    have h := (regularAt ω).neg_mem ((regularAt ω).mul_mem ((regularAt ω).pow_mem hw b)
      (uniformizer_div_one_sub_geom_mem hε ω hω (b - a) (by omega)))
    convert h using 1
    field_simp
  · rw [← neg_sub, node_sub_node_of_lt hε _ Xr_ne_zero hlt]
    have h := (regularAt ω).mul_mem ((regularAt ω).pow_mem hw a)
      (uniformizer_div_one_sub_geom_mem hε ω hω (a - b) (by omega))
    convert h using 1
    field_simp

/-- `π³ S_a` is regular (fact (b)). -/
theorem uniformizer_cube_mul_S_mem (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω : ω ≠ 0) (a : ℕ) :
    uniformizer ω ^ 3 * S ε Xr a ∈ regularAt ω := by
  unfold S
  rw [Finset.mul_sum]
  apply (regularAt ω).sum_mem
  intro N hN
  have h := (regularAt ω).mul_mem ((regularAt ω).pow_mem (base_mem_regularAt ω) (3 * N))
    ((regularAt ω).pow_mem (uniformizer_div_one_sub_geom_mem hε ω hω N (mem_Icc.mp hN).1) 3)
  convert h using 1
  rw [psi, div_pow]
  ring

omit [CharZero 𝕜] in
/-- `S_a` is regular if none of its denominators vanishes. -/
theorem S_mem_regularAt (ω : 𝕜) (a : ℕ) (h : ∀ N ∈ Icc 1 a, (wpar ε ω) ^ N ≠ 1) :
    S ε Xr a ∈ regularAt ω := by
  unfold S
  apply (regularAt ω).sum_mem
  intro N hN
  rw [psi, div_eq_mul_inv, ← inv_pow]
  exact (regularAt ω).mul_mem ((regularAt ω).pow_mem (base_mem_regularAt ω) _)
    ((regularAt ω).pow_mem (inv_one_sub_geom_mem ω N (h N hN)) 3)

/-- Number of other labelled nodes colliding with node `a` at `ω`. -/
noncomputable def collisionCount (ε : ℤ) (ω : 𝕜) (K a : ℕ) : ℕ := by
  classical
  exact (((Icc 1 K).erase a).filter fun b => (wpar ε ω) ^ a = (wpar ε ω) ^ b).card

/-- Exactly the colliding-node factors are needed to clear `F'(x_a)`. -/
theorem uniformizer_pow_div_derivative_mem (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω : ω ≠ 0) (K a : ℕ)
    (ha : a ∈ Icc 1 K) :
    uniformizer ω ^ collisionCount ε ω K a / (derivative (F ε Xr K)).eval (node ε Xr a) ∈
      regularAt ω := by
  classical
  have hprod : (∏ b ∈ (Icc 1 K).erase a,
      (if (wpar ε ω) ^ a = (wpar ε ω) ^ b then uniformizer ω else 1) /
        (node ε Xr a - node ε Xr b)) ∈ regularAt ω := by
    apply (regularAt ω).prod_mem
    intro b hb
    by_cases hab : (wpar ε ω) ^ a = (wpar ε ω) ^ b
    · simp only [hab, ite_true]
      exact uniformizer_div_node_diff_mem hε ω hω a b (mem_erase.mp hb).1.symm
    · simp only [hab, ite_false, one_div]
      exact inv_node_diff_mem hε ω a b (mem_erase.mp hb).1.symm hab
  rw [Finset.prod_div_distrib] at hprod
  have hnum : (∏ b ∈ (Icc 1 K).erase a,
      if (wpar ε ω) ^ a = (wpar ε ω) ^ b then uniformizer ω else 1) =
      uniformizer ω ^ collisionCount ε ω K a := by
    rw [← Finset.prod_filter]
    simp [collisionCount]
  rw [hnum, ← derivative_F_eval_eq_prod Xr K a ha] at hprod
  exact hprod

omit [CharZero 𝕜] in
/-- Pole bookkeeping in the local ring. -/
theorem scaled_ratio_mem (ω : 𝕜) (N D q : RatFunc 𝕜) (v c s w : ℕ)
    (hN : N / uniformizer ω ^ v ∈ regularAt ω)
    (hD : uniformizer ω ^ c / D ∈ regularAt ω)
    (hq : uniformizer ω ^ s * q ∈ regularAt ω) (hc : c + s ≤ w + v) :
    uniformizer ω ^ w * (N / D) * q ∈ regularAt ω := by
  have h := (regularAt ω).mul_mem ((regularAt ω).mul_mem ((regularAt ω).mul_mem hN hD) hq)
    ((regularAt ω).pow_mem (uniformizer_mem ω) (w + v - (c + s)))
  have hu : uniformizer ω ≠ 0 := uniformizer_ne_zero ω
  convert h using 1
  have he : w + v = (w + v - (c + s)) + c + s := by omega
  have hpow : uniformizer ω ^ w * uniformizer ω ^ v =
      uniformizer ω ^ (w + v - (c + s)) * uniformizer ω ^ c * uniformizer ω ^ s := by
    rw [← pow_add, ← pow_add, ← pow_add, ← he]
  have hv : uniformizer ω ^ v ≠ 0 := pow_ne_zero _ hu
  have hw' : uniformizer ω ^ w = uniformizer ω ^ (w + v - (c + s)) * uniformizer ω ^ c *
      uniformizer ω ^ s / uniformizer ω ^ v := by
    rw [eq_div_iff hv, hpow]
  rw [hw']
  simp only [div_eq_mul_inv]
  ring

/-- A single residue term of the pole part, scaled by `π^w`, has regular coefficients once the
numerator zero order `v` compensates the collisions and the pole order `s` of `S_a`. -/
theorem proper_term_coeff_mem (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω : ω ≠ 0) (K a : ℕ) (ha : a ∈ Icc 1 K)
    (N : RatFunc 𝕜) (v s w : ℕ) (hN : N / uniformizer ω ^ v ∈ regularAt ω)
    (hS : uniformizer ω ^ s * S ε Xr a ∈ regularAt ω)
    (hw : collisionCount ε ω K a + s ≤ w + v) (i : ℕ) :
    (C (uniformizer ω ^ w * (N * (2 * Xr ^ a) / (derivative (F ε Xr K)).eval (node ε Xr a))) *
      (X - C (S ε Xr a))).coeff i ∈ regularAt ω := by
  have hD := uniformizer_pow_div_derivative_mem hε ω hω K a ha
  have hN2 : N * (2 * Xr ^ a) / uniformizer ω ^ v ∈ regularAt ω := by
    have := (regularAt ω).mul_mem hN ((regularAt ω).mul_mem
      (show (2 : RatFunc 𝕜) ∈ regularAt ω by simp)
      ((regularAt ω).pow_mem (base_mem_regularAt ω) a))
    convert this using 1
    ring
  have hone : uniformizer ω ^ 0 * (1 : RatFunc 𝕜) ∈ regularAt ω := by simp
  have hscalar := scaled_ratio_mem ω _ _ 1 v _ 0 w hN2 hD hone (by omega)
  have hconstant := scaled_ratio_mem ω _ _ (S ε Xr a) v _ s w hN2 hD hS hw
  rw [mul_one] at hscalar
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_sub]
  by_cases hi0 : i = 0
  · subst i
    have := (regularAt ω).neg_mem hconstant
    simp only [Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub, mul_neg]
    convert this using 1
  · by_cases hi1 : i = 1
    · subst i
      simpa using hscalar
    · simp [Polynomial.coeff_X, Polynomial.coeff_C, hi0, Ne.symm hi1]

end LucasU.Denom
