/-
Generalised from lean_fibzeta FibZeta/Analytic/Entry.lean (ε = ±1, general t).
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/DividedDifferences.lean and
lean/QZeta3/GramIdentity.lean (Apache-2.0, Lean formalisation by F. Solomon Admasu). Changes: real
nodes `x_a = w^{−a}` with `w = εt²` instead of `p^a`, partial fractions via
`Lagrange.eval_interpolate_not_at_node`, normalisation `D_K = (−1)^K w^{A_K} F_K`.
-/
import LucasU.Analytic.Functional

/-!
# The entry identity (Lemma 1 + partial fractions, PROOF_U §1)

`hasL_fraction_DK`: at `τ = t`, `X = Ξ`, the formal entries `nrm · (mConst + Ξ · mLin)` are the
values `L(s^k/D_K)` of the real functional (as convergent series).
-/

open Polynomial Finset Filter Topology

namespace LucasU.Analytic

variable {ε : ℤ} {t : ℝ} [hG : Fact (Good ε t)]

theorem node_injOn (K : ℕ) : Set.InjOn (node ε t) (Icc 1 K : Set ℕ) := by
  intro a _ b _ h
  simp only [node] at h
  have h1 := inv_injective h
  have h2 : (t ^ 2) ^ a = (t ^ 2) ^ b := by
    have := congrArg abs h1
    rwa [abs_w_pow, abs_w_pow, pow_mul, pow_mul] at this
  exact pow_right_injective₀ (t_sq_pos ε t) (t_sq_lt_one ε t).ne h2

theorem one_lt_abs_node {a : ℕ} (ha : 1 ≤ a) : 1 < |node ε t a| := by
  rw [node, abs_inv, abs_w_pow]
  exact one_lt_inv₀ (pow_pos (t_pos ε t) _) |>.mpr (pow_lt_one₀ (t_pos ε t).le (t_lt_one ε t) (by omega))

theorem ne_node_of_abs_lt {x : ℝ} (hx : |x| < 1) (K : ℕ) : ∀ a ∈ Icc 1 K, x ≠ node ε t a := by
  intro a ha h
  have := one_lt_abs_node (ε := ε) (t := t) (mem_Icc.mp ha).1
  rw [← h] at this
  linarith

omit hG in
theorem F_eq_nodal (K : ℕ) : F ε t K = Lagrange.nodal (Icc 1 K) (node ε t) := rfl

/-- Partial fractions for `x^k / F_K(x)`. -/
theorem partial_fraction (K k : ℕ) (x : ℝ) (hx : ∀ a ∈ Icc 1 K, x ≠ node ε t a) :
    x ^ k / (F ε t K).eval x =
      (X ^ k /ₘ F ε t K).eval x + ∑ a ∈ Icc 1 K, res ε t K k a / (x - node ε t a) := by
  have hmon : (F ε t K).Monic := Lagrange.nodal_monic
  have hdeg : (X ^ k %ₘ F ε t K).degree < #(Icc 1 K) := by
    have := degree_modByMonic_lt (X ^ k) hmon
    rwa [F_eq_nodal, Lagrange.degree_nodal] at this
  have hint := Lagrange.eq_interpolate (node_injOn (ε := ε) (t := t) K) hdeg
  have hroot : ∀ a ∈ Icc 1 K, (X ^ k %ₘ F ε t K).eval (node ε t a) = node ε t a ^ k := by
    intro a ha
    have hFa : (F ε t K).eval (node ε t a) = 0 := Lagrange.eval_nodal_at_node ha
    have h := congrArg (eval (node ε t a)) (modByMonic_add_div (X ^ k) (F ε t K))
    simp only [eval_add, eval_mul, eval_pow, eval_X, hFa, zero_mul, add_zero] at h
    exact h
  have hF : (F ε t K).eval x ≠ 0 := Lagrange.eval_nodal_not_at_node hx
  have hr : (X ^ k %ₘ F ε t K).eval x =
      (F ε t K).eval x * ∑ a ∈ Icc 1 K, res ε t K k a / (x - node ε t a) := by
    conv_lhs => rw [hint]
    rw [Lagrange.eval_interpolate_not_at_node _ hx, ← F_eq_nodal]
    congr 1
    apply sum_congr rfl
    intro a ha
    rw [hroot a ha, Lagrange.nodalWeight_eq_eval_derivative_nodal ha, res, ← F_eq_nodal]
    ring
  have hmain := congrArg (eval x) (modByMonic_add_div (X ^ k) (F ε t K))
  simp only [eval_add, eval_mul, eval_pow, eval_X] at hmain
  rw [← hmain, hr]
  field_simp
  ring

theorem AK_succ (K : ℕ) : AK (K + 1) = AK K + (K + 1) := by
  unfold AK
  have : (K + 1) * (K + 1 + 1) = K * (K + 1) + (K + 1) * 2 := by ring
  rw [this, Nat.add_mul_div_right _ _ two_pos]

theorem DK_eq (K : ℕ) (x : ℝ) :
    DK ε t K x = ((-1) ^ K * wpar ε t ^ AK K) * (F ε t K).eval x := by
  induction K with
  | zero => simp [DK, F, AK]
  | succ K ih =>
    have hF : F ε t (K + 1) = F ε t K * (X - C (node ε t (K + 1))) := by
      rw [F, prod_Icc_succ_top (by omega)]; rfl
    have hD : DK ε t (K + 1) x = DK ε t K x * (1 - wpar ε t ^ (K + 1) * x) := by
      rw [DK, prod_Icc_succ_top (by omega)]; rfl
    have hw : wpar ε t ^ (K + 1) ≠ 0 := pow_ne_zero _ w_ne_zero
    rw [hD, ih, hF, AK_succ, eval_mul, eval_sub, eval_X, eval_C, node,
      pow_add (wpar ε t) (AK K) (K + 1), pow_succ (-1 : ℝ) K]
    generalize wpar ε t ^ (K + 1) = u at hw ⊢
    field_simp
    ring

theorem nrm_ne_zero (K : ℕ) : nrm ε t K ≠ 0 := by
  rw [nrm]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (inv_ne_zero (pow_ne_zero _ w_ne_zero))

theorem fraction_DK (K k : ℕ) (x : ℝ) :
    x ^ k / DK ε t K x = nrm ε t K * (x ^ k / (F ε t K).eval x) := by
  rw [DK_eq, nrm]
  have h1 : ((-1 : ℝ) ^ K) * (-1) ^ K = 1 := by rw [← mul_pow]; norm_num
  have hw : wpar ε t ^ AK K ≠ 0 := pow_ne_zero _ w_ne_zero
  have hs : ((-1 : ℝ) ^ K) ≠ 0 := pow_ne_zero _ (by norm_num)
  generalize wpar ε t ^ AK K = v at hw ⊢
  generalize ((-1 : ℝ) ^ K) = e at h1 hs ⊢
  rcases eq_or_ne ((F ε t K).eval x) 0 with h | h
  · simp [h]
  · field_simp
    linear_combination (-x ^ k) * h1

/-- The pole pieces `res/(y − x_a) = (−res w^a) (1 − w^a y)⁻¹`. -/
theorem pole_eq (c : ℝ) (a : ℕ) (y : ℝ) (hy : y ≠ node ε t a) :
    c / (y - node ε t a) = (-c * wpar ε t ^ a) * (1 - wpar ε t ^ a * y)⁻¹ := by
  have hw : wpar ε t ^ a ≠ 0 := pow_ne_zero _ w_ne_zero
  have h1 : y - node ε t a ≠ 0 := sub_ne_zero.mpr hy
  have h2 : 1 - wpar ε t ^ a * y ≠ 0 := by
    intro h; apply h1; rw [node]; field_simp; linear_combination -h
  rw [node] at h1 ⊢
  generalize wpar ε t ^ a = u at hw h1 h2 ⊢
  have h3 : y - u⁻¹ = -(u⁻¹) * (1 - u * y) := by field_simp; ring
  rw [h3, div_eq_mul_inv, mul_inv, inv_neg, inv_inv]
  ring

theorem w_pow_mul_inv (a : ℕ) : wpar ε t ^ a * (((ε : ℝ) * t) ^ a)⁻¹ = t ^ a := by
  have ht : ((ε : ℝ) * t) ^ a ≠ 0 := pow_ne_zero _ rho_ne_zero
  have : wpar ε t ^ a = ((ε : ℝ) * t) ^ a * t ^ a := by rw [← mul_pow, wpar]; ring
  rw [this]; field_simp

/-- The entries as convergent series. -/
theorem hasL_fraction_DK (K k : ℕ) :
    HasSum (Lterm ε t (fun y => y ^ k / DK ε t K y))
      (nrm ε t K * (mConst ε t K k + XiR ε t * mLin ε t K k)) := by
  set Q := X ^ k /ₘ F ε t K
  let P : ℕ → ℝ → ℝ := fun a y =>
    (-(res ε t K k a) * wpar ε t ^ a) * (1 - wpar ε t ^ a * y)⁻¹
  let g : ℝ → ℝ := fun y => nrm ε t K * (Q.eval y + ∑ a ∈ Icc 1 K, P a y)
  have hreg : Reg (fun y => Q.eval y + ∑ a ∈ Icc 1 K, P a y) :=
    reg_add (reg_poly Q) (reg_sum _ _ fun a _ =>
      reg_const_mul (reg_simplePole _ (abs_w_pow_le_one a)) _)
  have hP : HasSum (Lterm ε t (fun y => Q.eval y + ∑ a ∈ Icc 1 K, P a y))
      (Lpoly ε t Q + ∑ a ∈ Icc 1 K,
        (-(res ε t K k a) * wpar ε t ^ a) *
          (2 * (((ε : ℝ) * t) ^ a)⁻¹ * (XiR ε t - S ε t a))) :=
    hasL_add (reg_poly Q) (reg_sum _ _ fun a _ =>
      reg_const_mul (reg_simplePole _ (abs_w_pow_le_one a)) _) (hasL_poly Q)
      (hasL_sum _ _ _ (fun a _ => reg_const_mul (reg_simplePole _ (abs_w_pow_le_one a)) _)
        (fun a _ => hasL_const_mul (reg_simplePole _ (abs_w_pow_le_one a))
          (hasL_simplePole a) _))
  have hg := hasL_const_mul hreg hP (nrm ε t K)
  have he : ∀ n, (fun y => y ^ k / DK ε t K y) =ᶠ[𝓝 (pt ε t n)] g := by
    intro n
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds (abs_pt_lt_one n)]
      with y hy
    have hy' := ne_node_of_abs_lt (ε := ε) (t := t) hy K
    simp only [g, P]
    rw [fraction_DK, partial_fraction K k y hy']
    congr 2
    apply sum_congr rfl
    intro a ha
    exact pole_eq _ a y (hy' a ha)
  convert hasL_congr he hg using 2
  have hterm : ∀ a ∈ Icc 1 K,
      (-(res ε t K k a) * wpar ε t ^ a) * (2 * (((ε : ℝ) * t) ^ a)⁻¹ * (XiR ε t - S ε t a)) =
        2 * (res ε t K k a * t ^ a * S ε t a) +
          XiR ε t * (-(2 * (res ε t K k a * t ^ a))) := by
    intro a _
    have h := w_pow_mul_inv (ε := ε) (t := t) a
    linear_combination (-(2 * res ε t K k a * (XiR ε t - S ε t a))) * h
  rw [sum_congr rfl hterm, sum_add_distrib, ← mul_sum, ← mul_sum, mConst, mLin]
  simp only [sum_neg_distrib, ← mul_sum]
  ring

end LucasU.Analytic
