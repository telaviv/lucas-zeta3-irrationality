/-
Generalised from lean_fibzeta FibZeta/Analytic/Weight.lean (ε = ±1, general t).
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/AnalyticWeight.lean and
lean/QZeta3/Functional.lean (Apache-2.0, Lean formalisation by F. Solomon Admasu). Changes: the
weight bounds hold for real `q`, `x` of either sign (`|q| ≤ 1/2`, `|x| ≤ |q|`, stated with absolute
values); `thetaOp_eq_theta` relates `θ(θ+1)` to the Euler operator `θ`.
-/
import LucasU.Analytic.Functional

/-!
# The Euler operator `θ` and the weight `W_K = 1/D_K` (PROOF §2)

* `theta f x = x f'(x)`, Leibniz rules `theta_mul`, `theta_sq_mul`;
* `thetaOp_eq_theta : θ(θ+1) f = θ²f + θf`;
* `rationalWeight_euler_bounds`: `|W| ≤ 2`, `|θW| ≤ (8/3)|x|`, `|θ²W| ≤ (16/3)|x|` on
  `|x| ≤ |q| ≤ 1/2`.
-/

open Finset Filter Topology

namespace LucasU.Analytic

/-- The Euler derivative `θ = x d/dx`. -/
noncomputable def theta (f : ℝ → ℝ) : ℝ → ℝ := fun x => x * deriv f x

theorem theta_congr_nhds {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] g) :
    theta f =ᶠ[𝓝 x] theta g :=
  h.deriv.mono fun y hy => by simp only [theta, hy]

theorem theta_add {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    theta (f + g) x = theta f x + theta g x := by
  simp only [theta, deriv_add hf hg, mul_add]

theorem differentiableAt_theta {f : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (theta f) x :=
  differentiableAt_id.fun_mul (differentiableAt_deriv hf)

theorem theta_mul {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    theta (f * g) x = theta f x * g x + f x * theta g x := by
  simp only [theta, deriv_mul hf hg]
  ring

theorem theta_sq_mul {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    theta (theta (f * g)) x = theta (theta f) x * g x +
      2 * theta f x * theta g x + f x * theta (theta g) x := by
  have he : theta (f * g) =ᶠ[𝓝 x] theta f * g + f * theta g := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hyf hyg
    exact theta_mul (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  rw [(theta_congr_nhds he).eq_of_nhds]
  have hdf := hf.differentiableAt (by norm_num)
  have hdg := hg.differentiableAt (by norm_num)
  rw [theta_add ((differentiableAt_theta hf).mul hdg) (hdf.mul (differentiableAt_theta hg)),
    theta_mul (differentiableAt_theta hf) hdg, theta_mul hdf (differentiableAt_theta hg)]
  ring

/-- `θ(θ+1) = θ² + θ`. -/
theorem thetaOp_eq_theta {f : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) :
    thetaOp f x = theta (theta f) x + theta f x := by
  have hd : HasDerivAt (fun y => y * deriv f y) (1 * deriv f x + x * deriv (deriv f) x) x :=
    (hasDerivAt_id' x).mul (differentiableAt_deriv hf).hasDerivAt
  have h2 : theta (theta f) x = x * (1 * deriv f x + x * deriv (deriv f) x) := by
    change x * deriv (fun y => y * deriv f y) x = _
    rw [hd.deriv]
  rw [h2, thetaOp, theta]
  ring

/-! ### The weight -/

noncomputable def rationalWeight (q : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ∏ a ∈ Icc 1 K, (1 - q ^ a * x)⁻¹

noncomputable def weightAlpha (q : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ Icc 1 K, q ^ a * x / (1 - q ^ a * x)

noncomputable def weightBeta (q : ℝ) (K : ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ Icc 1 K, q ^ a * x / (1 - q ^ a * x) ^ 2

theorem one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (v : ι → ℝ)
    (hv0 : ∀ i ∈ s, 0 ≤ v i) (hv1 : ∀ i ∈ s, v i ≤ 1) :
    1 - ∑ i ∈ s, v i ≤ ∏ i ∈ s, (1 - v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hvi0 := hv0 i (mem_insert_self i s)
    have hvi1 := hv1 i (mem_insert_self i s)
    have hvs0 : ∀ j ∈ s, 0 ≤ v j := fun j hj => hv0 j (mem_insert_of_mem hj)
    have hvs1 : ∀ j ∈ s, v j ≤ 1 := fun j hj => hv1 j (mem_insert_of_mem hj)
    have h := mul_le_mul_of_nonneg_left (ih hvs0 hvs1) (sub_nonneg.mpr hvi1)
    have hs : 0 ≤ ∑ j ∈ s, v j := sum_nonneg hvs0
    rw [sum_insert hi, prod_insert hi]
    nlinarith [mul_nonneg hs hvi0]

theorem sum_half_pow_eq (K : ℕ) : ∑ a ∈ Icc 1 K, (1 / 2 : ℝ) ^ a = 1 - (1 / 2) ^ K := by
  induction K with
  | zero => simp
  | succ K ih => rw [sum_Icc_succ_top (by omega), ih, pow_succ]; ring

theorem sum_geometric_nodes_le_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2) (K : ℕ) :
    ∑ a ∈ Icc 1 K, q ^ a ≤ 1 := by
  calc _ ≤ ∑ a ∈ Icc 1 K, (1 / 2 : ℝ) ^ a := sum_le_sum fun a _ => pow_le_pow_left₀ hq0 hq1 a
    _ = 1 - (1 / 2) ^ K := sum_half_pow_eq K
    _ ≤ 1 := by linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) K]

theorem weight_factor_bounds {q x : ℝ} (hq1 : |q| ≤ 1 / 2) (hxq : |x| ≤ |q|) {a : ℕ}
    (ha : 1 ≤ a) : |q ^ a * x| = |q| ^ a * |x| ∧ |q ^ a * x| ≤ 1 / 4 := by
  have hq0 := abs_nonneg q
  have hqa : |q| ^ a ≤ |q| := by
    simpa using pow_le_pow_of_le_one hq0 (by linarith : |q| ≤ 1) ha
  have he : |q ^ a * x| = |q| ^ a * |x| := by rw [abs_mul, abs_pow]
  refine ⟨he, ?_⟩
  rw [he]
  have := mul_le_mul hqa hxq (abs_nonneg x) hq0
  nlinarith

theorem one_sub_factor_pos {q x : ℝ} (hq1 : |q| ≤ 1 / 2) (hxq : |x| ≤ |q|) {a : ℕ}
    (ha : 1 ≤ a) : 3 / 4 ≤ |1 - q ^ a * x| := by
  have h := (weight_factor_bounds hq1 hxq ha).2
  have := abs_sub_abs_le_abs_sub 1 (q ^ a * x)
  rw [abs_one] at this
  linarith

theorem factor_ne_zero {q x : ℝ} (hq1 : |q| ≤ 1 / 2) (hxq : |x| ≤ |q|) (K : ℕ) :
    ∀ a ∈ Icc 1 K, 1 - q ^ a * x ≠ 0 := by
  intro a ha h
  have := one_sub_factor_pos hq1 hxq (mem_Icc.mp ha).1
  rw [h, abs_zero] at this
  norm_num at this

theorem sum_abs_factor_le {q x : ℝ} (hq1 : |q| ≤ 1 / 2) (hxq : |x| ≤ |q|) (K : ℕ) :
    ∑ a ∈ Icc 1 K, |q ^ a * x| ≤ |x| := by
  calc ∑ a ∈ Icc 1 K, |q ^ a * x| = (∑ a ∈ Icc 1 K, |q| ^ a) * |x| := by
        rw [sum_mul]
        exact sum_congr rfl fun a ha => (weight_factor_bounds hq1 hxq (mem_Icc.mp ha).1).1
    _ ≤ 1 * |x| := mul_le_mul_of_nonneg_right
        (sum_geometric_nodes_le_one (abs_nonneg q) hq1 K) (abs_nonneg x)
    _ = |x| := one_mul _

theorem rationalWeight_bound {q x : ℝ} (hq1 : |q| ≤ 1 / 2) (hxq : |x| ≤ |q|) (K : ℕ) :
    |rationalWeight q K x| ≤ 2 := by
  have hx : |x| ≤ 1 / 2 := hxq.trans hq1
  have hprod : 1 / 2 ≤ ∏ a ∈ Icc 1 K, |1 - q ^ a * x| := by
    have h1 := one_sub_sum_le_prod (Icc 1 K) (fun a => |q ^ a * x|)
      (fun a _ => abs_nonneg _)
      (fun a ha => le_trans (weight_factor_bounds hq1 hxq (mem_Icc.mp ha).1).2 (by norm_num))
    have h2 : ∏ a ∈ Icc 1 K, (1 - |q ^ a * x|) ≤ ∏ a ∈ Icc 1 K, |1 - q ^ a * x| := by
      apply Finset.prod_le_prod₀
      · intro a ha
        have := (weight_factor_bounds hq1 hxq (mem_Icc.mp ha).1).2
        linarith
      · intro a _
        have := abs_sub_abs_le_abs_sub 1 (q ^ a * x)
        rwa [abs_one] at this
    have h3 := sum_abs_factor_le hq1 hxq K
    linarith
  have hpos : 0 < ∏ a ∈ Icc 1 K, |1 - q ^ a * x| := by linarith
  unfold rationalWeight
  rw [Finset.prod_inv_distrib, abs_inv, Finset.abs_prod, inv_le_iff_one_le_mul₀ hpos]
  linarith

theorem contDiffAt_rationalWeight {q x : ℝ} (K : ℕ)
    (hx : ∀ a ∈ Icc 1 K, 1 - q ^ a * x ≠ 0) : ContDiffAt ℝ 2 (rationalWeight q K) x := by
  apply contDiffAt_prod
  intro a ha
  exact (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)).inv (hx a ha)

theorem contDiffAt_weightAlpha {q x : ℝ} (K : ℕ)
    (hx : ∀ a ∈ Icc 1 K, 1 - q ^ a * x ≠ 0) : ContDiffAt ℝ 2 (weightAlpha q K) x := by
  apply ContDiffAt.sum
  intro a ha
  exact (contDiffAt_const.mul contDiffAt_id).div
    (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)) (hx a ha)

theorem hasDerivAt_weight_factor {q x : ℝ} (a : ℕ) (hx : 1 - q ^ a * x ≠ 0) :
    HasDerivAt (fun y : ℝ => (1 - q ^ a * y)⁻¹) (q ^ a / (1 - q ^ a * x) ^ 2) x := by
  convert (((hasDerivAt_id' x).const_mul (q ^ a)).const_sub (1 : ℝ)).fun_inv hx using 1
  ring

theorem theta_rationalWeight {q x : ℝ} (K : ℕ) (hx : ∀ a ∈ Icc 1 K, 1 - q ^ a * x ≠ 0) :
    theta (rationalWeight q K) x = rationalWeight q K x * weightAlpha q K x := by
  have hd := HasDerivAt.fun_finsetProd (fun a ha => hasDerivAt_weight_factor a (hx a ha))
  change x * deriv (fun y => ∏ a ∈ Icc 1 K, (1 - q ^ a * y)⁻¹) x = _
  rw [hd.deriv]
  simp only [smul_eq_mul, Finset.mul_sum, weightAlpha]
  apply Finset.sum_congr rfl
  intro a ha
  have hw : rationalWeight q K x =
      (1 - q ^ a * x)⁻¹ * ∏ b ∈ (Icc 1 K).erase a, (1 - q ^ b * x)⁻¹ :=
    (Finset.mul_prod_erase _ _ ha).symm
  rw [hw]
  have := hx a ha
  field_simp

theorem theta_weightAlpha {q x : ℝ} (K : ℕ) (hx : ∀ a ∈ Icc 1 K, 1 - q ^ a * x ≠ 0) :
    theta (weightAlpha q K) x = weightBeta q K x := by
  have hd (a : ℕ) (ha : a ∈ Icc 1 K) :
      HasDerivAt (fun y : ℝ => q ^ a * y / (1 - q ^ a * y)) (q ^ a / (1 - q ^ a * x) ^ 2) x := by
    convert ((hasDerivAt_id' x).const_mul (q ^ a)).fun_div
      (((hasDerivAt_id' x).const_mul (q ^ a)).const_sub (1 : ℝ)) (hx a ha) using 1
    ring
  change x * deriv (fun y => ∑ a ∈ Icc 1 K, q ^ a * y / (1 - q ^ a * y)) x = _
  rw [(HasDerivAt.fun_sum hd).deriv]
  simp only [weightBeta, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem theta_sq_rationalWeight {q x : ℝ} (K : ℕ) (hx : ∀ a ∈ Icc 1 K, 1 - q ^ a * x ≠ 0) :
    theta (theta (rationalWeight q K)) x =
      rationalWeight q K x * (weightAlpha q K x ^ 2 + weightBeta q K x) := by
  have hgood : ∀ᶠ y in 𝓝 x, ∀ a ∈ Icc 1 K, 1 - q ^ a * y ≠ 0 := by
    rw [Finset.eventually_all]
    intro a ha
    exact (continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).eventually_ne (hx a ha)
  have he : theta (rationalWeight q K) =ᶠ[𝓝 x] rationalWeight q K * weightAlpha q K :=
    hgood.mono (fun y hy => theta_rationalWeight K hy)
  rw [(theta_congr_nhds he).eq_of_nhds,
    theta_mul ((contDiffAt_rationalWeight K hx).differentiableAt (by norm_num))
      ((contDiffAt_weightAlpha K hx).differentiableAt (by norm_num)),
    theta_rationalWeight K hx, theta_weightAlpha K hx]
  ring

theorem weightAlpha_bound {q x : ℝ} (hq1 : |q| ≤ 1 / 2) (hxq : |x| ≤ |q|) (K : ℕ) :
    |weightAlpha q K x| ≤ (4 / 3) * |x| := by
  have hterm (a : ℕ) (ha : a ∈ Icc 1 K) :
      |q ^ a * x / (1 - q ^ a * x)| ≤ (4 / 3) * |q ^ a * x| := by
    have h1 := one_sub_factor_pos hq1 hxq (mem_Icc.mp ha).1
    rw [abs_div]
    calc |q ^ a * x| / |1 - q ^ a * x| ≤ |q ^ a * x| / (3 / 4) :=
          div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) h1
      _ = _ := by ring
  calc |weightAlpha q K x| ≤ ∑ a ∈ Icc 1 K, |q ^ a * x / (1 - q ^ a * x)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Icc 1 K, (4 / 3) * |q ^ a * x| := sum_le_sum hterm
    _ = (4 / 3) * ∑ a ∈ Icc 1 K, |q ^ a * x| := by rw [mul_sum]
    _ ≤ (4 / 3) * |x| := by
        have := sum_abs_factor_le hq1 hxq K
        linarith

theorem weightBeta_bound {q x : ℝ} (hq1 : |q| ≤ 1 / 2) (hxq : |x| ≤ |q|) (K : ℕ) :
    |weightBeta q K x| ≤ (16 / 9) * |x| := by
  have hterm (a : ℕ) (ha : a ∈ Icc 1 K) :
      |q ^ a * x / (1 - q ^ a * x) ^ 2| ≤ (16 / 9) * |q ^ a * x| := by
    have h1 := one_sub_factor_pos hq1 hxq (mem_Icc.mp ha).1
    have h2 : 9 / 16 ≤ |1 - q ^ a * x| ^ 2 := by nlinarith
    rw [abs_div, abs_pow]
    calc |q ^ a * x| / |1 - q ^ a * x| ^ 2 ≤ |q ^ a * x| / (9 / 16) :=
          div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) h2
      _ = _ := by ring
  calc |weightBeta q K x| ≤ ∑ a ∈ Icc 1 K, |q ^ a * x / (1 - q ^ a * x) ^ 2| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Icc 1 K, (16 / 9) * |q ^ a * x| := sum_le_sum hterm
    _ = (16 / 9) * ∑ a ∈ Icc 1 K, |q ^ a * x| := by rw [mul_sum]
    _ ≤ (16 / 9) * |x| := by
        have := sum_abs_factor_le hq1 hxq K
        linarith

/-- Uniform bounds for the weight and both Euler derivatives on `|x| ≤ |q| ≤ 1/2`. -/
theorem rationalWeight_euler_bounds {q x : ℝ} (hq1 : |q| ≤ 1 / 2) (hxq : |x| ≤ |q|) (K : ℕ) :
    |rationalWeight q K x| ≤ 2 ∧
      |theta (rationalWeight q K) x| ≤ (8 / 3) * |x| ∧
      |theta (theta (rationalWeight q K)) x| ≤ (16 / 3) * |x| := by
  have hw := rationalWeight_bound hq1 hxq K
  have ha := weightAlpha_bound hq1 hxq K
  have hb := weightBeta_bound hq1 hxq K
  have hx := factor_ne_zero hq1 hxq K
  have hxh : |x| ≤ 1 / 2 := hxq.trans hq1
  rw [theta_rationalWeight K hx, theta_sq_rationalWeight K hx, abs_mul, abs_mul]
  refine ⟨hw, ?_, ?_⟩
  · calc _ ≤ 2 * ((4 / 3) * |x|) := mul_le_mul hw ha (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  · have hasq : |weightAlpha q K x ^ 2 + weightBeta q K x| ≤ (8 / 3) * |x| := by
      calc _ ≤ |weightAlpha q K x| ^ 2 + |weightBeta q K x| := by
            rw [← abs_pow]; exact abs_add_le _ _
        _ ≤ ((4 / 3) * |x|) ^ 2 + (16 / 9) * |x| := by
            gcongr
        _ ≤ (8 / 3) * |x| := by nlinarith [abs_nonneg x]
    calc _ ≤ 2 * ((8 / 3) * |x|) := mul_le_mul hw hasq (abs_nonneg _) (by norm_num)
      _ = _ := by ring

end LucasU.Analytic
