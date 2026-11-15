/-
Generalised from lean_fibzeta FibZeta/Analytic/Decay.lean (ε = ±1, general t).
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/AnalyticEntry.lean,
lean/QZeta3/GeometricTail.lean and lean/QZeta3/AnalyticDeterminant.lean (Apache-2.0, Lean
formalisation by F. Solomon Admasu). Changes: signed nodes `w^m`, `w = εt²`, weights
`(εt)^m`, the operator `θ(θ+1) = θ² + θ`, extra factor `2^{i+j}` in the entry bound, and the
final prefactor packaged as `4096^{K²}`.
-/
import LucasU.Analytic.Jets

/-!
# Real decay (Proposition 2)

`decayBound_of_fact : DecayBound ε t`, i.e. `|Δ_K(Ξ)| ≤ 4096^{K²} t^{2 b_K}` for `K ≥ 1`.

Route (PROOF §2): `Δ_K(Ξ) = det[L(s^{i+j}/D_K)] = det[L(B_iB_j/D_K)]` (`Delta_eval_eq_det`,
`det_tripleRootGram`); the `m`-th term of `L(B_iB_j/D_K)` vanishes for `m < max(R_i,R_j)` and is
`≤ (32/3)(i+j+1)² 2^{i+j} |w|^{a_i+a_j} |w|^{m−R}` otherwise; summing,
`|L(B_iB_j/D_K)| ≤ (64/3)(i+j+1)² 2^{i+j} |w|^{a_i+a_j}`; then `Matrix.det_le` after extracting
`|w|^{a_i}` from rows and columns.
-/

open Polynomial Finset Filter Topology

namespace LucasU.Analytic

/-- Multiplication of two bounded Euler-jet triples. -/
theorem euler_product_estimate (a b u v U V A B i j t : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hi : 0 ≤ i) (hj : 0 ≤ j)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : |a| ≤ A) (hb : |b| ≤ B)
    (hu : |u| ≤ i * A * t) (hv : |v| ≤ j * B * t)
    (hU : |U| ≤ i ^ 2 * A * t) (hV : |V| ≤ j ^ 2 * B * t) :
    |a * b| ≤ A * B ∧
      |u * b + a * v| ≤ (i + j) * (A * B) * t ∧
      |U * b + 2 * u * v + a * V| ≤ (i + j) ^ 2 * (A * B) * t := by
  have hab : |a * b| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) hA
  have h₁ : |u * b + a * v| ≤ (i + j) * (A * B) * t := by
    calc _ ≤ |u * b| + |a * v| := abs_add_le _ _
      _ = |u| * |b| + |a| * |v| := by rw [abs_mul, abs_mul]
      _ ≤ (i * A * t) * B + A * (j * B * t) :=
        add_le_add (mul_le_mul hu hb (abs_nonneg _) (by positivity))
          (mul_le_mul ha hv (abs_nonneg _) hA)
      _ = _ := by ring
  have ht : t ^ 2 ≤ t := by nlinarith
  have h₂ : |U * b + 2 * u * v + a * V| ≤ (i + j) ^ 2 * (A * B) * t := by
    calc _ ≤ |U * b| + |2 * u * v| + |a * V| := abs_add_three _ _ _
      _ = |U| * |b| + 2 * |u| * |v| + |a| * |V| := by
        simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
      _ ≤ (i ^ 2 * A * t) * B + 2 * (i * A * t) * (j * B * t) + A * (j ^ 2 * B * t) := by
        apply add_le_add
        · apply add_le_add (mul_le_mul hU hb (abs_nonneg _) (by positivity))
          exact mul_le_mul (mul_le_mul_of_nonneg_left hu (by norm_num)) hv
            (abs_nonneg _) (by positivity)
        · exact mul_le_mul ha hV (abs_nonneg _) hA
      _ = (i ^ 2 + j ^ 2) * (A * B) * t + (2 * i * j * A * B) * t ^ 2 := by ring
      _ ≤ (i ^ 2 + j ^ 2) * (A * B) * t + (2 * i * j * A * B) * t :=
        add_le_add (le_refl _) (mul_le_mul_of_nonneg_left ht (by positivity))
      _ = _ := by ring
  exact ⟨hab, h₁, h₂⟩

/-- Adjoining the rational weight preserves geometric decay of a jet. -/
theorem euler_weight_estimate (a u U w v V A h x t : ℝ)
    (hA : 0 ≤ A) (hh : 0 ≤ h) (hx1 : x ≤ 1)
    (ht : x ≤ t) (ht0 : 0 ≤ t)
    (ha : |a| ≤ A) (hu : |u| ≤ h * A * t) (hU : |U| ≤ h ^ 2 * A * t)
    (hw : |w| ≤ 2) (hv : |v| ≤ (8 / 3) * x) (hV : |V| ≤ (16 / 3) * x) :
    |U * w + 2 * u * v + a * V| ≤ (16 / 3) * (h + 1) ^ 2 * A * t := by
  calc _ ≤ |U * w| + |2 * u * v| + |a * V| := abs_add_three _ _ _
    _ = |U| * |w| + 2 * |u| * |v| + |a| * |V| := by
      simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    _ ≤ (h ^ 2 * A * t) * 2 + 2 * (h * A * t) * ((8 / 3) * x) + A * ((16 / 3) * x) := by
      apply add_le_add
      · apply add_le_add (mul_le_mul hU hw (abs_nonneg _) (by positivity))
        exact mul_le_mul (mul_le_mul_of_nonneg_left hu (by norm_num)) hv
          (abs_nonneg _) (by positivity)
      · exact mul_le_mul ha hV (abs_nonneg _) hA
    _ ≤ (h ^ 2 * A * t) * 2 + (16 / 3) * (h * A * t) + (16 / 3) * A * t := by
      have h₁ := mul_le_mul_of_nonneg_left hx1 (show 0 ≤ (16 / 3) * h * A * t by positivity)
      have h₂ := mul_le_mul_of_nonneg_left ht (show 0 ≤ (16 / 3) * A by positivity)
      nlinarith only [h₁, h₂]
    _ ≤ _ := by
      have hcoeff : 2 * h ^ 2 + (16 / 3) * h + (16 / 3) ≤ (16 / 3) * (h + 1) ^ 2 := by
        nlinarith [sq_nonneg h]
      nlinarith [mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hA ht0)]

theorem contDiffAt_realPolynomial (P : ℝ[X]) (x : ℝ) : ContDiffAt ℝ 2 (fun y => P.eval y) x := by
  simp only [eval_eq_sum, Polynomial.sum_def]
  exact ContDiffAt.sum fun j _ => contDiffAt_const.mul (contDiffAt_id.pow j)

/-- Pointwise decay of a transformed entry at a surviving node `q^m`. -/
theorem tripleRoot_entry_surviving {q : ℝ} (hq : q ≠ 0) (hqhalf : |q| ≤ 1 / 2)
    (K i j m : ℕ) (hm : 1 ≤ m) (hR : max ((i + 2) / 3) ((j + 2) / 3) ≤ m) :
    |thetaOp (fun x => (tripleRootPoly q i).eval x * (tripleRootPoly q j).eval x *
        rationalWeight q K x) (q ^ m)| ≤
      (32 / 3) * ((i : ℝ) + j + 1) ^ 2 * ((2 ^ i * |q| ^ aj i) * (2 ^ j * |q| ^ aj j)) *
        |q| ^ (m - max ((i + 2) / 3) ((j + 2) / 3)) := by
  set R := max ((i + 2) / 3) ((j + 2) / 3) with hRdef
  set x := q ^ m with hxdef
  set t := |q| ^ m / |q| ^ R with htdef
  set f : ℝ → ℝ := fun x => (tripleRootPoly q i).eval x with hfdef
  set g : ℝ → ℝ := fun x => (tripleRootPoly q j).eval x with hgdef
  set A := (2 ^ i * |q| ^ aj i) * (2 ^ j * |q| ^ aj j) with hAdef
  have hq0 : 0 < |q| := abs_pos.mpr hq
  have hq1 : |q| ≤ 1 := by linarith
  have hxabs : |x| = |q| ^ m := by rw [hxdef, abs_pow]
  have hxq : |x| ≤ |q| := by rw [hxabs]; simpa only [pow_one] using pow_le_pow_of_le_one hq0.le hq1 hm
  have hx1 : |x| ≤ 1 := le_trans hxq hq1
  have hqR : 0 < |q| ^ R := pow_pos hq0 R
  have ht0 : 0 ≤ t := div_nonneg (pow_pos hq0 m).le hqR.le
  have ht1 : t ≤ 1 := (div_le_one hqR).mpr (pow_le_pow_of_le_one hq0.le hq1 hR)
  have hxt : |x| ≤ t := by
    rw [hxabs, htdef, le_div_iff₀ hqR]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (pow_le_one₀ hq0.le hq1) (pow_pos hq0 m).le
  have hi := tripleRoot_jets_common hq hq1 i m R (le_max_left _ _) hR
  have hj := tripleRoot_jets_common hq hq1 j m R (le_max_right _ _) hR
  have hf : ContDiffAt ℝ 2 f x := contDiffAt_realPolynomial (tripleRootPoly q i) x
  have hg : ContDiffAt ℝ 2 g x := contDiffAt_realPolynomial (tripleRootPoly q j) x
  have hw : ContDiffAt ℝ 2 (rationalWeight q K) x :=
    contDiffAt_rationalWeight K (factor_ne_zero hqhalf hxq K)
  have hA : 0 ≤ A := by positivity
  have hp := euler_product_estimate (f x) (g x) (theta f x) (theta g x)
    (theta (theta f) x) (theta (theta g) x) (2 ^ i * |q| ^ aj i) (2 ^ j * |q| ^ aj j) i j t
    (by positivity) (by positivity) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    ht0 ht1 hi.1 hj.1 hi.2.1 hj.2.1 hi.2.2 hj.2.2
  have hp0 : |(f * g) x| ≤ A := hp.1
  have hp1 : |theta (f * g) x| ≤ ((i : ℝ) + j) * A * t := by
    rw [theta_mul (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))]
    exact hp.2.1
  have hp2 : |theta (theta (f * g)) x| ≤ ((i : ℝ) + j) ^ 2 * A * t := by
    rw [theta_sq_mul hf hg]
    exact hp.2.2
  have hwbound := rationalWeight_euler_bounds hqhalf hxq K
  have h2 := euler_weight_estimate ((f * g) x) (theta (f * g) x)
    (theta (theta (f * g)) x) (rationalWeight q K x) (theta (rationalWeight q K) x)
    (theta (theta (rationalWeight q K)) x) A (i + j) |x| t
    hA (by positivity) hx1 hxt ht0 hp0 hp1 hp2 hwbound.1 hwbound.2.1 hwbound.2.2
  have hfg : ContDiffAt ℝ 2 (f * g) x := hf.mul hg
  have h1 : |theta ((f * g) * rationalWeight q K) x| ≤
      (16 / 3) * (((i : ℝ) + j) + 1) ^ 2 * A * t := by
    rw [theta_mul (hfg.differentiableAt (by norm_num)) (hw.differentiableAt (by norm_num))]
    have hij : (0 : ℝ) ≤ i + j := by positivity
    calc _ ≤ |theta (f * g) x| * |rationalWeight q K x| +
          |(f * g) x| * |theta (rationalWeight q K) x| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (((i : ℝ) + j) * A * t) * 2 + A * ((8 / 3) * t) := by
          apply add_le_add
          · exact mul_le_mul hp1 hwbound.1 (abs_nonneg _) (by positivity)
          · exact mul_le_mul hp0 (hwbound.2.1.trans (by linarith)) (abs_nonneg _) hA
      _ ≤ _ := by
          have hc : 2 * ((i : ℝ) + j) + 8 / 3 ≤ (16 / 3) * (((i : ℝ) + j) + 1) ^ 2 := by
            nlinarith [sq_nonneg ((i : ℝ) + j)]
          nlinarith [mul_le_mul_of_nonneg_right hc (mul_nonneg hA ht0)]
  have hfun : (fun x => (tripleRootPoly q i).eval x * (tripleRootPoly q j).eval x *
      rationalWeight q K x) = (f * g) * rationalWeight q K := rfl
  have ht : t = |q| ^ (m - R) := (pow_sub₀ |q| hq0.ne' hR).symm
  rw [hfun, thetaOp_eq_theta (f := (f * g) * rationalWeight q K) (hfg.mul hw),
    theta_sq_mul (f := f * g) (g := rationalWeight q K) hfg hw]
  calc _ ≤ |theta (theta (f * g)) x * rationalWeight q K x +
        2 * theta (f * g) x * theta (rationalWeight q K) x +
        (f * g) x * theta (theta (rationalWeight q K)) x| +
        |theta ((f * g) * rationalWeight q K) x| := abs_add_le _ _
    _ ≤ (16 / 3) * (((i : ℝ) + j) + 1) ^ 2 * A * t +
        (16 / 3) * (((i : ℝ) + j) + 1) ^ 2 * A * t := add_le_add h2 h1
    _ = _ := by rw [← ht]; ring

theorem euler_jets_mul_vanish_left {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (h₀ : f x = 0) (h₁ : theta f x = 0) (h₂ : theta (theta f) x = 0) :
    (f * g) x = 0 ∧ theta (f * g) x = 0 ∧ theta (theta (f * g)) x = 0 := by
  rw [theta_mul (f := f) (g := g) (hf.differentiableAt (by norm_num))
      (hg.differentiableAt (by norm_num)), theta_sq_mul hf hg]
  simp only [Pi.mul_apply, h₀, h₁, h₂, zero_mul, mul_zero, add_zero, and_self]

theorem euler_jets_mul_vanish_right {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (h₀ : g x = 0) (h₁ : theta g x = 0) (h₂ : theta (theta g) x = 0) :
    (f * g) x = 0 ∧ theta (f * g) x = 0 ∧ theta (theta (f * g)) x = 0 := by
  rw [mul_comm f g]
  exact euler_jets_mul_vanish_left hg hf h₀ h₁ h₂

/-- All earlier nodes contribute zero. -/
theorem tripleRoot_entry_vanish {q : ℝ} (hqhalf : |q| ≤ 1 / 2)
    (K i j m : ℕ) (hm : 1 ≤ m) (hR : m < max ((i + 2) / 3) ((j + 2) / 3)) :
    thetaOp (fun x => (tripleRootPoly q i).eval x * (tripleRootPoly q j).eval x *
      rationalWeight q K x) (q ^ m) = 0 := by
  let f : ℝ → ℝ := fun x => (tripleRootPoly q i).eval x
  let g : ℝ → ℝ := fun x => (tripleRootPoly q j).eval x
  have hf : ContDiffAt ℝ 2 f (q ^ m) := contDiffAt_realPolynomial _ _
  have hg : ContDiffAt ℝ 2 g (q ^ m) := contDiffAt_realPolynomial _ _
  have hq1 : |q| ≤ 1 := by linarith
  have hxq : |q ^ m| ≤ |q| := by
    rw [abs_pow]; simpa only [pow_one] using pow_le_pow_of_le_one (abs_nonneg q) hq1 hm
  have hw : ContDiffAt ℝ 2 (rationalWeight q K) (q ^ m) :=
    contDiffAt_rationalWeight K (factor_ne_zero hqhalf hxq K)
  have hprod : (f * g) (q ^ m) = 0 ∧ theta (f * g) (q ^ m) = 0 ∧
      theta (theta (f * g)) (q ^ m) = 0 := by
    rcases lt_max_iff.mp hR with h | h
    · obtain ⟨h₀, h₁, h₂⟩ := tripleRoot_euler_vanish q hm h
      exact euler_jets_mul_vanish_left hf hg h₀ h₁ h₂
    · obtain ⟨h₀, h₁, h₂⟩ := tripleRoot_euler_vanish q hm h
      exact euler_jets_mul_vanish_right hf hg h₀ h₁ h₂
  have hv := euler_jets_mul_vanish_left (f := f * g) (g := rationalWeight q K)
    (hf.mul hg) hw hprod.1 hprod.2.1 hprod.2.2
  have hfun : (fun x => (tripleRootPoly q i).eval x * (tripleRootPoly q j).eval x *
      rationalWeight q K x) = (f * g) * rationalWeight q K := rfl
  rw [hfun, thetaOp_eq_theta (f := (f * g) * rationalWeight q K) ((hf.mul hg).mul hw), hv.2.1,
    hv.2.2, add_zero]

/-! ### Summation over the nodes -/

/-- Geometric tail with its initial terms suppressed. -/
noncomputable def geometricTail (r : ℝ) (R n : ℕ) : ℝ :=
  if R ≤ n + 1 then r ^ ((n + 1) - R) else 0

theorem geometricTail_sum_bound {r : ℝ} (hr0 : 0 < r) (hrhalf : r ≤ 1 / 2) (R : ℕ) :
    Summable (geometricTail r R) ∧ (∑' n : ℕ, geometricTail r R n) ≤ 2 := by
  let G : ℕ → ℝ := fun n => if R ≤ n then r ^ (n - R) else 0
  have hr1 : r < 1 := by linarith
  have hs : HasSum (fun n : ℕ => G (n + R)) (1 - r)⁻¹ := by
    simpa [G] using hasSum_geometric_of_lt_one hr0.le hr1
  have hzero : ∑ i ∈ range R, G i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [G, not_le.mpr (mem_range.mp hi), ite_false]
  have hG : HasSum G (1 - r)⁻¹ := by
    have ht := (hasSum_nat_add_iff (f := G) R).mp hs
    simpa only [hzero, add_zero] using ht
  have ht : Summable (geometricTail r R) := by
    change Summable (fun m : ℕ => G (m + 1))
    exact (summable_nat_add_iff (f := G) 1).mpr hG.summable
  refine ⟨ht, ?_⟩
  have hsplit := hG.summable.sum_add_tsum_nat_add 1
  simp only [sum_range_one, hG.tsum_eq] at hsplit
  have hG0 : 0 ≤ G 0 := by dsimp [G]; split_ifs <;> positivity
  have hinv : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < 1 - r)]
    linarith
  change (∑' m : ℕ, G (m + 1)) ≤ 2
  linarith

theorem abs_tsum_le_geometricTail {r C : ℝ} (hr0 : 0 < r) (hrhalf : r ≤ 1 / 2)
    (R : ℕ) {v : ℕ → ℝ} (hv : Summable v) (hC : 0 ≤ C)
    (hbound : ∀ n, |v n| ≤ C * geometricTail r R n) :
    |∑' n : ℕ, v n| ≤ 2 * C := by
  obtain ⟨hg, hgsum⟩ := geometricTail_sum_bound hr0 hrhalf R
  have ha : Summable (fun n => |v n|) := hv.abs
  calc |∑' n : ℕ, v n| ≤ ∑' n : ℕ, |v n| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f := v) (by
          simpa only [Real.norm_eq_abs] using ha)
    _ ≤ ∑' n : ℕ, C * geometricTail r R n := ha.tsum_le_tsum hbound (hg.mul_left C)
    _ = C * ∑' n : ℕ, geometricTail r R n := tsum_mul_left
    _ ≤ C * 2 := mul_le_mul_of_nonneg_left hgsum hC
    _ = 2 * C := mul_comm _ _

variable {ε : ℤ} {t : ℝ} [hG : Fact (Good ε t)]

omit hG in
theorem weight_eq_DK_inv (K : ℕ) : rationalWeight (wpar ε t) K = fun x => (DK ε t K x)⁻¹ := by
  funext x
  simp only [rationalWeight, DK, Finset.prod_inv_distrib]

omit hG in
/-- The entry functions in product form. -/
theorem entry_fun_eq (K i j : ℕ) :
    (fun x => (tripleRootPoly (wpar ε t) i).eval x * (tripleRootPoly (wpar ε t) j).eval x / DK ε t K x) =
      (fun x => (tripleRootPoly (wpar ε t) i).eval x * (tripleRootPoly (wpar ε t) j).eval x *
        rationalWeight (wpar ε t) K x) := by
  rw [weight_eq_DK_inv]
  funext x
  rw [div_eq_mul_inv]

/-- Each term of a transformed entry is dominated by a geometric tail. -/
theorem tripleRoot_entry_majorant (K i j n : ℕ) :
    |Lterm ε t (fun x => (tripleRootPoly (wpar ε t) i).eval x *
        (tripleRootPoly (wpar ε t) j).eval x / DK ε t K x) n| ≤
      ((32 / 3) * ((i : ℝ) + j + 1) ^ 2 *
        ((2 ^ i * (t ^ 2) ^ aj i) * (2 ^ j * (t ^ 2) ^ aj j))) *
        geometricTail (t ^ 2) (max ((i + 2) / 3) ((j + 2) / 3)) n := by
  have hq : (wpar ε t) ≠ 0 := w_ne_zero
  have hqhalf : |(wpar ε t)| ≤ 1 / 2 := by rw [abs_w]; exact (t_sq_le_half ε t)
  rw [Lterm, entry_fun_eq, pt, abs_mul]
  have hrho : |((ε : ℝ) * t) ^ (n + 1)| ≤ 1 := by
    rw [abs_pow, abs_rho]; exact pow_le_one₀ (t_pos ε t).le (t_lt_one ε t).le
  unfold geometricTail
  split_ifs with hR
  · have h := tripleRoot_entry_surviving hq hqhalf K i j (n + 1) (by omega) hR
    rw [abs_w] at h
    calc _ ≤ 1 * |thetaOp _ ((wpar ε t) ^ (n + 1))| :=
          mul_le_mul_of_nonneg_right hrho (abs_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h
  · rw [tripleRoot_entry_vanish hqhalf K i j (n + 1) (by omega) (by omega)]
    simp

/-- The transformed Gram entry bound. -/
theorem tripleRoot_entry_bound (K i j : ℕ) :
    |Lfun ε t (fun x => (tripleRootPoly (wpar ε t) i).eval x *
        (tripleRootPoly (wpar ε t) j).eval x / DK ε t K x)| ≤
      (64 / 3) * ((i : ℝ) + j + 1) ^ 2 *
        ((2 ^ i * (t ^ 2) ^ aj i) * (2 ^ j * (t ^ 2) ^ aj j)) := by
  have h := abs_tsum_le_geometricTail (t_sq_pos ε t) (t_sq_le_half ε t)
    (max ((i + 2) / 3) ((j + 2) / 3)) (summable_tripleRootGram_entry (ε := ε) (t := t) (wpar ε t) K i j)
    (by positivity) (fun n => tripleRoot_entry_majorant K i j n)
  rw [Lfun_eq_tsum]
  linarith

/-! ### The determinant -/

theorem prod_tripleRoot_weights (r : ℝ) (K : ℕ) :
    (∏ i : Fin K, r ^ aj i.val) ^ 2 = r ^ bK K := by
  rw [Finset.prod_pow_eq_pow_sum, ← pow_mul]
  congr 1
  simp only [bK, Fin.sum_univ_eq_sum_range]
  omega

theorem gram_det_bound (K : ℕ) :
    |(gramR ε t K).det| ≤
      (K.factorial : ℝ) * ((64 / 3) * (2 * (K : ℝ)) ^ 2 * 4 ^ K) ^ K * (t ^ 2) ^ bK K := by
  rw [← det_tripleRootGram (ε := ε) (t := t) (wpar ε t) K]
  have hentry : ∀ i j : Fin K, |tripleRootGram ε t (wpar ε t) K i j| ≤
      ((64 / 3) * (2 * (K : ℝ)) ^ 2 * 4 ^ K) * (t ^ 2) ^ aj i.val * (t ^ 2) ^ aj j.val := by
    intro i j
    have hi : (i.val : ℝ) + 1 ≤ K := by exact_mod_cast i.isLt
    have hj : (j.val : ℝ) + 1 ≤ K := by exact_mod_cast j.isLt
    have hsq : ((i.val : ℝ) + j.val + 1) ^ 2 ≤ (2 * (K : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h2 : (2 : ℝ) ^ i.val * 2 ^ j.val ≤ 4 ^ K := by
      rw [← pow_add, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    calc |tripleRootGram ε t (wpar ε t) K i j| ≤ (64 / 3) * ((i.val : ℝ) + j.val + 1) ^ 2 *
          ((2 ^ i.val * (t ^ 2) ^ aj i.val) * (2 ^ j.val * (t ^ 2) ^ aj j.val)) :=
          tripleRoot_entry_bound K i.val j.val
      _ = (64 / 3) * ((i.val : ℝ) + j.val + 1) ^ 2 * (2 ^ i.val * 2 ^ j.val) *
          ((t ^ 2) ^ aj i.val * (t ^ 2) ^ aj j.val) := by ring
      _ ≤ (64 / 3) * (2 * (K : ℝ)) ^ 2 * 4 ^ K *
          ((t ^ 2) ^ aj i.val * (t ^ 2) ^ aj j.val) := by gcongr
      _ = _ := by ring
  have h := abs_det_le_of_scaled_entries (tripleRootGram ε t (wpar ε t) K)
    (fun i => (t ^ 2) ^ aj i.val) _ (fun i => pow_pos (t_sq_pos ε t) _) hentry
  simpa only [Fintype.card_fin, prod_tripleRoot_weights] using h

theorem prefactor_le (K : ℕ) (hK : 1 ≤ K) :
    (K.factorial : ℝ) * ((64 / 3) * (2 * (K : ℝ)) ^ 2 * 4 ^ K) ^ K ≤ (4096 : ℝ) ^ (K ^ 2) := by
  have hK2 : (K : ℝ) ≤ 2 ^ K := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hfact : (K.factorial : ℝ) ≤ 2 ^ (K ^ 2) := by
    calc (K.factorial : ℝ) ≤ (K : ℝ) ^ K := by exact_mod_cast Nat.factorial_le_pow K
      _ ≤ (2 ^ K) ^ K := pow_le_pow_left₀ (Nat.cast_nonneg _) hK2 K
      _ = 2 ^ (K ^ 2) := by rw [← pow_mul, sq]
  have hM : (64 / 3) * (2 * (K : ℝ)) ^ 2 * 4 ^ K ≤ 2 ^ (11 * K) := by
    have h1 : (2 * (K : ℝ)) ^ 2 ≤ 4 * 4 ^ K := by
      have : (K : ℝ) ^ 2 ≤ 4 ^ K := by
        calc (K : ℝ) ^ 2 ≤ (2 ^ K) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hK2 2
          _ = 4 ^ K := by rw [← pow_mul, mul_comm K 2, pow_mul]; norm_num
      nlinarith
    have h4 : (4 : ℝ) ^ K = 2 ^ (2 * K) := by rw [pow_mul]; norm_num
    have h7 : (2 : ℝ) ^ 7 ≤ 2 ^ (7 * K) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc (64 / 3) * (2 * (K : ℝ)) ^ 2 * 4 ^ K ≤ (64 / 3) * (4 * 4 ^ K) * 4 ^ K := by gcongr
      _ ≤ 2 ^ 7 * (2 ^ (2 * K) * 2 ^ (2 * K)) := by rw [h4]; nlinarith [pow_pos (two_pos (α := ℝ)) (2 * K)]
      _ ≤ 2 ^ (7 * K) * (2 ^ (2 * K) * 2 ^ (2 * K)) := by gcongr
      _ = 2 ^ (11 * K) := by rw [← pow_add, ← pow_add]; ring_nf
  have hMK : ((64 / 3) * (2 * (K : ℝ)) ^ 2 * 4 ^ K) ^ K ≤ 2 ^ (11 * K ^ 2) := by
    calc _ ≤ ((2 : ℝ) ^ (11 * K)) ^ K := pow_le_pow_left₀ (by positivity) hM K
      _ = 2 ^ (11 * K ^ 2) := by rw [← pow_mul]; ring_nf
  calc _ ≤ (2 : ℝ) ^ (K ^ 2) * 2 ^ (11 * K ^ 2) := mul_le_mul hfact hMK (by positivity) (by positivity)
    _ = (4096 : ℝ) ^ (K ^ 2) := by
        rw [← pow_add, show (4096 : ℝ) = 2 ^ 12 by norm_num, ← pow_mul]; ring_nf

/-- **Proposition 2** (real decay). -/
theorem decayBound_of_fact : DecayBound ε t := by
  refine ⟨4096, by norm_num, fun K hK => ?_⟩
  rw [Delta_eval_eq_det]
  calc |(gramR ε t K).det| ≤ (K.factorial : ℝ) * ((64 / 3) * (2 * (K : ℝ)) ^ 2 * 4 ^ K) ^ K *
        (t ^ 2) ^ bK K := gram_det_bound K
    _ ≤ (4096 : ℝ) ^ (K ^ 2) * (t ^ 2) ^ bK K :=
        mul_le_mul_of_nonneg_right (prefactor_le K hK) (pow_nonneg (t_sq_pos ε t).le _)
    _ = (4096 : ℝ) ^ (K ^ 2) * t ^ (2 * bK K) := by rw [pow_mul]

end LucasU.Analytic
