import LucasU.Statements

-- Generalised from lean_fibzeta FibZeta/NonVan/Cauchy.lean (ε = ±1, general t).
-- Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/CauchyAtInfinity.lean,
-- lean/QZeta3/CauchyExterior.lean and lean/QZeta3/MomentDecay.lean (Apache-2.0, Lean formalisation by
-- F. Solomon Admasu). Changes: the Fibonacci Cauchy kernel `2ρⁿwⁿz/(z − wⁿ)³` (alternating weights and
-- poles), moments `ν_k` of `Defs.lean`, and the node values `𝓕(w^{−a}) = 2t^a(Ξ − S_a)`.

/-!
# The Cauchy transform `𝓕(z) = L(1/(z − s))` at infinity (PROOF §5, PROOF_U §5)

`𝓕(z) = ∑_{n ≥ 1} ρⁿ · 2wⁿz/(z − wⁿ)³` with `ρ = ε t`, `w = ε t²`, under `Good ε t`
(`ε = ±1`, `0 < t ≤ φ⁻¹`; only `0 < t < 1` and `ε² = 1` are used).

* `cauchyF_inv_eq` : `𝓕(1/u) = u ∑_k ν_k u^k` for `0 < |u| < 1`;
* `meromorphicAt_cauchyF_inv` : `u ↦ 𝓕(1/u)` is meromorphic (indeed analytic) at `0`;
* `analyticAt_cauchyF_of_one_lt_abs` : `𝓕` is analytic at every `|z| > 1`;
* `tendsto_cauchyF_monomial_sub` : `𝓕(z) z^k − ∑_{j<k} ν_j z^{k−1−j} → 0` as `z → +∞`;
* `cauchyF_node` : `𝓕(x_a) = 2 t^a (Ξ − S_a)` at `x_a = w^{−a}` (the pole moments of Lemma 1(ii)).
-/

open Filter Topology Finset
open scoped ENNReal NNReal

namespace LucasU.NonVan

variable {ε : ℤ} {t : ℝ}

/-! ### Elementary facts about `t`, `ρ = ε t`, `w = ε t²` -/

theorem t_pos (hG : Good ε t) : 0 < t := hG.2.1

theorem t_lt_one (hG : Good ε t) : t < 1 :=
  lt_of_le_of_lt hG.2.2 (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)

theorem eps_sq (hG : Good ε t) : (ε : ℝ) ^ 2 = 1 := by
  rcases hG.1 with h1 | h1 <;> simp [h1]

theorem abs_eps (hG : Good ε t) : |(ε : ℝ)| = 1 := by
  rcases hG.1 with h1 | h1 <;> simp [h1]

theorem tsq_pos (hG : Good ε t) : 0 < t ^ 2 := pow_pos (t_pos hG) 2

theorem tsq_lt_one (hG : Good ε t) : t ^ 2 < 1 := pow_lt_one₀ (t_pos hG).le (t_lt_one hG) (by norm_num)

theorem norm_tsq_lt_one (hG : Good ε t) : ‖t ^ 2‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (tsq_pos hG)]; exact (tsq_lt_one hG)

theorem abs_w (hG : Good ε t) : |wpar ε t| = t ^ 2 := by
  rw [wpar, abs_mul, abs_eps hG, one_mul, abs_of_pos (tsq_pos hG)]

theorem abs_w_pow (hG : Good ε t) (m : ℕ) : |(wpar ε t) ^ m| = (t ^ 2) ^ m := by
  rw [abs_pow, abs_w hG]

theorem abs_rho_pow (hG : Good ε t) (m : ℕ) : |((ε : ℝ) * t) ^ m| = t ^ m := by
  rw [abs_pow, abs_mul, abs_eps hG, one_mul, abs_of_pos (t_pos hG)]

theorem w_ne_zero (hG : Good ε t) : (wpar ε t) ≠ 0 := by
  intro h0
  have := abs_w hG
  rw [h0, abs_zero] at this
  exact (tsq_pos hG).ne this

theorem rho_ne_zero (hG : Good ε t) : (ε : ℝ) * t ≠ 0 := by
  intro h0
  have := abs_rho_pow hG 1
  rw [pow_one, pow_one, h0, abs_zero] at this
  exact (t_pos hG).ne this

theorem w_pow_ne_zero (hG : Good ε t) (m : ℕ) : (wpar ε t) ^ m ≠ 0 := pow_ne_zero _ (w_ne_zero hG)

theorem rho_mul_w_pow (hG : Good ε t) (m : ℕ) : ((ε : ℝ) * t) ^ m * (wpar ε t) ^ m = (t ^ 3) ^ m := by
  rw [← mul_pow]; congr 1; unfold wpar; linear_combination t ^ 3 * eps_sq hG

theorem tsq_pow_le_tsq (hG : Good ε t) {m : ℕ} (hm : 1 ≤ m) : (t ^ 2) ^ m ≤ t ^ 2 := by
  simpa using pow_le_pow_of_le_one (tsq_pos hG).le (tsq_lt_one hG).le hm

theorem tsq_pow_lt_one (hG : Good ε t) {m : ℕ} (hm : 1 ≤ m) : (t ^ 2) ^ m < 1 :=
  lt_of_le_of_lt ((tsq_pow_le_tsq hG) hm) (tsq_lt_one hG)

/-! ### The moments `ν_k` -/

theorem abs_alpha (hG : Good ε t) (k : ℕ) : |alpha ε t k| = t * (t ^ 2) ^ k := by
  unfold alpha; rw [abs_mul, abs_mul, abs_eps hG, one_mul, abs_of_pos (t_pos hG), (abs_w_pow hG)]

theorem abs_alpha_le_t (hG : Good ε t) (k : ℕ) : |alpha ε t k| ≤ t := by
  rw [(abs_alpha hG)]
  exact mul_le_of_le_one_right (t_pos hG).le (pow_le_one₀ (tsq_pos hG).le (tsq_lt_one hG).le)

theorem abs_alpha_le_pow (hG : Good ε t) (k : ℕ) : |alpha ε t k| ≤ (t ^ 2) ^ k := by
  rw [(abs_alpha hG)]
  exact mul_le_of_le_one_left (by positivity) (t_lt_one hG).le

theorem norm_alpha_lt_one (hG : Good ε t) (k : ℕ) : ‖alpha ε t k‖ < 1 := by
  rw [Real.norm_eq_abs]; exact lt_of_le_of_lt ((abs_alpha_le_t hG) k) (t_lt_one hG)

theorem one_sub_t_le_abs (hG : Good ε t) (k : ℕ) : 1 - t ≤ |1 - alpha ε t k| := by
  have h1 := (abs_alpha_le_t hG) k
  have h2 := abs_sub_abs_le_abs_sub (1 : ℝ) (alpha ε t k)
  rw [abs_one] at h2
  linarith

theorem one_sub_alpha_ne (hG : Good ε t) (k : ℕ) : 1 - alpha ε t k ≠ 0 := by
  intro h
  have := (one_sub_t_le_abs hG) k
  rw [h, abs_zero] at this
  linarith [(t_lt_one hG)]

theorem abs_nu_le (hG : Good ε t) (k : ℕ) : |nu ε t k| ≤ 2 / (1 - t) * ((k : ℝ) ^ 2 * (t ^ 2) ^ k) := by
  have ht1 : 0 < 1 - t := by linarith [(t_lt_one hG)]
  have hk : ((k * (k + 1) : ℕ) : ℝ) ≤ ((2 * k ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast (by nlinarith : k * (k + 1) ≤ 2 * k ^ 2)
  push_cast at hk
  unfold nu
  rw [abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) + 1))]
  rw [div_le_iff₀ (lt_of_lt_of_le ht1 ((one_sub_t_le_abs hG) k))]
  have h1 := (abs_alpha_le_pow hG) k
  have h2 := (one_sub_t_le_abs hG) k
  have h3 : (0 : ℝ) ≤ (t ^ 2) ^ k := by positivity
  calc (k : ℝ) * ((k : ℝ) + 1) * |alpha ε t k| ≤ (2 * (k : ℝ) ^ 2) * (t ^ 2) ^ k :=
        mul_le_mul hk h1 (abs_nonneg _) (by positivity)
    _ = 2 / (1 - t) * ((k : ℝ) ^ 2 * (t ^ 2) ^ k) * (1 - t) := by field_simp
    _ ≤ 2 / (1 - t) * ((k : ℝ) ^ 2 * (t ^ 2) ^ k) * |1 - alpha ε t k| :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

theorem summable_abs_nu (hG : Good ε t) : Summable (fun k : ℕ => |nu ε t k|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (abs_nu_le hG)
    ((summable_pow_mul_geometric_of_norm_lt_one 2 (norm_tsq_lt_one hG)).mul_left _)

theorem summable_nu_mul_pow (hG : Good ε t) {u : ℝ} (hu : ‖u‖ < 1) : Summable (fun k : ℕ => nu ε t k * u ^ k) := by
  apply Summable.of_norm_bounded (summable_abs_nu hG)
  intro k
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (pow_le_one₀ (abs_nonneg _) (by simpa [Real.norm_eq_abs] using hu.le))

/-- The shifted moment power series `∑_n ν_{n+k} u^n`. -/
noncomputable def momentSeries (ε : ℤ) (t : ℝ) (k : ℕ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n => nu ε t (n + k))

theorem momentSeries_radius_ge_one (hG : Good ε t) (k : ℕ) : (1 : ℝ≥0∞) ≤ (momentSeries ε t k).radius := by
  apply (momentSeries ε t k).le_radius_of_summable (r := 1)
  simpa [momentSeries, FormalMultilinearSeries.ofScalars_norm, Real.norm_eq_abs] using
    (summable_nat_add_iff k).mpr (summable_abs_nu hG)

theorem analyticAt_moment (hG : Good ε t) (k : ℕ) {u : ℝ} (hu : ‖u‖ < 1) :
    AnalyticAt ℝ (fun v : ℝ => ∑' n : ℕ, nu ε t (n + k) * v ^ n) u := by
  have huR : u ∈ Metric.eball (0 : ℝ) (momentSeries ε t k).radius := by
    apply mem_eball_zero_iff.mpr
    apply lt_of_lt_of_le _ ((momentSeries_radius_ge_one hG) k)
    exact ENNReal.coe_lt_coe.mpr hu
  have h := (momentSeries ε t k).analyticOnNhd u huR
  convert h using 1
  ext v
  simpa [momentSeries, FormalMultilinearSeries.ofScalarsSum, smul_eq_mul] using
    (FormalMultilinearSeries.ofScalars_sum_eq (fun n => nu ε t (n + k)) v).symm

/-! ### The Cauchy transform -/

/-- The `n`-th kernel `2ρ^{n+1}w^{n+1}z/(z − w^{n+1})³`. -/
noncomputable def kern (ε : ℤ) (t : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  2 * ((ε : ℝ) * t) ^ (n + 1) * (wpar ε t) ^ (n + 1) * z / (z - (wpar ε t) ^ (n + 1)) ^ 3

/-- `𝓕(z) = L(1/(z − s)) = ∑_{n ≥ 1} ρⁿ · 2wⁿz/(z − wⁿ)³`. -/
noncomputable def cauchyF (ε : ℤ) (t : ℝ) (z : ℝ) : ℝ := ∑' n : ℕ, kern ε t n z

theorem hasSum_kk1_geometric {y : ℝ} (hy : ‖y‖ < 1) :
    HasSum (fun k : ℕ => (k : ℝ) * ((k : ℝ) + 1) * y ^ k) (2 * y / (1 - y) ^ 3) := by
  have h1 := hasSum_sq_mul_geometric_of_norm_lt_one hy
  have h2 := hasSum_coe_mul_geometric_of_norm_lt_one hy
  have hy1 : 1 - y ≠ 0 := by
    intro h
    have : y = 1 := by linarith
    rw [this, norm_one] at hy
    exact lt_irrefl _ hy
  convert h1.add h2 using 1
  · funext k; ring
  · field_simp; ring

/-- `𝓕(1/u) = u ∑_k ν_k u^k` for `0 < |u| < 1`. -/
theorem cauchyF_inv_eq (hG : Good ε t) {u : ℝ} (hu : ‖u‖ < 1) (hu0 : u ≠ 0) :
    cauchyF ε t u⁻¹ = u * ∑' k : ℕ, nu ε t k * u ^ k := by
  have hu' : |u| < 1 := by simpa [Real.norm_eq_abs] using hu
  let f : ℕ × ℕ → ℝ := fun nk =>
    (nk.2 : ℝ) * ((nk.2 : ℝ) + 1) * (alpha ε t nk.2) ^ (nk.1 + 1) * u ^ (nk.2 + 1)
  have hf : Summable f := by
    have hg : Summable (fun n : ℕ => t ^ (n + 1)) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (t_pos hG).le (t_lt_one hG))
    have hh : Summable (fun k : ℕ => (k : ℝ) * ((k : ℝ) + 1) * (t ^ 2) ^ k) := by
      have := ((summable_pow_mul_geometric_of_norm_lt_one 2 (norm_tsq_lt_one hG)).add
        (summable_pow_mul_geometric_of_norm_lt_one 1 (norm_tsq_lt_one hG)))
      convert this using 1
      funext k; ring
    apply Summable.of_norm_bounded (hg.mul_of_nonneg hh (fun n => (pow_pos (t_pos hG) _).le)
      (fun k => mul_nonneg (by positivity) (pow_nonneg (tsq_pos hG).le _)))
    rintro ⟨n, k⟩
    simp only [f, Real.norm_eq_abs, abs_mul, abs_pow]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ)),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1), (abs_alpha hG)]
    have hupow : |u| ^ (k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) hu'.le
    have hpow : (t * (t ^ 2) ^ k) ^ (n + 1) ≤ t ^ (n + 1) * (t ^ 2) ^ k := by
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_left _ (pow_pos (t_pos hG) _).le
      rw [← pow_mul]
      exact pow_le_pow_of_le_one (tsq_pos hG).le (tsq_lt_one hG).le (by nlinarith)
    calc (k : ℝ) * ((k : ℝ) + 1) * (t * (t ^ 2) ^ k) ^ (n + 1) * |u| ^ (k + 1)
        ≤ (k : ℝ) * ((k : ℝ) + 1) * (t ^ (n + 1) * (t ^ 2) ^ k) * 1 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hupow
            (by positivity)
            (mul_nonneg (by positivity) (mul_nonneg (pow_pos (t_pos hG) _).le (pow_nonneg (tsq_pos hG).le _)))
      _ = t ^ (n + 1) * ((k : ℝ) * ((k : ℝ) + 1) * (t ^ 2) ^ k) := by ring
  have hrow : ∀ n : ℕ, ∑' k : ℕ, f (n, k) = kern ε t n u⁻¹ := by
    intro n
    let y : ℝ := (wpar ε t) ^ (n + 1) * u
    have hy : ‖y‖ < 1 := by
      rw [Real.norm_eq_abs, abs_mul, (abs_w_pow hG)]
      calc (t ^ 2) ^ (n + 1) * |u| < 1 * 1 := by
            apply mul_lt_mul' ((tsq_pow_lt_one hG) (by omega)).le hu' (abs_nonneg _) one_pos
        _ = 1 := by ring
    have hs := (hasSum_kk1_geometric hy).mul_left (((ε : ℝ) * t) ^ (n + 1) * u)
    have heq : (fun k : ℕ => ((ε : ℝ) * t) ^ (n + 1) * u * ((k : ℝ) * ((k : ℝ) + 1) * y ^ k)) =
        fun k => f (n, k) := by
      funext k
      simp only [f, alpha, y, mul_pow, ← pow_mul, Nat.mul_comm k (n + 1)]
      ring
    rw [heq] at hs
    rw [hs.tsum_eq]
    have hy1 : 1 - y ≠ 0 := by
      intro h
      have : y = 1 := by linarith
      rw [this, norm_one] at hy
      exact lt_irrefl _ hy
    have hz : u⁻¹ - (wpar ε t) ^ (n + 1) ≠ 0 := by
      intro h
      apply hy1
      have : (wpar ε t) ^ (n + 1) = u⁻¹ := (sub_eq_zero.mp h).symm
      simp only [y, this, inv_mul_cancel₀ hu0, sub_self]
    unfold kern
    have hyu : u⁻¹ - (wpar ε t) ^ (n + 1) = u⁻¹ * (1 - y) := by
      simp only [y]; field_simp
    rw [hyu, mul_pow u⁻¹, inv_pow]
    simp only [y]
    field_simp
  have hcol : ∀ k : ℕ, ∑' n : ℕ, f (n, k) = nu ε t k * u ^ (k + 1) := by
    intro k
    have hs := hasSum_geometric_of_norm_lt_one ((norm_alpha_lt_one hG) k)
    have hs' : HasSum (fun n : ℕ => alpha ε t k ^ (n + 1)) (alpha ε t k / (1 - alpha ε t k)) := by
      have := hs.mul_left (alpha ε t k)
      convert this using 1
      · funext n; ring
      · field_simp [(one_sub_alpha_ne hG) k]
    have := hs'.mul_left ((k : ℝ) * ((k : ℝ) + 1)) |>.mul_right (u ^ (k + 1))
    rw [show (fun n : ℕ => f (n, k)) = fun n => (k : ℝ) * ((k : ℝ) + 1) * alpha ε t k ^ (n + 1) *
      u ^ (k + 1) from rfl, this.tsum_eq]
    unfold nu
    ring
  calc cauchyF ε t u⁻¹ = ∑' n : ℕ, ∑' k : ℕ, f (n, k) := by
        unfold cauchyF; exact tsum_congr (fun n => (hrow n).symm)
    _ = ∑' k : ℕ, ∑' n : ℕ, f (n, k) := (Summable.tsum_comm (f := fun n k => f (n, k)) hf).symm
    _ = ∑' k : ℕ, nu ε t k * u ^ (k + 1) := tsum_congr hcol
    _ = u * ∑' k : ℕ, nu ε t k * u ^ k := by
        rw [← tsum_mul_left]; congr 1; funext k; ring

theorem meromorphicAt_cauchyF_inv (hG : Good ε t) : MeromorphicAt (fun u : ℝ => cauchyF ε t u⁻¹) 0 := by
  have h : AnalyticAt ℝ (fun u : ℝ => u * ∑' n : ℕ, nu ε t (n + 0) * u ^ n) 0 :=
    analyticAt_id.mul ((analyticAt_moment hG) 0 (by simp))
  apply h.meromorphicAt.congr
  have hn : ∀ᶠ u : ℝ in 𝓝 (0 : ℝ), ‖u‖ < 1 :=
    continuous_norm.continuousAt.eventually_lt continuousAt_const (by norm_num)
  filter_upwards [hn.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with u hu hu0
  simpa using ((cauchyF_inv_eq hG) hu (by simpa using hu0)).symm

theorem analyticAt_cauchyF_of_one_lt_abs (hG : Good ε t) {z : ℝ} (hz : 1 < |z|) : AnalyticAt ℝ (cauchyF ε t) z := by
  have hz0 : z ≠ 0 := by intro h; rw [h, abs_zero] at hz; linarith
  have hinv : ‖z⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_inv]; exact inv_lt_one_of_one_lt₀ hz
  have hi : AnalyticAt ℝ (fun w : ℝ => w⁻¹) z := analyticAt_id.inv hz0
  have h := hi.mul (((analyticAt_moment hG) 0 hinv).comp hi)
  apply h.congr
  have hn : ∀ᶠ w : ℝ in 𝓝 z, 1 < |w| :=
    continuousAt_const.eventually_lt continuous_abs.continuousAt hz
  filter_upwards [hn] with w hw
  have hw0 : w ≠ 0 := by intro h; rw [h, abs_zero] at hw; linarith
  have hwinv : ‖w⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_inv]; exact inv_lt_one_of_one_lt₀ hw
  simpa using ((cauchyF_inv_eq hG) hwinv (inv_ne_zero hw0)).symm

/-! ### Polynomial part at infinity (from `MomentDecay.lean`) -/

/-- `∑_{j<k} ν_j z^{k−1−j}`, the polynomial part of `𝓕(z) z^k`. -/
noncomputable def momentPolynomial (ε : ℤ) (t : ℝ) (k : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ range k, nu ε t j * z ^ (k - 1 - j)

theorem cauchyF_remainder (hG : Good ε t) {u : ℝ} (hu : ‖u‖ < 1) (hu0 : u ≠ 0) (k : ℕ) :
    cauchyF ε t u⁻¹ * (u⁻¹) ^ k - momentPolynomial ε t k u⁻¹ =
      u * ∑' n : ℕ, nu ε t (n + k) * u ^ n := by
  have hsplit := ((summable_nu_mul_pow hG) hu).sum_add_tsum_nat_add k
  have htail : (∑' n : ℕ, nu ε t (n + k) * u ^ (n + k)) =
      u ^ k * ∑' n : ℕ, nu ε t (n + k) * u ^ n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [pow_add]
    ring
  rw [htail] at hsplit
  have hpoly : u ^ k * momentPolynomial ε t k u⁻¹ =
      u * ∑ j ∈ range k, nu ε t j * u ^ j := by
    unfold momentPolynomial
    rw [mul_sum, mul_sum]
    apply sum_congr rfl
    intro j hj
    have hjk : j < k := mem_range.mp hj
    have he : k = (k - 1 - j) + (j + 1) := by omega
    have hpow : u ^ k = u ^ (k - 1 - j) * u ^ (j + 1) := by rw [← pow_add, ← he]
    have hc : u ^ (k - 1 - j) * (u⁻¹) ^ (k - 1 - j) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hu0, one_pow]
    calc u ^ k * (nu ε t j * (u⁻¹) ^ (k - 1 - j)) =
        nu ε t j * u ^ (j + 1) * (u ^ (k - 1 - j) * (u⁻¹) ^ (k - 1 - j)) := by rw [hpow]; ring
      _ = u * (nu ε t j * u ^ j) := by rw [hc, pow_succ]; ring
  apply (mul_left_cancel₀ (pow_ne_zero k hu0))
  rw [mul_sub, hpoly, (cauchyF_inv_eq hG) hu hu0]
  have hinv : u ^ k * (u⁻¹) ^ k = 1 := by rw [← mul_pow, mul_inv_cancel₀ hu0, one_pow]
  calc u ^ k * ((u * ∑' n : ℕ, nu ε t n * u ^ n) * (u⁻¹) ^ k) -
          u * ∑ j ∈ range k, nu ε t j * u ^ j =
        u * (∑' n : ℕ, nu ε t n * u ^ n) * (u ^ k * (u⁻¹) ^ k) -
          u * ∑ j ∈ range k, nu ε t j * u ^ j := by ring
    _ = _ := by rw [hinv, ← hsplit]; ring

theorem tendsto_cauchyF_monomial_sub (hG : Good ε t) (k : ℕ) :
    Tendsto (fun z : ℝ => cauchyF ε t z * z ^ k - momentPolynomial ε t k z) atTop (𝓝 0) := by
  have htail := ((analyticAt_moment hG) k (by simp)).continuousAt.tendsto.comp
    (tendsto_inv_atTop_zero : Tendsto (fun z : ℝ => z⁻¹) atTop (𝓝 0))
  have hprod := (tendsto_inv_atTop_zero : Tendsto (fun z : ℝ => z⁻¹) atTop (𝓝 0)).mul htail
  simp only [zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with z hz
  have hz0 : z ≠ 0 := by linarith
  have hzinv : ‖z⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by linarith))]
    exact inv_lt_one_of_one_lt₀ hz
  simpa using ((cauchyF_remainder hG) hzinv (inv_ne_zero hz0) k).symm

/-! ### Values at the interpolation nodes -/

theorem abs_psi_le (hG : Good ε t) (N : ℕ) (hN : 1 ≤ N) : |psi ε t N| ≤ (t ^ 3) ^ N / (1 - t ^ 2) ^ 3 := by
  unfold psi
  have h1 : 0 < 1 - t ^ 2 := by linarith [(tsq_lt_one hG)]
  have h2 : 1 - t ^ 2 ≤ |1 - (wpar ε t) ^ N| := by
    have := abs_sub_abs_le_abs_sub (1 : ℝ) ((wpar ε t) ^ N)
    rw [abs_one, (abs_w_pow hG)] at this
    linarith [(tsq_pow_le_tsq hG) hN]
  rw [abs_div, abs_pow, abs_pow, abs_of_pos (t_pos hG), ← pow_mul]
  apply div_le_div₀ (pow_pos (t_pos hG) _).le le_rfl (pow_pos h1 3)
  exact pow_le_pow_left₀ h1.le h2 3

theorem summable_psi_succ (hG : Good ε t) : Summable (fun N : ℕ => psi ε t (N + 1)) := by
  have hg : Summable (fun N : ℕ => (t ^ 3) ^ (N + 1) / (1 - t ^ 2) ^ 3) := by
    apply Summable.div_const
    exact (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (pow_pos (t_pos hG) 3).le
      (pow_lt_one₀ (t_pos hG).le (t_lt_one hG) (by norm_num)))
  exact Summable.of_norm_bounded hg (fun N => by
    rw [Real.norm_eq_abs]; exact (abs_psi_le hG) (N + 1) (by omega))

theorem S_eq_sum_range (a : ℕ) : S ε t a = ∑ i ∈ range a, psi ε t (i + 1) := by
  induction a with
  | zero => simp [S]
  | succ a ih =>
      rw [sum_range_succ, ← ih, S, S, Finset.sum_Icc_succ_top (by omega)]

theorem kern_node (hG : Good ε t) (n a : ℕ) :
    kern ε t n (node ε t a) = 2 * t ^ a * psi ε t (n + a + 1) := by
  unfold kern node psi
  have hVW : (wpar ε t) ^ (n + a + 1) = (wpar ε t) ^ (n + 1) * (wpar ε t) ^ a := by
    rw [← pow_add]; congr 1; omega
  set W : ℝ := (wpar ε t) ^ a with hW
  set V : ℝ := (wpar ε t) ^ (n + 1) with hV
  have hW0 : W ≠ 0 := (w_pow_ne_zero hG) a
  have h1 : 1 - V * W ≠ 0 := by
    rw [← hVW]; intro h
    have h' : |(wpar ε t) ^ (n + a + 1)| = 1 := by rw [← sub_eq_zero.mp h, abs_one]
    rw [(abs_w_pow hG)] at h'
    linarith [(tsq_pow_lt_one hG) (show 1 ≤ n + a + 1 by omega)]
  have hden : W⁻¹ - V = W⁻¹ * (1 - V * W) := by field_simp
  rw [hden, hVW]
  have hrw : ((ε : ℝ) * t) ^ (n + 1) * V = (t ^ 3) ^ (n + 1) := (rho_mul_w_pow hG) (n + 1)
  have hW2 : W ^ 2 = (t ^ 4) ^ a := by
    rw [hW, ← pow_mul, mul_comm, pow_mul]; congr 1; unfold wpar; linear_combination t ^ 4 * eps_sq hG
  have hpow : t ^ (3 * (n + a + 1)) = (t ^ 3) ^ (n + 1) * t ^ (3 * a) := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  have h4 : (t ^ 4) ^ a = t ^ a * t ^ (3 * a) := by
    rw [← pow_mul, ← pow_add]; congr 1; ring
  have key : ((ε : ℝ) * t) ^ (n + 1) * V * W ^ 2 = t ^ a * t ^ (3 * (n + a + 1)) := by
    rw [hrw, hW2, h4, hpow]; ring
  have hL : 2 * ((ε : ℝ) * t) ^ (n + 1) * V * W⁻¹ / (W⁻¹ * (1 - V * W)) ^ 3 =
      2 * (((ε : ℝ) * t) ^ (n + 1) * V * W ^ 2) / (1 - V * W) ^ 3 := by
    field_simp
  rw [hL, key]
  ring

/-- `𝓕(x_a) = 2t^a(Ξ − S_a)` (Lemma 1(ii) in the form `L(1/(x_a − s))`). -/
theorem cauchyF_node (hG : Good ε t) (a : ℕ) : cauchyF ε t (node ε t a) = 2 * t ^ a * ((XiR ε t) - S ε t a) := by
  have hsplit := (summable_psi_succ hG).sum_add_tsum_nat_add a
  unfold cauchyF
  simp_rw [(kern_node hG)]
  rw [tsum_mul_left, S_eq_sum_range, XiR, ← hsplit]
  ring

end LucasU.NonVan
