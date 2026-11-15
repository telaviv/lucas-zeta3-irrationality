-- Generalised from lean_fibzeta FibZeta/Cost/Cyclo.lean (ε = ±1, general t).
/-
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/CyclotomicBounds.lean (Apache-2.0, Lean
formalisation by F. Solomon Admasu). Changes: the integer point `p` is replaced by the pair `t`, `ε/t` (norm of
`Φ_d(t)` in a real quadratic field when `t = 1/α`), with the geometric error bound at ratio `t ≤ 2/3`.
-/
import LucasU.Main

/-!
# Lemma 3.5: size of `N(Φ_d(t)) = Φ_d(t) Φ_d(ε/t)`

For `ε = ±1` and `0 < t ≤ φ⁻¹`:
`log |Φ_d(t)| + log |Φ_d(ε/t)| ≤ φ(d) log t⁻¹ + 12` for every `d ≥ 1`.

Proof: `∑_{a ∣ n} log|Φ_a(x)| = log|x^n − 1|`; at `x = t` and `x = ε/t` the sum of the two minus `n log t⁻¹` is
`G(n) = log(1 − tⁿ) + log|1 − (ε t)ⁿ|`, `|G(n)| ≤ 6 tⁿ` (as `tⁿ ≤ t ≤ 2/3`); Möbius inversion gives
`|F(d)| ≤ ∑_{a ∣ d} 6 tᵃ ≤ 6 t/(1 − t) ≤ 12`.  (PROOF_U §3.3: `|F(d)| ≤ 2E₁(t)`; here the cruder uniform
bound `12` suffices.)
-/

open Polynomial Finset
open scoped ArithmeticFunction.Moebius

namespace LucasU.Cost

variable {ε : ℤ} {t : ℝ}

theorem inv_gold_le : Real.goldenRatio⁻¹ ≤ 2 / 3 := by
  have h5 : (2 : ℝ) ≤ √5 := by
    rw [show (2 : ℝ) = √(2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hg : (3 / 2 : ℝ) ≤ Real.goldenRatio := by
    rw [Real.goldenRatio]; linarith
  rw [inv_le_comm₀ Real.goldenRatio_pos (by norm_num)]
  linarith

theorem good_eps (h : Good ε t) : ε = 1 ∨ ε = -1 := h.1

theorem good_pos (h : Good ε t) : 0 < t := h.2.1

theorem good_le (h : Good ε t) : t ≤ 2 / 3 := h.2.2.trans inv_gold_le

theorem good_lt_one (h : Good ε t) : t < 1 := by linarith [(good_le h)]

theorem good_eps_sq (h : Good ε t) : (ε : ℝ) ^ 2 = 1 := by
  rcases (good_eps h) with rfl | rfl <;> norm_num

theorem good_abs_eps (h : Good ε t) : |(ε : ℝ)| = 1 := by
  rcases (good_eps h) with rfl | rfl <;> norm_num

theorem good_log_pos (h : Good ε t) : 0 < Real.log t⁻¹ :=
  Real.log_pos (one_lt_inv_iff₀.mpr ⟨(good_pos h), (good_lt_one h)⟩)

theorem abs_log_one_sub_le {v : ℝ} (hv : |v| ≤ 2 / 3) : |Real.log (|1 - v|)| ≤ 3 * |v| := by
  have hv1 : v ≤ 2 / 3 := le_trans (le_abs_self v) hv
  have h1 : 0 < 1 - v := by linarith
  rw [abs_of_pos h1]
  have habs := abs_nonneg v
  have hle := le_abs_self v
  have hge := neg_abs_le v
  refine abs_le.mpr ⟨?_, ?_⟩
  · have hlow := Real.one_sub_inv_le_log_of_pos h1
    have hinv : (1 - v)⁻¹ ≤ 1 + 3 * |v| := by
      rw [inv_eq_one_div, div_le_iff₀ h1]
      nlinarith [mul_le_mul_of_nonneg_left hv1 habs]
    linarith
  · have := Real.log_le_sub_one_of_pos h1
    linarith

theorem cyc_eval_ne_zero {x : ℝ} (hx : ∀ m : ℕ, 0 < m → x ^ m ≠ 1) {a : ℕ} (ha : 0 < a) :
    (cyclotomic a ℝ).eval x ≠ 0 := by
  intro h
  have : NeZero a := ⟨ha.ne'⟩
  have hroot : (cyclotomic a ℝ).IsRoot x := h
  rw [isRoot_cyclotomic_iff] at hroot
  exact hx a ha hroot.pow_eq_one

theorem sum_log_cyc {x : ℝ} (hx : ∀ m : ℕ, 0 < m → x ^ m ≠ 1) {n : ℕ} (hn : 0 < n) :
    ∑ a ∈ n.divisors, Real.log |(cyclotomic a ℝ).eval x| = Real.log |x ^ n - 1| := by
  rw [← Real.log_prod (fun a ha => abs_ne_zero.mpr
    (cyc_eval_ne_zero hx (Nat.pos_of_mem_divisors ha))), ← Finset.abs_prod, ← eval_prod,
    prod_cyclotomic_eq_X_pow_sub_one hn]
  simp

theorem good_not_root (h : Good ε t) : ∀ m : ℕ, 0 < m → t ^ m ≠ 1 := by
  apply pow_ne_one_of_abs_ne_one
  rw [abs_of_pos (good_pos h)]; exact (good_lt_one h).ne

theorem good_abs_conj (h : Good ε t) : |(ε : ℝ) / t| = t⁻¹ := by
  rw [abs_div, (good_abs_eps h), abs_of_pos (good_pos h), one_div]

theorem good_conj_not_root (h : Good ε t) : ∀ m : ℕ, 0 < m → ((ε : ℝ) / t) ^ m ≠ 1 := by
  apply pow_ne_one_of_abs_ne_one
  rw [(good_abs_conj h)]; exact (one_lt_inv_iff₀.mpr ⟨(good_pos h), (good_lt_one h)⟩).ne'

/-- The cyclotomic error `F(a) = log|Φ_a(t)| + log|Φ_a(ε/t)| − φ(a) log t⁻¹`. -/
noncomputable def cycErr (ε : ℤ) (t : ℝ) (a : ℕ) : ℝ :=
  Real.log |(cyclotomic a ℝ).eval t| + Real.log |(cyclotomic a ℝ).eval ((ε : ℝ) / t)| -
    (Nat.totient a : ℝ) * Real.log t⁻¹

/-- `G(n) = log|1 − tⁿ| + log|1 − (ε t)ⁿ|`. -/
noncomputable def cycG (ε : ℤ) (t : ℝ) (n : ℕ) : ℝ :=
  Real.log |1 - t ^ n| + Real.log |1 - ((ε : ℝ) * t) ^ n|

theorem sum_cycErr (h : Good ε t) {n : ℕ} (hn : 0 < n) :
    ∑ a ∈ n.divisors, cycErr ε t a = cycG ε t n := by
  unfold cycErr cycG
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, sum_log_cyc (good_not_root h) hn,
    sum_log_cyc (good_conj_not_root h) hn]
  have hs : (∑ d ∈ n.divisors, (Nat.totient d : ℝ)) = n := by exact_mod_cast Nat.sum_totient n
  rw [hs]
  have ht0 := (good_pos h).ne'
  have h1 : |t ^ n - 1| = |1 - t ^ n| := abs_sub_comm _ _
  have h2 : ((ε : ℝ) / t) ^ n - 1 = ((ε : ℝ) / t) ^ n * (1 - ((ε : ℝ) * t) ^ n) := by
    have : ((ε : ℝ) / t) ^ n * ((ε : ℝ) * t) ^ n = 1 := by
      rw [← mul_pow]
      have : (ε : ℝ) / t * ((ε : ℝ) * t) = 1 := by
        field_simp; exact good_eps_sq h
      rw [this, one_pow]
    linear_combination this
  have hne : ((ε : ℝ) * t) ^ n ≠ 1 := by
    intro h3
    have := congrArg abs h3
    rw [abs_one, abs_pow, abs_mul, (good_abs_eps h), one_mul, abs_of_pos (good_pos h)] at this
    exact (good_not_root h) n hn this
  rw [h1, h2, abs_mul, Real.log_mul, abs_pow, (good_abs_conj h), Real.log_pow]
  · ring
  · exact abs_ne_zero.mpr (pow_ne_zero _ (div_ne_zero (by rcases (good_eps h) with rfl | rfl <;> norm_num)
      ht0))
  · exact abs_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm hne))

theorem abs_cycG_le (h : Good ε t) {n : ℕ} (hn : 0 < n) : |cycG ε t n| ≤ 6 * t ^ n := by
  have hp : 0 ≤ t ^ n := pow_nonneg (good_pos h).le n
  have hle : t ^ n ≤ 2 / 3 :=
    le_trans (pow_le_of_le_one (good_pos h).le (good_lt_one h).le hn.ne') (good_le h)
  have a1 : |t ^ n| = t ^ n := abs_of_nonneg hp
  have a2 : |((ε : ℝ) * t) ^ n| = t ^ n := by
    rw [abs_pow, abs_mul, (good_abs_eps h), one_mul, abs_of_pos (good_pos h)]
  have e1 := abs_log_one_sub_le (v := t ^ n) (by rw [a1]; exact hle)
  have e2 := abs_log_one_sub_le (v := ((ε : ℝ) * t) ^ n) (by rw [a2]; exact hle)
  rw [a1] at e1; rw [a2] at e2
  unfold cycG
  calc _ ≤ |Real.log (|1 - t ^ n|)| + |Real.log (|1 - ((ε : ℝ) * t) ^ n|)| := abs_add_le _ _
    _ ≤ _ := by linarith

theorem sum_t_pow_le (h : Good ε t) (d : ℕ) : ∑ a ∈ Icc 1 d, t ^ a ≤ 2 := by
  have h' := geom_sum_Ico_le_of_lt_one (m := 1) (n := d + 1) (good_pos h).le (good_lt_one h)
  have hI : Icc 1 d = Ico 1 (d + 1) := by ext; simp
  rw [hI]
  refine h'.trans ?_
  rw [pow_one, div_le_iff₀ (by linarith [(good_lt_one h)])]
  linarith [(good_le h)]

theorem abs_cycErr_le (h : Good ε t) {d : ℕ} (hd : 0 < d) : |cycErr ε t d| ≤ 12 := by
  have hm := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
    (fun n hn => sum_cycErr h hn)) d hd
  rw [← hm, Nat.sum_divisorsAntidiagonal' (fun a b => (μ a : ℝ) * cycG ε t b)]
  calc |∑ a ∈ d.divisors, (μ (d / a) : ℝ) * cycG ε t a|
      ≤ ∑ a ∈ d.divisors, |(μ (d / a) : ℝ) * cycG ε t a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ d.divisors, 6 * t ^ a := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul]
      have hmu : |(μ (d / a) : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d / a))
      calc _ ≤ 1 * |cycG ε t a| := mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact abs_cycG_le h (Nat.pos_of_mem_divisors ha)
    _ ≤ ∑ a ∈ Icc 1 d, 6 * t ^ a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,
          Nat.le_of_dvd hd (Nat.dvd_of_mem_divisors ha)⟩
      · intro a _ _; have := (good_pos h); positivity
    _ ≤ 12 := by rw [← Finset.mul_sum]; linarith [sum_t_pow_le h d]

/-- **Lemma 3.5** (upper half, constant 12, uniform in `0 < t ≤ φ⁻¹` and `ε = ±1`). -/
theorem log_norm_cyc_le (h : Good ε t) {d : ℕ} (hd : 0 < d) :
    Real.log |(cyclotomic d ℝ).eval t| + Real.log |(cyclotomic d ℝ).eval ((ε : ℝ) / t)| ≤
      (Nat.totient d : ℝ) * Real.log t⁻¹ + 12 := by
  have := (abs_le.mp (abs_cycErr_le h hd)).2
  unfold cycErr at this
  linarith

end LucasU.Cost
