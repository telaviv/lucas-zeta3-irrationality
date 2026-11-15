/-
Generalised from lean_fibzeta FibZeta/Analytic/Jets.lean (ε = ±1, general t).
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/AnalyticDeterminant.lean and
lean/QZeta3/AnalyticEntry.lean (Apache-2.0, Lean formalisation by F. Solomon Admasu). Changes: roots
`q^{⌈u/3⌉}` of either sign; `|x − ϱ| ≤ 2|ϱ|` replaces `|x − r| ≤ r`, which costs a factor `2^j`.
-/
import LucasU.Analytic.Basis
import LucasU.Analytic.Weight

/-!
# Jet bounds for the triple-root basis (PROOF §2)

At a node `x = q^m` with `m ≥ R ≥ ⌈j/3⌉` (so `|x| ≤ |ϱ|` for every root `ϱ` of `B_j`):
`|B_j(x)| ≤ 2^j|q|^{a_j}`, `|θB_j(x)|, |θ²B_j(x)| ≤ j² 2^j |q|^{a_j} |q|^{m−R}`.
At `x = q^m` with `m < ⌈j/3⌉` the jets vanish (`tripleRoot_euler_vanish`).
-/

open Finset Polynomial

namespace LucasU.Analytic

/-- Scalar first-derivative step for adjoining one root. -/
theorem first_jet_product_step (x a ϱ c P n v d : ℝ)
    (ha : 0 ≤ a) (hc : a ≤ c) (hP : 0 ≤ P)
    (hxr : |x - ϱ| ≤ c) (hv : |v| ≤ P) (hd : |d| * a ≤ n * P) :
    |d * (x - ϱ) + v| * a ≤ (n + 1) * (P * c) := by
  have hc0 : 0 ≤ c := le_trans ha hc
  calc _ ≤ (|d| * |x - ϱ| + |v|) * a := by
        simpa only [abs_mul] using mul_le_mul_of_nonneg_right (abs_add_le (d * (x - ϱ)) v) ha
    _ ≤ (|d| * c + P) * a :=
        mul_le_mul_of_nonneg_right
          (add_le_add (mul_le_mul_of_nonneg_left hxr (abs_nonneg d)) hv) ha
    _ = (|d| * a) * c + P * a := by ring
    _ ≤ (n * P) * c + P * c :=
        add_le_add (mul_le_mul_of_nonneg_right hd hc0) (mul_le_mul_of_nonneg_left hc hP)
    _ = _ := by ring

/-- Scalar second-derivative step for adjoining one root. -/
theorem second_jet_product_step (x a ϱ c P n d e : ℝ)
    (ha : 0 ≤ a) (hc : a ≤ c) (hP : 0 ≤ P) (hn : 0 ≤ n)
    (hxr : |x - ϱ| ≤ c) (hd : |d| * a ≤ n * P)
    (he : |e| * a ^ 2 ≤ n * (n - 1) * P) :
    |e * (x - ϱ) + 2 * d| * a ^ 2 ≤ (n + 1) * n * (P * c) := by
  have hc0 : 0 ≤ c := le_trans ha hc
  have htri : |e * (x - ϱ) + 2 * d| ≤ |e| * |x - ϱ| + 2 * |d| := by
    simpa only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)] using
      abs_add_le (e * (x - ϱ)) (2 * d)
  calc _ ≤ (|e| * |x - ϱ| + 2 * |d|) * a ^ 2 := mul_le_mul_of_nonneg_right htri (sq_nonneg a)
    _ ≤ (|e| * c + 2 * |d|) * a ^ 2 :=
        mul_le_mul_of_nonneg_right
          (add_le_add (mul_le_mul_of_nonneg_left hxr (abs_nonneg e)) (le_refl _)) (sq_nonneg a)
    _ = (|e| * a ^ 2) * c + 2 * (|d| * a) * a := by ring
    _ ≤ (n * (n - 1) * P) * c + 2 * (n * P) * c := by
        apply add_le_add (mul_le_mul_of_nonneg_right he hc0)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num)) hc ha
          (mul_nonneg (by norm_num) (mul_nonneg hn hP))
    _ = _ := by ring

/-- Product-rule estimates for the triple-root polynomial at a point inside all its roots. -/
theorem tripleRoot_derivative_bounds {q x a : ℝ} (ha : 0 < a) (hxa : |x| ≤ a) (j : ℕ)
    (hroot : ∀ u ∈ Icc 1 j, a ≤ |q ^ ((u + 2) / 3)|) :
    |(tripleRootPoly q j).eval x| ≤ 2 ^ j * |q| ^ aj j ∧
      |(tripleRootPoly q j).derivative.eval x| * a ≤ (j : ℝ) * (2 ^ j * |q| ^ aj j) ∧
      |(tripleRootPoly q j).derivative.derivative.eval x| * a ^ 2 ≤
        (j : ℝ) * ((j : ℝ) - 1) * (2 ^ j * |q| ^ aj j) := by
  induction j with
  | zero => simp [tripleRootPoly, aj]
  | succ j ih =>
    have hr : a ≤ |q ^ ((j + 3) / 3)| := hroot (j + 1) (by simp)
    have hi := ih (fun u hu => hroot u (by
      rcases Finset.mem_Icc.mp hu with ⟨hu1, huj⟩
      exact Finset.mem_Icc.mpr ⟨hu1, by omega⟩))
    set P := 2 ^ j * |q| ^ aj j with hPdef
    set ϱ := q ^ ((j + 3) / 3) with hϱ
    set c := 2 * |ϱ| with hcdef
    set f := tripleRootPoly q j with hf
    have hP : 0 ≤ P := by positivity
    have hc : a ≤ c := by rw [hcdef]; linarith [abs_nonneg ϱ]
    have hxr : |x - ϱ| ≤ c := by
      calc |x - ϱ| ≤ |x| + |ϱ| := abs_sub _ _
        _ ≤ c := by rw [hcdef]; linarith
    have hpow : 2 ^ (j + 1) * |q| ^ aj (j + 1) = P * c := by
      rw [hPdef, hcdef, hϱ, abs_pow]
      unfold aj
      rw [Finset.sum_Icc_succ_top (by omega), pow_add, pow_succ]
      ring
    have he0 : (tripleRootPoly q (j + 1)).eval x = f.eval x * (x - ϱ) := by
      rw [tripleRootPoly_succ]
      simp [f, ϱ]
    have he1 : (tripleRootPoly q (j + 1)).derivative.eval x =
        f.derivative.eval x * (x - ϱ) + f.eval x := by
      rw [tripleRootPoly_succ]
      simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
        eval_add, eval_mul, eval_sub, eval_X, eval_C, mul_one, f, ϱ]
    have he2 : (tripleRootPoly q (j + 1)).derivative.derivative.eval x =
        f.derivative.derivative.eval x * (x - ϱ) + 2 * f.derivative.eval x := by
      rw [tripleRootPoly_succ]
      simp only [derivative_mul, derivative_add, derivative_sub, derivative_X, derivative_C,
        sub_zero, mul_one, eval_add, eval_mul, eval_sub, eval_X, eval_C, f, ϱ]
      ring
    have hb0 : |f.eval x * (x - ϱ)| ≤ P * c := by
      rw [abs_mul]
      exact mul_le_mul hi.1 hxr (abs_nonneg _) hP
    have hb1 := first_jet_product_step x a ϱ c P j (f.eval x) (f.derivative.eval x)
      ha.le hc hP hxr hi.1 hi.2.1
    have hb2 := second_jet_product_step x a ϱ c P j (f.derivative.eval x)
      (f.derivative.derivative.eval x) ha.le hc hP (Nat.cast_nonneg j) hxr hi.2.1 hi.2.2
    rw [he0, he1, he2, hpow]
    push_cast
    exact ⟨hb0, hb1, by simpa only [add_sub_cancel_right] using hb2⟩

theorem theta_polynomial (f : ℝ[X]) (x : ℝ) :
    theta (fun y => f.eval y) x = x * f.derivative.eval x := by
  rw [theta, Polynomial.deriv]

theorem theta_sq_polynomial (f : ℝ[X]) (x : ℝ) :
    theta (theta (fun y => f.eval y)) x =
      x * f.derivative.eval x + x ^ 2 * f.derivative.derivative.eval x := by
  have he : theta (fun y => f.eval y) = fun y => y * f.derivative.eval y :=
    funext (theta_polynomial f)
  have hd : HasDerivAt (fun y => y * f.derivative.eval y)
      (1 * f.derivative.eval x + x * f.derivative.derivative.eval x) x :=
    (hasDerivAt_id' x).mul (f.derivative.hasDerivAt x)
  rw [he, theta, hd.deriv]
  ring

theorem euler_jet_bounds_of_derivative_bounds (x a P n d e : ℝ)
    (ha : 0 < a) (hxa : |x| ≤ a) (hd : |d| * a ≤ n * P) (he : |e| * a ^ 2 ≤ n * (n - 1) * P) :
    |x * d| ≤ n * P * (|x| / a) ∧ |x * d + x ^ 2 * e| ≤ n ^ 2 * P * (|x| / a) := by
  have hx0 := abs_nonneg x
  constructor
  · rw [mul_div_assoc', le_div_iff₀ ha, abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hd hx0]
  · rw [mul_div_assoc', le_div_iff₀ ha]
    have htri : |x * d + x ^ 2 * e| ≤ |x| * |d| + |x| ^ 2 * |e| := by
      calc _ ≤ |x * d| + |x ^ 2 * e| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_pow]
    have hcompare : 0 ≤ (a - |x|) * |x| * |e| * a :=
      mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hxa) hx0) (abs_nonneg e)) ha.le
    have h₁ := mul_le_mul_of_nonneg_left hd hx0
    have h₂ := mul_le_mul_of_nonneg_left he hx0
    have h₃ := mul_le_mul_of_nonneg_right htri ha.le
    nlinarith only [hcompare, h₁, h₂, h₃]

/-- The jet bounds at a surviving node `q^m`, `m ≥ R ≥ ⌈i/3⌉`. -/
theorem tripleRoot_jets_common {q : ℝ} (hq : q ≠ 0) (hq1 : |q| ≤ 1)
    (i m R : ℕ) (hi : (i + 2) / 3 ≤ R) (hm : R ≤ m) :
    |(tripleRootPoly q i).eval (q ^ m)| ≤ 2 ^ i * |q| ^ aj i ∧
      |theta (fun x => (tripleRootPoly q i).eval x) (q ^ m)| ≤
        (i : ℝ) * (2 ^ i * |q| ^ aj i) * (|q| ^ m / |q| ^ R) ∧
      |theta (theta (fun x => (tripleRootPoly q i).eval x)) (q ^ m)| ≤
        (i : ℝ) ^ 2 * (2 ^ i * |q| ^ aj i) * (|q| ^ m / |q| ^ R) := by
  have hq0 : 0 < |q| := abs_pos.mpr hq
  have hxa : |q ^ m| ≤ |q| ^ R := by rw [abs_pow]; exact pow_le_pow_of_le_one hq0.le hq1 hm
  have h := tripleRoot_derivative_bounds (pow_pos hq0 R) hxa i
    (fun u hu => by
      rw [abs_pow]
      exact pow_le_pow_of_le_one hq0.le hq1 (by have := (Finset.mem_Icc.mp hu).2; omega))
  rw [theta_polynomial, theta_sq_polynomial]
  have he := euler_jet_bounds_of_derivative_bounds _ _ _ _ _ _ (pow_pos hq0 R) hxa h.2.1 h.2.2
  rw [abs_pow] at he
  exact ⟨h.1, he⟩

/-- Both Euler derivatives vanish at nodes preceding the surviving range. -/
theorem tripleRoot_euler_vanish (q : ℝ) {m j : ℕ} (hm : 1 ≤ m) (hj : m < (j + 2) / 3) :
    (tripleRootPoly q j).eval (q ^ m) = 0 ∧
      theta (fun x => (tripleRootPoly q j).eval x) (q ^ m) = 0 ∧
      theta (theta (fun x => (tripleRootPoly q j).eval x)) (q ^ m) = 0 := by
  obtain ⟨h₀, h₁, h₂⟩ := tripleRoot_jets_vanish q hm (by omega : 3 * m ≤ j)
  rw [theta_polynomial, theta_sq_polynomial, h₀, h₁, h₂]
  simp

end LucasU.Analytic
