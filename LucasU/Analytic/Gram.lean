/-
Generalised from lean_fibzeta FibZeta/Analytic/Gram.lean (ε = ±1, general t).
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/GramIdentity.lean (Apache-2.0,
Lean formalisation by F. Solomon Admasu). Changes: the functional `LucasU.Lfun` with signed
nodes; the Gram identity is stated for `LucasU.Delta ε t K` evaluated at `XiR ε t`.
-/
import LucasU.Analytic.Entry

/-!
# The real Gram determinant

* `numeratorFunctional ε t K : ℝ[X] →ₗ[ℝ] ℝ`, `P ↦ L(P/D_K)`;
* `gramR ε t K = [L(s^{i+j}/D_K)]` and `Delta_eval_eq_det : Δ_K(Ξ) = det gramR` (PROOF §1).
-/

open Polynomial Finset Filter Topology

namespace LucasU.Analytic

variable {ε : ℤ} {t : ℝ} [hG : Fact (Good ε t)]

theorem DK_ne_zero {y : ℝ} (hy : |y| < 1) (K : ℕ) : DK ε t K y ≠ 0 := by
  rw [DK]
  apply prod_ne_zero_iff.mpr
  intro a _
  have : |wpar ε t ^ a * y| < 1 := by
    rw [abs_mul]
    calc |wpar ε t ^ a| * |y| ≤ 1 * |y| :=
          mul_le_mul_of_nonneg_right (abs_w_pow_le_one a) (abs_nonneg y)
      _ < 1 := by rw [one_mul]; exact hy
  have := (abs_lt.mp this).2
  linarith

omit hG in
theorem contDiffAt_DK (K : ℕ) (y : ℝ) : ContDiffAt ℝ 2 (DK ε t K) y := by
  have : DK ε t K = fun s => ∏ a ∈ Icc 1 K, (1 - wpar ε t ^ a * s) := rfl
  rw [this]
  exact contDiffAt_prod fun a _ => contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)

theorem reg_frac_DK (K j : ℕ) : Reg (fun y => y ^ j / DK ε t K y) := fun x hx =>
  (contDiffAt_id.pow j).div (contDiffAt_DK K x) (DK_ne_zero hx K)

omit hG in
theorem poly_div_DK_eq_sum (K : ℕ) (P : ℝ[X]) :
    (fun y : ℝ => P.eval y / DK ε t K y) =
      (fun y => ∑ j ∈ P.support, P.coeff j * (y ^ j / DK ε t K y)) := by
  funext y
  rw [eval_eq_sum, Polynomial.sum_def, Finset.sum_div]
  apply sum_congr rfl
  intro j _
  ring

theorem reg_poly_div_DK (K : ℕ) (P : ℝ[X]) : Reg (fun y => P.eval y / DK ε t K y) := by
  rw [poly_div_DK_eq_sum]
  exact reg_sum _ _ fun j _ => reg_const_mul (reg_frac_DK K j) _

theorem hasL_poly_div_DK (K : ℕ) (P : ℝ[X]) :
    HasSum (Lterm ε t (fun y => P.eval y / DK ε t K y))
      (∑ j ∈ P.support, P.coeff j * (nrm ε t K * (mConst ε t K j + XiR ε t * mLin ε t K j))) := by
  rw [poly_div_DK_eq_sum]
  exact hasL_sum _ _ _ (fun j _ => reg_const_mul (reg_frac_DK K j) _)
    (fun j _ => hasL_const_mul (reg_frac_DK K j) (hasL_fraction_DK K j) _)

theorem summable_poly_div_DK (K : ℕ) (P : ℝ[X]) :
    Summable (Lterm ε t (fun y => P.eval y / DK ε t K y)) :=
  (hasL_poly_div_DK K P).summable

theorem Lfun_poly_div_DK_add (K : ℕ) (P Q : ℝ[X]) :
    Lfun ε t (fun y => (P + Q).eval y / DK ε t K y) =
      Lfun ε t (fun y => P.eval y / DK ε t K y) + Lfun ε t (fun y => Q.eval y / DK ε t K y) := by
  have hs := hasL_add (reg_poly_div_DK (ε := ε) (t := t) K P) (reg_poly_div_DK K Q)
    (summable_poly_div_DK K P).hasSum (summable_poly_div_DK K Q).hasSum
  have he : (fun y => (P + Q).eval y / DK ε t K y) =
      (fun y => P.eval y / DK ε t K y + Q.eval y / DK ε t K y) := by
    funext y; rw [eval_add, add_div]
  rw [he]
  exact hs.tsum_eq

theorem Lfun_poly_div_DK_smul (K : ℕ) (P : ℝ[X]) (c : ℝ) :
    Lfun ε t (fun y => (c • P).eval y / DK ε t K y) =
      c * Lfun ε t (fun y => P.eval y / DK ε t K y) := by
  have hs := hasL_const_mul (reg_poly_div_DK (ε := ε) (t := t) K P)
    (summable_poly_div_DK K P).hasSum c
  have he : (fun y => (c • P).eval y / DK ε t K y) = (fun y => c * (P.eval y / DK ε t K y)) := by
    funext y; rw [eval_smul, smul_eq_mul]; ring
  rw [he]
  exact hs.tsum_eq

variable (ε t) in
/-- `P ↦ L(P/D_K)` as a linear map. -/
noncomputable def numeratorFunctional (K : ℕ) : ℝ[X] →ₗ[ℝ] ℝ where
  toFun P := Lfun ε t (fun y => P.eval y / DK ε t K y)
  map_add' := Lfun_poly_div_DK_add K
  map_smul' c P := by
    simpa only [smul_eq_mul, RingHom.id_apply] using Lfun_poly_div_DK_smul K P c

/-- The real Gram matrix `[L(s^{i+j}/D_K)]`. -/
noncomputable def gramR (ε : ℤ) (t : ℝ) (K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  Matrix.of fun i j => Lfun ε t (fun y => y ^ (i.val + j.val) / DK ε t K y)

/-- `Δ_K(Ξ)` is the real Gram determinant. -/
theorem Delta_eval_eq_det (K : ℕ) : (Delta ε t K).eval (XiR ε t) = (gramR ε t K).det := by
  unfold Delta
  rw [← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, map_add, map_mul, coe_evalRingHom, hankelLin, hankelConst,
    Matrix.of_apply, gramR]
  rw [show Lfun ε t (fun y => y ^ (i.val + j.val) / DK ε t K y) = _ from
    (hasL_fraction_DK K (i.val + j.val)).tsum_eq]
  simp only [eval_mul, eval_X, eval_C]
  ring

end LucasU.Analytic
