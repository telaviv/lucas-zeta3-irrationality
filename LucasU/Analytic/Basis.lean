/-
Generalised from lean_fibzeta FibZeta/Analytic/Basis.lean (ε = ±1, general t).
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/AnalyticDeterminant.lean and
lean/QZeta3/GramBasis.lean (Apache-2.0, Lean formalisation by F. Solomon Admasu). Changes: namespace;
the Gram matrix of `LucasU.Lfun` over `LucasU.DK`; the algebraic lemmas are unchanged.
-/
import LucasU.Analytic.Gram
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The triple-root basis (PROOF §2)

`B_j(s) = ∏_{u=1}^{j} (s − q^{⌈u/3⌉})`; the change of basis from monomials is unitriangular, so
`det[L(B_iB_j/D_K)] = det[L(s^{i+j}/D_K)]` (`det_tripleRootGram`).  Also the generic determinant
estimate `abs_det_le_of_scaled_entries`.
-/

open Finset Matrix Polynomial

namespace LucasU.Analytic

variable {ε : ℤ} {t : ℝ}

/-- The monic basis with three repeated roots at each successive node. -/
noncomputable def tripleRootPoly (q : ℝ) (j : ℕ) : ℝ[X] :=
  ∏ u ∈ Icc 1 j, (X - C (q ^ ((u + 2) / 3)))

theorem tripleRootPoly_monic (q : ℝ) (j : ℕ) : (tripleRootPoly q j).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem tripleRootPoly_natDegree (q : ℝ) (j : ℕ) : (tripleRootPoly q j).natDegree = j := by
  unfold tripleRootPoly
  rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _,
    Finset.sum_congr rfl fun u _ => natDegree_X_sub_C _]
  simp

theorem tripleRootPoly_succ (q : ℝ) (j : ℕ) :
    tripleRootPoly q (j + 1) = tripleRootPoly q j * (X - C (q ^ ((j + 3) / 3))) := by
  unfold tripleRootPoly
  rw [Finset.prod_Icc_succ_top (by omega)]

theorem tripleRootPoly_dvd (q : ℝ) {a b : ℕ} (hab : a ≤ b) :
    tripleRootPoly q a ∣ tripleRootPoly q b := by
  induction b, hab using Nat.le_induction with
  | base => exact dvd_refl _
  | succ b _ ih =>
    rw [tripleRootPoly_succ]
    exact dvd_mul_of_dvd_left ih _

theorem tripleRootPoly_block (q : ℝ) (n : ℕ) :
    tripleRootPoly q (3 * (n + 1)) = tripleRootPoly q (3 * n) * (X - C (q ^ (n + 1))) ^ 3 := by
  rw [show 3 * (n + 1) = ((3 * n + 1) + 1) + 1 by omega]
  rw [tripleRootPoly_succ, tripleRootPoly_succ, tripleRootPoly_succ]
  have h₁ : (3 * n + 3) / 3 = n + 1 := by omega
  have h₂ : (3 * n + 1 + 3) / 3 = n + 1 := by omega
  have h₃ : (3 * n + 1 + 1 + 3) / 3 = n + 1 := by omega
  rw [h₁, h₂, h₃]
  ring

theorem tripleRoot_dvd (q : ℝ) {m j : ℕ} (hm : 1 ≤ m) (hj : 3 * m ≤ j) :
    (X - C (q ^ m)) ^ 3 ∣ tripleRootPoly q j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  apply dvd_trans _ (tripleRootPoly_dvd q hj)
  rw [tripleRootPoly_block]
  exact dvd_mul_left _ _

/-- The three ordinary jets vanish at every completed node. -/
theorem tripleRoot_jets_vanish (q : ℝ) {m j : ℕ} (hm : 1 ≤ m) (hj : 3 * m ≤ j) :
    (tripleRootPoly q j).eval (q ^ m) = 0 ∧
      (tripleRootPoly q j).derivative.eval (q ^ m) = 0 ∧
      (tripleRootPoly q j).derivative.derivative.eval (q ^ m) = 0 := by
  obtain ⟨f, hf⟩ := tripleRoot_dvd q hm hj
  rw [hf]
  simp [derivative_mul, derivative_pow]

/-- Coefficient matrix converting monomials into the triple-root basis. -/
noncomputable def tripleRootChange (q : ℝ) (K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  fun i j => (tripleRootPoly q i.val).coeff j.val

theorem det_tripleRootChange (q : ℝ) (K : ℕ) : (tripleRootChange q K).det = 1 := by
  have h := Matrix.det_matrixOfPolynomials (fun i : Fin K => tripleRootPoly q i.val)
    (fun i => tripleRootPoly_natDegree q i.val) (fun i => tripleRootPoly_monic q i.val)
  convert h using 1
  exact (Matrix.det_transpose _).symm

/-- Extract positive row and column weights before the factorial determinant estimate. -/
theorem abs_det_le_of_scaled_entries {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (r : n → ℝ) (M : ℝ) (hr : ∀ i, 0 < r i)
    (hA : ∀ i j, |A i j| ≤ M * r i * r j) :
    |A.det| ≤ (Fintype.card n).factorial * M ^ Fintype.card n * (∏ i, r i) ^ 2 := by
  let B : Matrix n n ℝ := fun i j => A i j / (r i * r j)
  have hB : ∀ i j, |B i j| ≤ M := by
    intro i j
    dsimp [B]
    rw [abs_div, abs_of_pos (mul_pos (hr i) (hr j)), div_le_iff₀ (mul_pos (hr i) (hr j))]
    simpa only [mul_assoc] using hA i j
  have hdet : |B.det| ≤ (Fintype.card n).factorial * M ^ Fintype.card n := by
    simpa only [nsmul_eq_mul, AbsoluteValue.abs_apply] using
      (Matrix.det_le (abv := AbsoluteValue.abs) hB)
  have hfactor : A = diagonal r * B * diagonal r := by
    ext i j
    calc A i j = r i * B i j * r j := by
          dsimp [B]
          field_simp [(hr i).ne', (hr j).ne']
      _ = (diagonal r * B * diagonal r) i j := by
          rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hrprod : 0 < ∏ i, r i := Finset.prod_pos fun i _ => hr i
  rw [hfactor, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal,
    abs_mul, abs_mul, abs_of_pos hrprod]
  nlinarith [sq_nonneg (∏ i, r i), mul_le_mul_of_nonneg_right hdet (sq_nonneg (∏ i, r i))]

theorem det_congruence_of_det_one {n : Type*} [Fintype n] [DecidableEq n]
    (A U : Matrix n n ℝ) (hU : U.det = 1) : (U * A * U.transpose).det = A.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hU]
  ring

/-- The Gram matrix in the triple-root basis. -/
noncomputable def tripleRootGram (ε : ℤ) (t : ℝ) (q : ℝ) (K : ℕ) : Matrix (Fin K) (Fin K) ℝ :=
  fun i j => Lfun ε t (fun x =>
    (tripleRootPoly q i.val).eval x * (tripleRootPoly q j.val).eval x / DK ε t K x)

theorem tripleRootPoly_expansion (q : ℝ) {K : ℕ} (i : Fin K) :
    tripleRootPoly q i.val = ∑ j : Fin K, (tripleRootChange q K i j) • (X : ℝ[X]) ^ j.val := by
  have h := (tripleRootPoly q i.val).as_sum_range_C_mul_X_pow'
    (show (tripleRootPoly q i.val).natDegree < K by rw [tripleRootPoly_natDegree]; exact i.isLt)
  rw [← Fin.sum_univ_eq_sum_range _ K] at h
  simpa only [tripleRootChange, smul_eq_C_mul] using h

theorem tripleRootGram_eq_congruence [Fact (Good ε t)] (q : ℝ) (K : ℕ) :
    tripleRootGram ε t q K = tripleRootChange q K * gramR ε t K * (tripleRootChange q K).transpose := by
  let L := numeratorFunctional ε t K
  have hmono (i j : Fin K) : L ((X : ℝ[X]) ^ (i.val + j.val)) = gramR ε t K i j := by
    simp only [L, numeratorFunctional, LinearMap.coe_mk, AddHom.coe_mk, gramR,
      Matrix.of_apply, eval_pow, eval_X]
  ext i j
  have hid : tripleRootGram ε t q K i j = L (tripleRootPoly q i.val * tripleRootPoly q j.val) := by
    simp only [tripleRootGram, L, numeratorFunctional, LinearMap.coe_mk, AddHom.coe_mk, eval_mul]
  rw [hid, tripleRootPoly_expansion _ i, tripleRootPoly_expansion _ j]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    ← pow_add, map_sum, map_smul, smul_eq_mul, hmono]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro r _
  ring

theorem det_tripleRootGram [Fact (Good ε t)] (q : ℝ) (K : ℕ) : (tripleRootGram ε t q K).det = (gramR ε t K).det := by
  rw [tripleRootGram_eq_congruence]
  exact det_congruence_of_det_one _ _ (det_tripleRootChange _ _)

theorem summable_tripleRootGram_entry [Fact (Good ε t)] (q : ℝ) (K i j : ℕ) :
    Summable (Lterm ε t (fun x =>
      (tripleRootPoly q i).eval x * (tripleRootPoly q j).eval x / DK ε t K x)) := by
  simpa only [eval_mul] using
    summable_poly_div_DK (ε := ε) (t := t) K (tripleRootPoly q i * tripleRootPoly q j)

end LucasU.Analytic
