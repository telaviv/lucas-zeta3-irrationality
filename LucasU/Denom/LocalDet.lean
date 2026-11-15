/-
Generalised from lean_fibzeta FibZeta/Denom/LocalDet.lean (ε = ±1, general t).
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/LocalDeterminants.lean and
lean/QZeta3/LocalGramBounds.lean (`det_weighted_eq`) (Apache-2.0, Lean formalisation by F. Solomon
Admasu). Changes: only the construction-independent determinant tools are kept; namespace renamed.
-/
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Basic

/-!
# Weighted determinants and the rank correction

* `det_weighted_mem_subring`: entrywise row/column weights clear the determinant by the sum of the
  weights (the scaling `π^{⌈w_j⌉}`, `π^{⌊w_j⌋}` of Proposition 3.2).
* `C_pow_mul_det_add_inv_mem_subring`: a simple pole `π⁻¹ B` with `rank B ≤ r` costs at most `r`
  in the determinant (the multilinear expansion of the α-root bullet of Proposition 3.2).
-/

open Finset Matrix Polynomial

namespace LucasU.Denom

section Subring
variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

theorem det_mem_subring (S : Subring R) (M : Matrix ι ι R)
    (hM : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  apply S.sum_mem
  intro σ _
  have hp : (∏ i, M (σ i) i) ∈ S := S.prod_mem (fun i _ => hM (σ i) i)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simpa [h] using hp
  · simpa [h] using S.neg_mem hp

/-- The determinant of a matrix after independent row and column scalings. -/
theorem det_weighted_eq (t : R) (M : Matrix ι ι R) (r c : ι → ℕ) :
    (Matrix.of fun i j => t ^ (r i + c j) * M i j).det =
      t ^ ((∑ i, r i) + (∑ i, c i)) * M.det := by
  have hA : (Matrix.of fun i j => t ^ (r i + c j) * M i j) =
      Matrix.of fun i j => t ^ (r i) * (Matrix.of fun k l => t ^ (c l) * M k l) i j := by
    ext i j
    simp only [Matrix.of_apply, pow_add]
    ring
  rw [hA, Matrix.det_mul_column, Matrix.det_mul_row,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, pow_add]
  ring

/-- Full row expansion, with the scalar extracted for the selected rows. -/
theorem det_add_smul_eq_sum (A B : Matrix ι ι R) (t : R) :
    (A + t • B).det = ∑ s : Finset ι, t ^ s.card * Matrix.det (s.piecewise B A) := by
  have he := (Matrix.detRowAlternating : (ι → R) [⋀^ι]→ₗ[R] R).map_add_univ (t • B) A
  change (t • B + A).det = _ at he
  rw [add_comm] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro s _
  have hM : s.piecewise (t • B) A =
      fun i => (if i ∈ s then t else 1) • (s.piecewise B A) i := by
    funext i j
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  change Matrix.detRowAlternating _ = _
  rw [hM, AlternatingMap.map_smul_univ]
  simp only [smul_eq_mul]
  congr 1
  simp

end Subring

section Field
variable {R ι : Type*} [Field R] [Fintype ι] [DecidableEq ι]

/-- The rank correction works coefficientwise in a formal target variable. -/
theorem det_piecewise_polynomial_eq_zero_of_rank_lt
    (A : Matrix ι ι R[X]) (B : Matrix ι ι R) (s : Finset ι)
    (hs : B.rank < s.card) : Matrix.det (s.piecewise (B.map Polynomial.C) A) = 0 := by
  classical
  by_contra hne
  have hli0 := (Matrix.linearIndependent_rows_of_det_ne_zero hne).comp
    (fun i : s => (i : ι)) Subtype.val_injective
  have hliP : LinearIndependent R[X] (fun i : s => (B.map Polynomial.C) i) := by
    simpa [Function.comp_def, Finset.piecewise] using hli0
  have hliR := hliP.restrict_scalars' R
  let φ : (ι → R) →ₗ[R] (ι → R[X]) := LinearMap.pi
    (fun j => Polynomial.CAlgHom.toLinearMap.comp (LinearMap.proj j))
  have hli : LinearIndependent R (fun i : s => B i) := by
    apply LinearIndependent.of_comp φ
    exact hliR
  have hspan : Submodule.span R (Set.range (fun i : s => B i)) ≤
      Submodule.span R (Set.range (fun i => B i)) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨i, rfl⟩
  have hdim := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli, Fintype.card_coe] at hdim
  have hrank : Module.finrank R (Submodule.span R (Set.range (fun i => B i))) = B.rank :=
    (Matrix.rank_eq_finrank_span_cols B.transpose).symm.trans (Matrix.rank_transpose B)
  rw [hrank] at hdim
  omega

/-- Polynomial-valued low-rank pole correction.  The subring `T` may be the polynomials whose
coefficients are regular at a fixed point. -/
theorem C_pow_mul_det_add_inv_mem_subring (T : Subring R[X]) (τ : R) (hτ : τ ≠ 0)
    (hτT : Polynomial.C τ ∈ T) (A : Matrix ι ι R[X]) (B : Matrix ι ι R)
    (hA : ∀ i j, A i j ∈ T) (hB : ∀ i j, Polynomial.C (B i j) ∈ T)
    (r : ℕ) (hr : B.rank ≤ r) :
    (Polynomial.C τ) ^ r * (A + (Polynomial.C τ⁻¹) • B.map Polynomial.C).det ∈ T := by
  rw [det_add_smul_eq_sum, Finset.mul_sum]
  apply T.sum_mem
  intro s _
  by_cases hs : s.card ≤ r
  · have he : (Polynomial.C τ) ^ r * (Polynomial.C τ⁻¹) ^ s.card =
        (Polynomial.C τ) ^ (r - s.card) := by
      rw [← map_pow, ← map_pow, ← map_mul, ← map_pow]
      congr 1
      rw [inv_pow, ← div_eq_mul_inv]
      nth_rw 1 [← Nat.sub_add_cancel hs]
      rw [pow_add]
      field_simp
    rw [← mul_assoc, he]
    apply T.mul_mem (T.pow_mem hτT _)
    apply det_mem_subring
    intro i j
    by_cases hi : i ∈ s <;> simp only [Finset.piecewise, hi, ite_true, ite_false]
    · exact hB i j
    · exact hA i j
  · rw [det_piecewise_polynomial_eq_zero_of_rank_lt A B s (by omega), mul_zero, mul_zero]
    exact T.zero_mem

end Field

end LucasU.Denom
