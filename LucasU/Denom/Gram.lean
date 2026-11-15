/-
Generalised from lean_fibzeta FibZeta/Denom/Gram.lean (ε = ±1, general t).
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/GenericGram.lean (Apache-2.0,
Lean formalisation by F. Solomon Admasu). Changes: the moment functional is that of the Fibonacci
construction (`L_X(1/(s − x_a)) = −2τ^a (X − S_a)`); the pole part is named `properPart`.
-/
import LucasU.Denom.Localization
import Mathlib.Algebra.Polynomial.Eval.SMul

/-!
# The moment functional on polynomials and the Gram congruence

`momentPolynomial ε τ K f = L_X(f/F_K) ∈ 𝕜[X]` for any polynomial `f` (PROOF §1: polynomial quotient
plus partial fractions).  For a family `G` of `K` polynomials of degree `< K`, the Gram matrix
`[nrm · L_X(G_i G_j / F_K)]` is congruent to the Hankel matrix of `Delta`
(`det_normalizedGram`): this is the change of basis of Proposition 3.2.
-/

open Polynomial Finset Matrix

namespace LucasU.Denom

variable {𝕜 : Type*} [Field 𝕜] {ε : ℤ}

noncomputable def LpolyLinear (ε : ℤ) (τ : 𝕜) : 𝕜[X] →ₗ[𝕜] 𝕜 :=
  Polynomial.lsum (fun j => LinearMap.mulRight 𝕜 (nu ε τ j))

@[simp] theorem LpolyLinear_apply (τ : 𝕜) (f : 𝕜[X]) : LpolyLinear ε τ f = Lpoly ε τ f := rfl

theorem Lpoly_add (τ : 𝕜) (f g : 𝕜[X]) : Lpoly ε τ (f + g) = Lpoly ε τ f + Lpoly ε τ g :=
  (LpolyLinear ε τ).map_add f g

theorem Lpoly_smul (τ c : 𝕜) (f : 𝕜[X]) : Lpoly ε τ (c • f) = c * Lpoly ε τ f :=
  (LpolyLinear ε τ).map_smul c f

/-- The pole part `−∑_a L_X(A_a/(s − x_a))`: the residue of `f/F` at `x_a` times
`2τ^a (X − S_a)`. -/
noncomputable def properPart (ε : ℤ) (τ : 𝕜) (K : ℕ) (f : 𝕜[X]) : 𝕜[X] :=
  ∑ a ∈ Icc 1 K, C (f.eval (node ε τ a) * (2 * τ ^ a) / (derivative (F ε τ K)).eval (node ε τ a)) *
    (X - C (S ε τ a))

/-- `L_X(f/F_K)` (polynomial quotient plus partial fractions). -/
noncomputable def momentPolynomial (ε : ℤ) (τ : 𝕜) (K : ℕ) (f : 𝕜[X]) : 𝕜[X] :=
  C (Lpoly ε τ (f /ₘ F ε τ K)) - properPart ε τ K f

noncomputable def momentFunctional (ε : ℤ) (τ : 𝕜) (K : ℕ) : 𝕜[X] →ₗ[𝕜] 𝕜[X] where
  toFun := momentPolynomial ε τ K
  map_add' f g := by
    simp only [momentPolynomial, properPart, Polynomial.add_divByMonic, Lpoly_add, map_add,
      Polynomial.eval_add, add_mul, add_div, Finset.sum_add_distrib]
    ring
  map_smul' c f := by
    simp only [momentPolynomial, properPart, Polynomial.smul_divByMonic, Lpoly_smul,
      Polynomial.eval_smul, smul_eq_mul, map_mul, RingHom.id_apply]
    rw [Polynomial.smul_eq_C_mul, mul_sub, Finset.mul_sum]
    congr 1
    apply sum_congr rfl
    intro a _
    have key : ∀ (u v : 𝕜) (p : 𝕜[X]), u = c * v → C u * p = C c * (C v * p) := by
      intro u v p h; rw [h, map_mul, mul_assoc]
    apply key
    ring

@[simp] theorem momentFunctional_apply (τ : 𝕜) (K : ℕ) (f : 𝕜[X]) :
    momentFunctional ε τ K f = momentPolynomial ε τ K f := rfl

/-- The generalized functional agrees with the formal moments of `Defs`. -/
theorem momentPolynomial_monomial (τ : 𝕜) (K k : ℕ) :
    momentPolynomial ε τ K (X ^ k) = X * C (mLin ε τ K k) + C (mConst ε τ K k) := by
  have he (a : ℕ) : (X ^ k : 𝕜[X]).eval (node ε τ a) * (2 * τ ^ a) /
      (derivative (F ε τ K)).eval (node ε τ a) = 2 * (res ε τ K k a * τ ^ a) := by
    simp only [Polynomial.eval_pow, Polynomial.eval_X, res]
    ring
  have hsum : (∑ a ∈ Icc 1 K, C (2 * (res ε τ K k a * τ ^ a)) * (X - C (S ε τ a))) =
      X * C (2 * ∑ a ∈ Icc 1 K, res ε τ K k a * τ ^ a) -
        C (2 * ∑ a ∈ Icc 1 K, res ε τ K k a * τ ^ a * S ε τ a) := by
    rw [map_mul, map_mul, map_sum, map_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply sum_congr rfl
    intro a _
    simp only [map_mul]
    ring
  simp only [momentPolynomial, properPart, he]
  rw [hsum]
  simp only [mLin, mConst, map_add, map_neg, map_mul]
  ring

noncomputable def normalizedGram (ε : ℤ) (τ : 𝕜) (K : ℕ) (G : Fin K → 𝕜[X]) :
    Matrix (Fin K) (Fin K) 𝕜[X] :=
  Matrix.of fun i j => C (nrm ε τ K) * momentPolynomial ε τ K (G i * G j)

noncomputable def unnormalizedGram (ε : ℤ) (τ : 𝕜) (K : ℕ) (G : Fin K → 𝕜[X]) :
    Matrix (Fin K) (Fin K) 𝕜[X] :=
  Matrix.of fun i j => momentPolynomial ε τ K (G i * G j)

noncomputable def polynomialChange (K : ℕ) (G : Fin K → 𝕜[X]) : Matrix (Fin K) (Fin K) 𝕜 :=
  Matrix.of fun i j => (G i).coeff j.val

theorem hankel_apply (τ : 𝕜) (K : ℕ) (i j : Fin K) :
    ((X : 𝕜[X]) • (hankelLin ε τ K).map C + (hankelConst ε τ K).map C) i j =
      C (nrm ε τ K) * momentPolynomial ε τ K (X ^ (i.val + j.val)) := by
  rw [momentPolynomial_monomial]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, hankelLin, hankelConst,
    Matrix.of_apply, smul_eq_mul, map_mul]
  ring

theorem normalizedGram_congruence (τ : 𝕜) (K : ℕ) (G : Fin K → 𝕜[X])
    (hG : ∀ i, (G i).natDegree < K) :
    normalizedGram ε τ K G = (polynomialChange K G).map C *
      ((X : 𝕜[X]) • (hankelLin ε τ K).map C + (hankelConst ε τ K).map C) *
      ((polynomialChange K G).map C).transpose := by
  let U := polynomialChange K G
  let L : 𝕜[X] →ₗ[𝕜] 𝕜[X] := (nrm ε τ K) • momentFunctional ε τ K
  have hexp (i : Fin K) : G i = ∑ j : Fin K, U i j • (X : 𝕜[X]) ^ j.val := by
    have h := (G i).as_sum_range_C_mul_X_pow' (hG i)
    rw [← Fin.sum_univ_eq_sum_range _ K] at h
    simpa only [U, polynomialChange, Matrix.of_apply, Polynomial.smul_eq_C_mul] using h
  have hmono (i j : Fin K) :
      L ((X : 𝕜[X]) ^ (i.val + j.val)) =
        ((X : 𝕜[X]) • (hankelLin ε τ K).map C + (hankelConst ε τ K).map C) i j := by
    rw [hankel_apply]
    simp [L, Polynomial.smul_eq_C_mul]
  apply Matrix.ext
  intro i j
  have hid : normalizedGram ε τ K G i j = L (G i * G j) := by
    simp [normalizedGram, L, Polynomial.smul_eq_C_mul]
  rw [hid, hexp i, hexp j]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    ← pow_add, map_sum, map_smul, hmono]
  simp only [Polynomial.smul_eq_C_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
    Finset.mul_sum]
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro r _
  ring

/-- The determinant changes by the square of the coefficient determinant. -/
theorem det_normalizedGram (τ : 𝕜) (K : ℕ) (G : Fin K → 𝕜[X])
    (hG : ∀ i, (G i).natDegree < K) :
    (normalizedGram ε τ K G).det = C ((polynomialChange K G).det) ^ 2 * Delta ε τ K := by
  rw [normalizedGram_congruence τ K G hG, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  have hm : ((polynomialChange K G).map C).det = C ((polynomialChange K G).det) :=
    (RingHom.map_det C (polynomialChange K G)).symm
  rw [hm]
  unfold Delta
  ring

theorem det_normalizedGram_eq (τ : 𝕜) (K : ℕ) (G : Fin K → 𝕜[X]) :
    (normalizedGram ε τ K G).det = C (nrm ε τ K) ^ K * (unnormalizedGram ε τ K G).det := by
  have hmatrix : normalizedGram ε τ K G = C (nrm ε τ K) • unnormalizedGram ε τ K G := by
    ext a b
    rfl
  rw [hmatrix, Matrix.det_smul, Fintype.card_fin]

end LucasU.Denom
