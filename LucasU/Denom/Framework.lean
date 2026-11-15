/-
Generalised from lean_fibzeta FibZeta/Denom/Framework.lean (ε = ±1, general t).
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/PolynomialMomentRank.lean,
lean/QZeta3/LocalGramBounds.lean and lean/QZeta3/CyclotomicLocal.lean (Apache-2.0, Lean formalisation
by F. Solomon Admasu). Changes: the singular polynomial moments are all `ν_l` with `l ≥ k₀` (not a
single `μ_d`); the rank bound is `K − 1 − k₀`; one local theorem covers every root type.
-/
import LucasU.Denom.Gram
import LucasU.Denom.Local
import LucasU.Denom.LocalDet

/-!
# The local determinant bound in a general basis

`local_bound_of_basis` is the common core of Proposition 3.2 and Lemma 3.3.  Given a basis `G` of
polynomials of degree `< K` with regular coefficients and unit change-of-basis determinant at `ω`,
row/column weights `r, c` that make every scaled pole part `π^{r_i + c_j} · properPart(G_i G_j)`
regular, and `k₀` such that `ν_l` is regular at `ω` for `1 ≤ l < k₀`, the determinant satisfies
`π^{∑ r + ∑ c + (K − 1 − k₀)} · coeff ∈ regularAt ω`.

The polynomial part is split as `A + π⁻¹ B` (`poly_part_split`): `ν_l = π⁻¹ (π ν_l)` for `l ≥ k₀`
(`1 − α_l` has at most a simple zero), and the bilinear form `B` has rank `≤ K − 1 − k₀` because
`f` of degree `≤ k₀` lies in its kernel.
-/

open Polynomial Finset Matrix

namespace LucasU.Denom

variable {𝕜 : Type*} [Field 𝕜] {ε : ℤ}

local notation "Xr" => (RatFunc.X : RatFunc 𝕜)

/-! ### Simple zeros of `1 − α_l` and `1 − w^n` -/

theorem uniformizer_div_mem_of_eval_or_derivative (ω : 𝕜) (p : 𝕜[X])
    (h : p.eval ω ≠ 0 ∨ (derivative p).eval ω ≠ 0) :
    uniformizer ω / algebraMap 𝕜[X] (RatFunc 𝕜) p ∈ regularAt ω := by
  by_cases hp : p.eval ω = 0
  · exact uniformizer_div_mem_of_simple_root ω p hp (h.resolve_left (not_not.mpr hp))
  · rw [div_eq_mul_inv]
    exact (regularAt ω).mul_mem (uniformizer_mem ω) (inv_polynomial_mem_regularAt ω p hp)

theorem one_sub_alpha_X (j : ℕ) :
    1 - alpha ε Xr j =
      algebraMap 𝕜[X] (RatFunc 𝕜) (1 - C ((ε : 𝕜) ^ (j + 1)) * X ^ (2 * j + 1)) := by
  simp only [map_sub, map_one, map_mul, map_pow, RatFunc.algebraMap_X,
    map_intCast, alpha, wpar]
  ring

theorem one_sub_geom_X (n : ℕ) :
    1 - (wpar ε Xr) ^ n = algebraMap 𝕜[X] (RatFunc 𝕜) (1 - C ((ε : 𝕜) ^ n) * X ^ (2 * n)) := by
  simp only [map_sub, map_one, map_mul, map_pow, RatFunc.algebraMap_X,
    map_intCast, wpar]
  ring

theorem eval_one_sub_alpha (ω : 𝕜) (j : ℕ) :
    (1 - C ((ε : 𝕜) ^ (j + 1)) * X ^ (2 * j + 1) : 𝕜[X]).eval ω = 1 - alpha ε ω j := by
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_pow, eval_X, alpha, wpar]
  ring

theorem eval_one_sub_geom (ω : 𝕜) (n : ℕ) :
    (1 - C ((ε : 𝕜) ^ n) * X ^ (2 * n) : 𝕜[X]).eval ω = 1 - (wpar ε ω) ^ n := by
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_pow, eval_X, wpar]
  ring

variable [CharZero 𝕜]

theorem derivative_C_mul_X_pow_eval_ne_zero (ω : 𝕜) (hω : ω ≠ 0) (c : 𝕜) (hc : c ≠ 0) (n : ℕ)
    (hn : 0 < n) : (derivative (1 - C c * X ^ n : 𝕜[X])).eval ω ≠ 0 := by
  simp only [derivative_sub, derivative_one, zero_sub, derivative_C_mul_X_pow, eval_neg,
    eval_mul, eval_C, eval_pow, eval_X, neg_ne_zero]
  refine mul_ne_zero (mul_ne_zero hc ?_) (pow_ne_zero _ hω)
  exact_mod_cast hn.ne'

theorem uniformizer_div_one_sub_alpha_mem (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω : ω ≠ 0) (j : ℕ) :
    uniformizer ω / (1 - alpha ε Xr j) ∈ regularAt ω := by
  rw [one_sub_alpha_X]
  exact uniformizer_div_mem_of_eval_or_derivative ω _ (Or.inr
    (derivative_C_mul_X_pow_eval_ne_zero ω hω _ (pow_ne_zero _ (eps_cast_ne_zero hε))
      _ (by omega)))

theorem uniformizer_div_one_sub_geom_mem (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω : ω ≠ 0) (n : ℕ) (hn : 0 < n) :
    uniformizer ω / (1 - (wpar ε Xr) ^ n) ∈ regularAt ω := by
  rw [one_sub_geom_X]
  exact uniformizer_div_mem_of_eval_or_derivative ω _ (Or.inr
    (derivative_C_mul_X_pow_eval_ne_zero ω hω _ (pow_ne_zero _ (eps_cast_ne_zero hε))
      _ (by omega)))

omit [CharZero 𝕜] in
theorem inv_one_sub_alpha_mem (ω : 𝕜) (j : ℕ) (h : alpha ε ω j ≠ 1) :
    (1 - alpha ε Xr j)⁻¹ ∈ regularAt ω := by
  rw [one_sub_alpha_X]
  exact inv_polynomial_mem_regularAt ω _ (by rw [eval_one_sub_alpha]; exact sub_ne_zero.mpr h.symm)

omit [CharZero 𝕜] in
theorem inv_one_sub_geom_mem (ω : 𝕜) (n : ℕ) (h : (wpar ε ω) ^ n ≠ 1) :
    (1 - (wpar ε Xr) ^ n)⁻¹ ∈ regularAt ω := by
  rw [one_sub_geom_X]
  exact inv_polynomial_mem_regularAt ω _ (by rw [eval_one_sub_geom]; exact sub_ne_zero.mpr h.symm)

omit [CharZero 𝕜] in
theorem alpha_X_mem (ω : 𝕜) (j : ℕ) : alpha ε Xr j ∈ regularAt ω :=
  (regularAt ω).mul_mem ((regularAt ω).mul_mem (intCast_mem _ ε) (base_mem_regularAt ω))
    ((regularAt ω).pow_mem (wpar_mem _ (base_mem_regularAt ω)) j)

/-- Every polynomial moment has at most a simple pole at a nonzero point (fact (c)). -/
theorem uniformizer_mul_nu_mem (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω : ω ≠ 0) (j : ℕ) :
    uniformizer ω * nu ε Xr j ∈ regularAt ω := by
  have h := (regularAt ω).mul_mem ((regularAt ω).mul_mem ((regularAt ω).mul_mem
    (natCast_mem _ j) ((regularAt ω).add_mem (natCast_mem _ j) (regularAt ω).one_mem))
    (alpha_X_mem (ε := ε) ω j)) (uniformizer_div_one_sub_alpha_mem hε ω hω j)
  convert h using 1
  rw [nu]
  ring

omit [CharZero 𝕜] in
theorem nu_mem_of_alpha_ne (ω : 𝕜) (j : ℕ) (h : alpha ε ω j ≠ 1) : nu ε Xr j ∈ regularAt ω := by
  rw [nu, div_eq_mul_inv]
  exact (regularAt ω).mul_mem ((regularAt ω).mul_mem
    ((regularAt ω).mul_mem (natCast_mem _ j) ((regularAt ω).add_mem (natCast_mem _ j)
      (regularAt ω).one_mem)) (alpha_X_mem (ε := ε) ω j)) (inv_one_sub_alpha_mem ω j h)

omit [CharZero 𝕜] in
theorem inv_w_mem_regularAt (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω : ω ≠ 0) :
    (wpar ε Xr)⁻¹ ∈ regularAt ω := by
  rw [wpar_inv hε]
  exact wpar_mem _ (inv_base_mem_regularAt ω hω)

/-! ### The rank of the singular polynomial part -/

omit [CharZero 𝕜] in
/-- A functional killing all polynomials of degree `< k₀`, applied to the quotients of a Gram
family, has rank `≤ K − 1 − k₀`. -/
theorem rank_quotient_functional_le {F₀ : (RatFunc 𝕜)[X]} (hF : F₀.Monic) {K : ℕ}
    (hdegree : F₀.natDegree = K) (G : Fin K → (RatFunc 𝕜)[X])
    (hG : ∀ i, (G i).natDegree < K) (L : (RatFunc 𝕜)[X] →ₗ[RatFunc 𝕜] RatFunc 𝕜) (k₀ : ℕ)
    (hL : ∀ q : (RatFunc 𝕜)[X], q.natDegree < k₀ → L q = 0) :
    (Matrix.of fun i j => L ((G i * G j) /ₘ F₀)).rank ≤ K - 1 - k₀ := by
  classical
  let U : Matrix (Fin K) (Fin K) (RatFunc 𝕜) := fun i j => (G i).coeff j.val
  let L' : (RatFunc 𝕜)[X] →ₗ[RatFunc 𝕜] RatFunc 𝕜 := L.comp (Polynomial.divByMonicHom F₀)
  let M₀ : Matrix (Fin K) (Fin K) (RatFunc 𝕜) := fun i j => L' ((X : (RatFunc 𝕜)[X]) ^ (i.val + j.val))
  have hexp (i : Fin K) : G i = ∑ j : Fin K, U i j • (X : (RatFunc 𝕜)[X]) ^ j.val := by
    have h := (G i).as_sum_range_C_mul_X_pow' (hG i)
    rw [← Fin.sum_univ_eq_sum_range _ K] at h
    simpa only [U, Polynomial.smul_eq_C_mul] using h
  have hzero (i j : Fin K) (hi : i.val ≤ k₀) : M₀ i j = 0 := by
    change L ((X ^ (i.val + j.val)) /ₘ F₀) = 0
    by_cases hij : i.val + j.val < K
    · have hz : ((X : (RatFunc 𝕜)[X]) ^ (i.val + j.val)) /ₘ F₀ = 0 := by
        apply (divByMonic_eq_zero_iff hF).mpr
        rw [degree_X_pow, degree_eq_natDegree hF.ne_zero, hdegree]
        exact_mod_cast hij
      rw [hz, map_zero]
    · apply hL
      rw [natDegree_divByMonic _ hF, natDegree_X_pow, hdegree]
      have := j.isLt
      omega
  have hM₀ : M₀.rank ≤ K - 1 - k₀ := by
    by_cases hk : k₀ < K
    · let a : Fin K := ⟨k₀, hk⟩
      have h := Matrix.rank_le_card_of_support_subset M₀ (Ioi a) (by
        rw [Function.support_subset_iff']
        intro i hi
        ext j
        apply hzero i j
        have hin : ¬a < i := by simpa only [mem_coe, mem_Ioi] using hi
        exact le_of_not_gt hin)
      rw [Fin.card_Ioi] at h
      dsimp [a] at h
      omega
    · have hz : M₀ = 0 := by
        ext i j
        exact hzero i j (by have := i.isLt; omega)
      rw [hz, Matrix.rank_zero]
      omega
  have heq : (Matrix.of fun i j => L ((G i * G j) /ₘ F₀)) = U * M₀ * U.transpose := by
    ext i j
    change L' (G i * G j) = _
    rw [hexp i, hexp j]
    have hmono (i j : Fin K) : L' ((X : (RatFunc 𝕜)[X]) ^ (i.val + j.val)) = M₀ i j := rfl
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      ← pow_add, map_sum, map_smul, smul_eq_mul, hmono]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    apply sum_congr rfl
    intro s _
    apply sum_congr rfl
    intro r _
    ring
  rw [heq]
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hM₀)

/-- The polynomial part of the scaled Gram matrix is `A + π⁻¹ B` with `A, B` regular and
`rank B ≤ K − 1 − k₀`. -/
theorem poly_part_split (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω0 : ω ≠ 0) (K : ℕ)
    (G : Fin K → (RatFunc 𝕜)[X]) (hGdegree : ∀ i, (G i).natDegree < K)
    (hGcoeff : ∀ i j, (G i).coeff j ∈ regularAt ω) (r c : Fin K → ℕ) (k₀ : ℕ)
    (hnu : ∀ l, 1 ≤ l → l < k₀ → nu ε Xr l ∈ regularAt ω) :
    ∃ A B : Matrix (Fin K) (Fin K) (RatFunc 𝕜),
      (∀ i j, A i j ∈ regularAt ω) ∧ (∀ i j, B i j ∈ regularAt ω) ∧
      B.rank ≤ K - 1 - k₀ ∧
      ∀ i j, uniformizer ω ^ (r i + c j) * Lpoly ε Xr ((G i * G j) /ₘ F ε Xr K) =
        A i j + (uniformizer ω)⁻¹ * B i j := by
  classical
  set π := uniformizer ω with hπ
  let H : Fin K → Fin K → (RatFunc 𝕜)[X] := fun i j => (G i * G j) /ₘ F ε Xr K
  let lo := (range K).filter (· < k₀)
  let hi := (range K).filter (fun l => ¬ l < k₀)
  let Lhi : (RatFunc 𝕜)[X] →ₗ[RatFunc 𝕜] RatFunc 𝕜 :=
    ∑ l ∈ hi, (π * nu ε Xr l) • Polynomial.lcoeff (RatFunc 𝕜) l
  have hLhi (q : (RatFunc 𝕜)[X]) : Lhi q = ∑ l ∈ hi, q.coeff l * (π * nu ε Xr l) := by
    simp only [Lhi, LinearMap.sum_apply, LinearMap.smul_apply, Polynomial.lcoeff_apply,
      smul_eq_mul]
    exact sum_congr rfl fun _ _ => mul_comm _ _
  let A : Matrix (Fin K) (Fin K) (RatFunc 𝕜) := fun i j =>
    π ^ (r i + c j) * ∑ l ∈ lo, (H i j).coeff l * nu ε Xr l
  let B : Matrix (Fin K) (Fin K) (RatFunc 𝕜) := fun i j => π ^ (r i + c j) * Lhi (H i j)
  have hHcoeff (i j : Fin K) (l : ℕ) : (H i j).coeff l ∈ regularAt ω := by
    apply quotient_coeff_mem (regularAt ω) Xr (inv_w_mem_regularAt hε ω hω0) K
    apply (coeff_mem_iff_lifts (regularAt ω) (G i * G j)).mpr
    exact (Polynomial.liftsRing (regularAt ω).subtype).mul_mem
      ((coeff_mem_iff_lifts _ _).mp (hGcoeff i)) ((coeff_mem_iff_lifts _ _).mp (hGcoeff j))
  have hHdegree (i j : Fin K) : (H i j).natDegree < K := by
    dsimp only [H]
    have hprod : (G i * G j).natDegree ≤ (G i).natDegree + (G j).natDegree :=
      Polynomial.natDegree_mul_le
    have := natDegree_quotient_le (ε := ε) Xr K (G i * G j) hprod
    have := hGdegree i
    have := hGdegree j
    omega
  have hA (i j : Fin K) : A i j ∈ regularAt ω := by
    apply (regularAt ω).mul_mem ((regularAt ω).pow_mem (uniformizer_mem ω) _)
    apply (regularAt ω).sum_mem
    intro l hl
    apply (regularAt ω).mul_mem (hHcoeff i j l)
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · rw [nu_zero]; exact (regularAt ω).zero_mem
    · exact hnu l hl0 (mem_filter.mp hl).2
  have hB (i j : Fin K) : B i j ∈ regularAt ω := by
    apply (regularAt ω).mul_mem ((regularAt ω).pow_mem (uniformizer_mem ω) _)
    rw [hLhi]
    exact (regularAt ω).sum_mem fun l _ =>
      (regularAt ω).mul_mem (hHcoeff i j l) (uniformizer_mul_nu_mem hε ω hω0 l)
  have hLvanish (q : (RatFunc 𝕜)[X]) (hq : q.natDegree < k₀) : Lhi q = 0 := by
    rw [hLhi]
    apply Finset.sum_eq_zero
    intro l hl
    rw [coeff_eq_zero_of_natDegree_lt (by have := (mem_filter.mp hl).2; omega), zero_mul]
  have hMrank : (Matrix.of fun i j => Lhi (H i j)).rank ≤ K - 1 - k₀ :=
    rank_quotient_functional_le (F_monic _ K) (F_natDegree _ K) G hGdegree Lhi k₀ hLvanish
  have hBrank : B.rank ≤ K - 1 - k₀ := by
    have heq : B = Matrix.diagonal (fun i => π ^ (r i)) *
        (Matrix.of fun i j => Lhi (H i j)) * Matrix.diagonal (fun j => π ^ (c j)) := by
      ext i j
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [B, Matrix.of_apply, pow_add]
      ring
    rw [heq]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hMrank)
  refine ⟨A, B, hA, hB, hBrank, ?_⟩
  intro i j
  have hsplit : Lpoly ε Xr (H i j) = ∑ l ∈ lo, (H i j).coeff l * nu ε Xr l +
      ∑ l ∈ hi, (H i j).coeff l * nu ε Xr l := by
    rw [Lpoly_eq_sum_range Xr _ K (hHdegree i j)]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  change π ^ (r i + c j) * Lpoly ε Xr (H i j) = A i j + π⁻¹ * B i j
  have ht : π ≠ 0 := uniformizer_ne_zero ω
  simp only [A, B, hLhi, hsplit, mul_add]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply sum_congr rfl
  intro l _
  field_simp

/-! ### The local theorem -/

/-- **Local determinant bound in a general basis** (core of Prop 3.2 and Lemma 3.3). -/
theorem local_bound_of_basis (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω0 : ω ≠ 0) (K : ℕ)
    (G : Fin K → (RatFunc 𝕜)[X]) (hGdegree : ∀ i, (G i).natDegree < K)
    (hGcoeff : ∀ i j, (G i).coeff j ∈ regularAt ω)
    (hU0 : (polynomialChange K G).det ≠ 0)
    (hUinv : (polynomialChange K G).det⁻¹ ∈ regularAt ω)
    (r c : Fin K → ℕ)
    (hproper : ∀ i j, C (uniformizer ω ^ (r i + c j)) * properPart ε Xr K (G i * G j) ∈
      Polynomial.liftsRing (regularAt ω).subtype)
    (k₀ : ℕ) (hnu : ∀ l, 1 ≤ l → l < k₀ → nu ε Xr l ∈ regularAt ω) (i : ℕ) :
    uniformizer ω ^ ((∑ i, r i) + (∑ i, c i) + (K - 1 - k₀)) * (Delta ε Xr K).coeff i ∈
      regularAt ω := by
  classical
  let T := Polynomial.liftsRing (regularAt ω).subtype
  set π := uniformizer ω with hπ
  obtain ⟨A, B, hA, hB, hBrank, hAB⟩ :=
    poly_part_split hε ω hω0 K G hGdegree hGcoeff r c k₀ hnu
  let P : Matrix (Fin K) (Fin K) (RatFunc 𝕜)[X] := fun i j =>
    C (π ^ (r i + c j)) * properPart ε Xr K (G i * G j)
  let A' : Matrix (Fin K) (Fin K) (RatFunc 𝕜)[X] := A.map C - P
  have hA' (i j : Fin K) : A' i j ∈ T :=
    T.sub_mem (C_mem_lifts _ _ (hA i j)) (hproper i j)
  have hB' (i j : Fin K) : C (B i j) ∈ T := C_mem_lifts _ _ (hB i j)
  have hmem := C_pow_mul_det_add_inv_mem_subring T π
    (uniformizer_ne_zero ω) (C_mem_lifts _ _ (uniformizer_mem ω))
    A' B hA' hB' (K - 1 - k₀) hBrank
  have heq : A' + C (π⁻¹) • B.map C =
      Matrix.of fun i j => C π ^ (r i + c j) * unnormalizedGram ε Xr K G i j := by
    apply Matrix.ext
    intro i j
    change C (A i j) - P i j + C (π⁻¹) * C (B i j) = _
    simp only [P, unnormalizedGram, Matrix.of_apply, momentPolynomial,
      ← map_pow, mul_sub, ← map_mul]
    rw [hAB i j, map_add, map_mul]
    ring
  rw [heq, det_weighted_eq] at hmem
  have hdet : C π ^ ((∑ i, r i) + (∑ i, c i) + (K - 1 - k₀)) *
      (unnormalizedGram ε Xr K G).det ∈ T := by
    simpa only [← mul_assoc, ← pow_add, Nat.add_comm (K - 1 - k₀)] using hmem
  -- descend through the basis change
  have hnrm : nrm ε Xr K ∈ regularAt ω := by
    unfold nrm
    rw [← inv_pow]
    exact (regularAt ω).mul_mem ((regularAt ω).pow_mem ((regularAt ω).neg_mem
      (regularAt ω).one_mem) K) ((regularAt ω).pow_mem (inv_w_mem_regularAt hε ω hω0) _)
  have hinv := C_mem_lifts _ _ hUinv
  have hm := T.mul_mem (T.pow_mem hinv 2) (T.mul_mem (T.pow_mem (C_mem_lifts _ _ hnrm) K) hdet)
  set E := (∑ i, r i) + (∑ i, c i) + (K - 1 - k₀)
  have hidentity : C ((polynomialChange K G).det⁻¹) ^ 2 *
      (C (nrm ε Xr K) ^ K * (C π ^ E * (unnormalizedGram ε Xr K G).det)) =
      C π ^ E * Delta ε Xr K := by
    calc _ = C π ^ E * (C ((polynomialChange K G).det⁻¹) ^ 2 *
          (normalizedGram ε Xr K G).det) := by
          rw [det_normalizedGram_eq]
          ring
      _ = _ := by
        rw [det_normalizedGram Xr K G hGdegree]
        have hc : C ((polynomialChange K G).det⁻¹) ^ 2 * C ((polynomialChange K G).det) ^ 2 =
            (1 : (RatFunc 𝕜)[X]) := by
          rw [← mul_pow, ← map_mul, inv_mul_cancel₀ hU0, map_one, one_pow]
        rw [← mul_assoc (C ((polynomialChange K G).det⁻¹) ^ 2), hc, one_mul]
  rw [hidentity] at hm
  have hcoeff := (coeff_mem_iff_lifts (regularAt ω) _).mpr hm i
  simpa only [← map_pow, Polynomial.coeff_C_mul] using hcoeff

end LucasU.Denom
