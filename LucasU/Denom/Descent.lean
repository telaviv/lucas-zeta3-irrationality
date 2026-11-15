/-
Generalised from lean_fibzeta FibZeta/Denom/Descent.lean (ε = ±1, general t).
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/IntegerFractions.lean,
lean/QZeta3/LocalPoleDescent.lean, lean/QZeta3/DenominatorDescent.lean and
lean/QZeta3/GenericEvaluation.lean (Apache-2.0, Lean formalisation by F. Solomon Admasu). Changes:
the integer-fraction ring now also inverts `±(X^{2n} ∓ 1)` and `±(X^{2k+1} ± 1)`; the clearing
polynomial is `CKpoly` (orders `d ≤ 4K`); specialization is at a real non-root of unity `τ`.
-/
import LucasU.Denom.Local
import LucasU.Denom.Specialization
import LucasU.Statements
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Proposition 3.4: from local bounds to the global denominator

* `integerMonicFractions`: rational functions `A/B` with `A, B ∈ ℤ[X]`, `B` monic.  Every
  coefficient of the generic `Delta X K` lies there (Lemma 3.1, "no rational constant is inverted").
* Pole descent: a rational function regular at every `ω ≠ 0` becomes a polynomial after
  multiplication by a power of `X`; if it is an integer monic fraction, the polynomial has integer
  coefficients (Gauss).
* `integrality_of_local_bounds`: the local bounds `(X − ω)^{b_{K,d}} · coeff ∈ regularAt ω` at all
  primitive `d`-th roots `ω`, `d ≤ 4K`, imply `Integrality`.
-/

open Polynomial Finset

namespace LucasU.Denom

variable {𝕜 : Type*} [Field 𝕜] {ε : ℤ}

/-! ### Integer fractions with monic denominators -/

noncomputable def intPolynomialMap : ℤ[X] →+* RatFunc 𝕜 :=
  (algebraMap 𝕜[X] (RatFunc 𝕜)).comp (Polynomial.mapRingHom (Int.castRingHom 𝕜))

theorem intPolynomialMap_apply (f : ℤ[X]) :
    intPolynomialMap (𝕜 := 𝕜) f =
      algebraMap 𝕜[X] (RatFunc 𝕜) (f.map (Int.castRingHom 𝕜)) := rfl

theorem intPolynomialMap_ne_zero {f : ℤ[X]} (hf : f.Monic) :
    intPolynomialMap (𝕜 := 𝕜) f ≠ 0 :=
  RatFunc.algebraMap_ne_zero (hf.map (Int.castRingHom 𝕜)).ne_zero

def IsIntegerMonicFraction (x : RatFunc 𝕜) : Prop :=
  ∃ A B : ℤ[X], B.Monic ∧ x = intPolynomialMap A / intPolynomialMap B

def integerMonicFractions : Subring (RatFunc 𝕜) where
  carrier := {x | IsIntegerMonicFraction x}
  zero_mem' := ⟨0, 1, monic_one, by simp⟩
  one_mem' := ⟨1, 1, monic_one, by simp⟩
  neg_mem' := by
    rintro x ⟨A, B, hB, rfl⟩
    exact ⟨-A, B, hB, by rw [map_neg, neg_div]⟩
  add_mem' := by
    rintro x y ⟨A, B, hB, rfl⟩ ⟨C, D, hD, rfl⟩
    refine ⟨A * D + B * C, B * D, hB.mul hD, ?_⟩
    rw [map_add, map_mul, map_mul, map_mul]
    exact div_add_div _ _ (intPolynomialMap_ne_zero (𝕜 := 𝕜) hB)
      (intPolynomialMap_ne_zero (𝕜 := 𝕜) hD)
  mul_mem' := by
    rintro x y ⟨A, B, hB, rfl⟩ ⟨C, D, hD, rfl⟩
    exact ⟨A * C, B * D, hB.mul hD, by rw [map_mul, map_mul, div_mul_div_comm]⟩

theorem integerPolynomial_mem (A : ℤ[X]) :
    intPolynomialMap (𝕜 := 𝕜) A ∈ integerMonicFractions :=
  ⟨A, 1, monic_one, by simp⟩

theorem inverse_monic_mem (B : ℤ[X]) (hB : B.Monic) :
    (intPolynomialMap (𝕜 := 𝕜) B)⁻¹ ∈ integerMonicFractions :=
  ⟨1, B, hB, by simp⟩

theorem intPolynomialMap_X : intPolynomialMap (𝕜 := 𝕜) X = RatFunc.X := by
  simp [intPolynomialMap]

theorem eps_pow_inv_mem (hε : ε = 1 ∨ ε = -1) (n : ℕ) :
    ((ε : RatFunc 𝕜) ^ n)⁻¹ ∈ integerMonicFractions := by
  rw [← inv_pow, eps_cast_inv hε]
  exact integerMonicFractions.pow_mem (intCast_mem _ ε) n

theorem eps_pow_sq (hε : ε = 1 ∨ ε = -1) (n : ℕ) : ((ε : RatFunc 𝕜) ^ n) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, eps_cast_sq hε, one_pow]

/-- `1 − w^n = −εⁿ (X^{2n} − εⁿ)`. -/
theorem inv_geom_mem_integerMonicFractions (hε : ε = 1 ∨ ε = -1) (n : ℕ) (hn : 1 ≤ n) :
    (1 - (wpar ε (RatFunc.X : RatFunc 𝕜)) ^ n)⁻¹ ∈ integerMonicFractions := by
  have hmonic : (X ^ (2 * n) - C (ε ^ n) : ℤ[X]).Monic :=
    Polynomial.monic_X_pow_sub_C _ (by omega)
  have hB := inverse_monic_mem (𝕜 := 𝕜) _ hmonic
  have hmap : intPolynomialMap (𝕜 := 𝕜) (X ^ (2 * n) - C (ε ^ n)) =
      RatFunc.X ^ (2 * n) - (ε : RatFunc 𝕜) ^ n := by
    simp [intPolynomialMap, RatFunc.algebraMap_X]
  rw [hmap] at hB
  have heq : (1 - (wpar ε (RatFunc.X : RatFunc 𝕜)) ^ n) =
      -((ε : RatFunc 𝕜) ^ n * (RatFunc.X ^ (2 * n) - (ε : RatFunc 𝕜) ^ n)) := by
    rw [wpar_pow]
    linear_combination (-1 : RatFunc 𝕜) * eps_pow_sq (𝕜 := 𝕜) hε n
  rw [heq, inv_neg, mul_inv]
  exact integerMonicFractions.neg_mem (integerMonicFractions.mul_mem (eps_pow_inv_mem hε n) hB)

/-- `1 − α_k = −ε^{k+1} (X^{2k+1} − ε^{k+1})`. -/
theorem inv_alpha_mem_integerMonicFractions (hε : ε = 1 ∨ ε = -1) (k : ℕ) :
    (1 - alpha ε (RatFunc.X : RatFunc 𝕜) k)⁻¹ ∈ integerMonicFractions := by
  have hmonic : (X ^ (2 * k + 1) - C (ε ^ (k + 1)) : ℤ[X]).Monic :=
    Polynomial.monic_X_pow_sub_C _ (by omega)
  have hB := inverse_monic_mem (𝕜 := 𝕜) _ hmonic
  have hmap : intPolynomialMap (𝕜 := 𝕜) (X ^ (2 * k + 1) - C (ε ^ (k + 1))) =
      RatFunc.X ^ (2 * k + 1) - (ε : RatFunc 𝕜) ^ (k + 1) := by
    simp [intPolynomialMap, RatFunc.algebraMap_X]
  rw [hmap] at hB
  have heq : (1 - alpha ε (RatFunc.X : RatFunc 𝕜) k) =
      -((ε : RatFunc 𝕜) ^ (k + 1) * (RatFunc.X ^ (2 * k + 1) - (ε : RatFunc 𝕜) ^ (k + 1))) := by
    rw [alpha, wpar_pow]
    linear_combination (-1 : RatFunc 𝕜) * eps_pow_sq (𝕜 := 𝕜) hε (k + 1)
  rw [heq, inv_neg, mul_inv]
  exact integerMonicFractions.neg_mem
    (integerMonicFractions.mul_mem (eps_pow_inv_mem hε (k + 1)) hB)

/-- All generic moments are built from integer fractions with monic denominators (Lemma 3.1). -/
theorem integerMonicFraction_localization (hε : ε = 1 ∨ ε = -1) (K : ℕ) :
    LocalizationData (integerMonicFractions (𝕜 := 𝕜)) ε RatFunc.X K where
  sign := hε
  base_mem := by simpa [intPolynomialMap_X] using integerPolynomial_mem (𝕜 := 𝕜) X
  inv_base_mem := by
    simpa [intPolynomialMap_X] using inverse_monic_mem (𝕜 := 𝕜) X monic_X
  inv_geom_mem n hn := inv_geom_mem_integerMonicFractions hε n (mem_Icc.mp hn).1
  inv_alpha_mem k _ := inv_alpha_mem_integerMonicFractions hε k

theorem Delta_coeff_integerMonicFraction (hε : ε = 1 ∨ ε = -1) (K i : ℕ) :
    (Delta ε (RatFunc.X : RatFunc 𝕜) K).coeff i ∈ integerMonicFractions :=
  (integerMonicFraction_localization (𝕜 := 𝕜) hε K).Delta_coeff_mem i

/-- Gauss descent in the form needed after clearing finite poles. -/
theorem polynomial_of_integerMonicFraction [CharZero 𝕜] (x : RatFunc 𝕜)
    (hx : x ∈ integerMonicFractions) (P : 𝕜[X])
    (hP : x = algebraMap 𝕜[X] (RatFunc 𝕜) P) :
    ∃ A : ℤ[X], x = intPolynomialMap A := by
  obtain ⟨A, B, hB, hfrac⟩ := hx
  have he : (A.map (Int.castRingHom 𝕜)) = (B.map (Int.castRingHom 𝕜)) * P := by
    apply RatFunc.algebraMap_injective 𝕜
    rw [map_mul, ← hP, hfrac, ← intPolynomialMap_apply, ← intPolynomialMap_apply]
    field_simp [intPolynomialMap_ne_zero hB]
  have hdiv : B.map (Int.castRingHom 𝕜) ∣ A.map (Int.castRingHom 𝕜) := ⟨P, he⟩
  have hdivZ : B ∣ A :=
    (Polynomial.map_dvd_map (Int.castRingHom 𝕜) (Int.cast_injective) hB).mp hdiv
  obtain ⟨Q, hQ⟩ := hdivZ
  refine ⟨Q, ?_⟩
  rw [hfrac, hQ, map_mul, mul_div_cancel_left₀ _ (intPolynomialMap_ne_zero hB)]

/-! ### Pole descent -/

/-- A local uniformizer bound controls the multiplicity of the reduced denominator. -/
theorem denom_rootMultiplicity_le_of_regular (ω : 𝕜) (x : RatFunc 𝕜) (c : ℕ)
    (h : uniformizer ω ^ c * x ∈ regularAt ω) :
    rootMultiplicity ω x.denom ≤ c := by
  obtain ⟨f, g, hg, he⟩ := h
  let u : 𝕜[X] := (X - C ω) ^ c
  have hu : u ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero ω)
  have hg0 : g ≠ 0 := by intro hzero; exact hg (by simp [hzero])
  have hug : u * g ≠ 0 := mul_ne_zero hu hg0
  have hgm : algebraMap 𝕜[X] (RatFunc 𝕜) g ≠ 0 := RatFunc.algebraMap_ne_zero hg0
  have hugm : algebraMap 𝕜[X] (RatFunc 𝕜) (u * g) ≠ 0 := RatFunc.algebraMap_ne_zero hug
  have hpresent : x = algebraMap 𝕜[X] (RatFunc 𝕜) f /
      algebraMap 𝕜[X] (RatFunc 𝕜) (u * g) := by
    apply (eq_div_iff hugm).mpr
    have hh := (eq_div_iff hgm).mp he
    calc x * algebraMap 𝕜[X] (RatFunc 𝕜) (u * g) =
        (uniformizer ω ^ c * x) * algebraMap 𝕜[X] (RatFunc 𝕜) g := by
          simp only [map_mul, u, map_pow, uniformizer]
          ring
      _ = _ := hh
  have hdvd : x.denom ∣ u * g := (RatFunc.denom_dvd hug).mpr ⟨f, hpresent⟩
  have hb := rootMultiplicity_le_rootMultiplicity_of_dvd hug hdvd ω
  rw [rootMultiplicity_mul hug] at hb
  have hgu : rootMultiplicity ω g = 0 := rootMultiplicity_eq_zero hg
  simpa only [u, rootMultiplicity_X_sub_C_pow, hgu, add_zero] using hb

theorem exists_polynomial_multiple_of_denom_dvd (x : RatFunc 𝕜) (D : 𝕜[X])
    (hD : x.denom ∣ D) :
    ∃ P : 𝕜[X], algebraMap 𝕜[X] (RatFunc 𝕜) D * x = algebraMap 𝕜[X] (RatFunc 𝕜) P := by
  obtain ⟨A, hA⟩ := hD
  refine ⟨A * x.num, ?_⟩
  rw [hA, map_mul, map_mul]
  have hden : algebraMap 𝕜[X] (RatFunc 𝕜) x.denom ≠ 0 :=
    RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero x)
  conv_lhs => arg 2; rw [← RatFunc.num_div_denom x]
  field_simp

/-- Over an algebraically closed field, a rational function regular at every `ω ≠ 0` becomes a
polynomial after multiplication by a power of `X`. -/
theorem exists_polynomial_multiple_of_regular [IsAlgClosed 𝕜] (x : RatFunc 𝕜)
    (hlocal : ∀ ω : 𝕜, ω ≠ 0 → x ∈ regularAt ω) :
    ∃ m : ℕ, ∃ P : 𝕜[X], algebraMap 𝕜[X] (RatFunc 𝕜) (X ^ m) * x =
      algebraMap 𝕜[X] (RatFunc 𝕜) P := by
  classical
  let m := rootMultiplicity (0 : 𝕜) x.denom
  have hX : (X : 𝕜[X]) ^ m ≠ 0 := pow_ne_zero _ X_ne_zero
  have hmul : x.denom ∣ (X : 𝕜[X]) ^ m := by
    apply (IsAlgClosed.splits x.denom).dvd_of_roots_le_roots (RatFunc.denom_ne_zero x)
    apply Multiset.le_iff_count.mpr
    intro ω
    simp only [Polynomial.count_roots]
    by_cases hω : ω = 0
    · subst ω
      have hm : rootMultiplicity (0 : 𝕜) ((X : 𝕜[X]) ^ m) = m := by
        simpa only [map_zero, sub_zero] using rootMultiplicity_X_sub_C_pow (0 : 𝕜) m
      rw [hm]
    · have h0 := denom_rootMultiplicity_le_of_regular ω x 0 (by simpa using hlocal ω hω)
      omega
  exact ⟨m, exists_polynomial_multiple_of_denom_dvd x _ hmul⟩

/-! ### Regularity away from the special roots of unity -/

theorem alpha_sq (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (k : ℕ) :
    (alpha ε ω k) ^ 2 = ω ^ (4 * k + 2) := by
  have h : (alpha ε ω k) ^ 2 = ((ε : 𝕜) ^ 2) ^ (k + 1) * ω ^ (4 * k + 2) := by
    rw [alpha, wpar_pow]; ring
  rw [h, eps_cast_sq hε, one_pow, one_mul]

theorem w_pow_sq (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (n : ℕ) :
    ((wpar ε ω) ^ n) ^ 2 = ω ^ (4 * n) := by
  have h : ((wpar ε ω) ^ n) ^ 2 = ((ε : 𝕜) ^ 2) ^ n * ω ^ (4 * n) := by
    rw [wpar_pow]; ring
  rw [h, eps_cast_sq hε, one_pow, one_mul]

/-- The local ring at a point `ω ≠ 0` that is neither a W- nor an α-root contains every
coefficient of the generic determinant. -/
theorem localizationData_regularAt (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω : ω ≠ 0) (K : ℕ)
    (hgeom : ∀ n ∈ Icc 1 K, (wpar ε ω) ^ n ≠ 1)
    (halpha : ∀ k ∈ Icc 1 (K - 2), alpha ε ω k ≠ 1) :
    LocalizationData (regularAt ω) ε RatFunc.X K where
  sign := hε
  base_mem := base_mem_regularAt ω
  inv_base_mem := inv_base_mem_regularAt ω hω
  inv_geom_mem n hn := by
    have h := inv_polynomial_mem_regularAt ω (1 - ((ε : 𝕜[X]) * X ^ 2) ^ n)
      (by simp only [eval_sub, eval_one, eval_pow, eval_mul, eval_intCast, eval_X]
          exact sub_ne_zero.mpr (Ne.symm (hgeom n hn)))
    simpa [RatFunc.algebraMap_X, wpar] using h
  inv_alpha_mem k hk := by
    have h := inv_polynomial_mem_regularAt ω
      (1 - ((ε : 𝕜[X]) * X) * ((ε : 𝕜[X]) * X ^ 2) ^ k)
      (by simp only [eval_sub, eval_one, eval_mul, eval_pow, eval_intCast, eval_X]
          exact sub_ne_zero.mpr (Ne.symm (halpha k hk)))
    simpa [RatFunc.algebraMap_X, alpha, wpar] using h

/-- At a point that is not a root of unity of order `≤ 4K`, every coefficient is regular. -/
theorem localizationData_of_not_root (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω : ω ≠ 0) (K : ℕ)
    (hroot : ∀ n ∈ Icc 1 (4 * K), ω ^ n ≠ 1) :
    LocalizationData (regularAt ω) ε RatFunc.X K := by
  apply localizationData_regularAt hε ω hω K
  · intro n hn h1
    apply hroot (4 * n) (mem_Icc.mpr ⟨by have := (mem_Icc.mp hn).1; omega,
      by have := (mem_Icc.mp hn).2; omega⟩)
    rw [← w_pow_sq hε, h1, one_pow]
  · intro k hk h1
    apply hroot (4 * k + 2) (mem_Icc.mpr ⟨by omega,
      by have := (mem_Icc.mp hk).2; have := (mem_Icc.mp hk).1; omega⟩)
    rw [← alpha_sq hε, h1, one_pow]

/-! ### The clearing polynomial -/

theorem CKpoly_map (K : ℕ) :
    (CKpoly ε K).map (Int.castRingHom 𝕜) = ∏ d ∈ Icc 1 (4 * K), (cyclotomic d 𝕜) ^ nExp ε K d := by
  simp [CKpoly, Polynomial.map_prod, Polynomial.map_cyclotomic]

theorem uniformizer_pow_dvd_CKpoly (K d : ℕ) (hd : d ∈ Icc 1 (4 * K))
    (ω : 𝕜) (hω : IsPrimitiveRoot ω d) :
    (X - C ω) ^ nExp ε K d ∣ (CKpoly ε K).map (Int.castRingHom 𝕜) := by
  rw [CKpoly_map]
  exact (pow_dvd_pow_of_dvd
    (Polynomial.dvd_iff_isRoot.mpr (hω.isRoot_cyclotomic (mem_Icc.mp hd).1)) _).trans
    (Finset.dvd_prod_of_mem (fun e => (cyclotomic e 𝕜) ^ nExp ε K e) hd)

/-- The hypothesis of the descent: the local bound of Propositions 3.2 / Lemma 3.3. -/
def LocalBounds (ε : ℤ) (𝕜 : Type*) [Field 𝕜] : Prop :=
  ∀ K i d : ℕ, d ∈ Icc 1 (4 * K) → ∀ ω : 𝕜, IsPrimitiveRoot ω d →
    uniformizer ω ^ nExp ε K d * (Delta ε (RatFunc.X : RatFunc 𝕜) K).coeff i ∈ regularAt ω

theorem CKpoly_mul_regular (hε : ε = 1 ∨ ε = -1) (hb : LocalBounds ε 𝕜) (K i : ℕ) (ω : 𝕜) (hω : ω ≠ 0) :
    intPolynomialMap (𝕜 := 𝕜) (CKpoly ε K) * (Delta ε (RatFunc.X : RatFunc 𝕜) K).coeff i ∈
      regularAt ω := by
  classical
  by_cases hroot : ∃ n ∈ Icc 1 (4 * K), ω ^ n = 1
  · obtain ⟨n, hn, hpow⟩ := hroot
    have hdvd := orderOf_dvd_of_pow_eq_one hpow
    have hdpos : 0 < orderOf ω := Nat.pos_of_dvd_of_pos hdvd (mem_Icc.mp hn).1
    have hd : orderOf ω ∈ Icc 1 (4 * K) :=
      mem_Icc.mpr ⟨hdpos, (Nat.le_of_dvd (mem_Icc.mp hn).1 hdvd).trans (mem_Icc.mp hn).2⟩
    obtain ⟨A, hA⟩ := uniformizer_pow_dvd_CKpoly K (orderOf ω) hd ω (IsPrimitiveRoot.orderOf ω)
    have hr := (regularAt ω).mul_mem (polynomial_mem_regularAt ω A)
      (hb K i (orderOf ω) hd ω (IsPrimitiveRoot.orderOf ω))
    convert hr using 1
    rw [intPolynomialMap_apply, hA, map_mul, map_pow]
    simp only [uniformizer]
    ring
  · push Not at hroot
    exact (regularAt ω).mul_mem (polynomial_mem_regularAt ω _)
      ((localizationData_of_not_root hε ω hω K hroot).Delta_coeff_mem i)

/-- Global Gauss descent. -/
theorem exists_integer_laurent [CharZero 𝕜] [IsAlgClosed 𝕜] (hε : ε = 1 ∨ ε = -1) (hb : LocalBounds ε 𝕜) (K i : ℕ) :
    ∃ m : ℕ, ∃ A : ℤ[X],
      intPolynomialMap (𝕜 := 𝕜) (X ^ m) *
        (intPolynomialMap (CKpoly ε K) * (Delta ε (RatFunc.X : RatFunc 𝕜) K).coeff i) =
          intPolynomialMap A := by
  set x := intPolynomialMap (𝕜 := 𝕜) (CKpoly ε K) * (Delta ε (RatFunc.X : RatFunc 𝕜) K).coeff i
  have hx : x ∈ integerMonicFractions := integerMonicFractions.mul_mem
    (integerPolynomial_mem _) (Delta_coeff_integerMonicFraction hε K i)
  obtain ⟨m, P, hP⟩ := exists_polynomial_multiple_of_regular x
    (fun ω hω => CKpoly_mul_regular hε hb K i ω hω)
  have hP' : intPolynomialMap (𝕜 := 𝕜) (X ^ m) * x = algebraMap 𝕜[X] (RatFunc 𝕜) P := by
    simpa [intPolynomialMap] using hP
  obtain ⟨A, hA⟩ := polynomial_of_integerMonicFraction _
    (integerMonicFractions.mul_mem (integerPolynomial_mem _) hx) P hP'
  exact ⟨m, A, hA⟩

/-! ### Specialization at a real non-root of unity -/

theorem localEval_intPolynomialMap (ω : 𝕜) (A : ℤ[X]) :
    localEval ω ⟨intPolynomialMap A, polynomial_mem_regularAt ω _⟩ = aeval ω A := by
  rw [localEval_apply]
  change RatFunc.eval (RingHom.id 𝕜) ω
    (algebraMap 𝕜[X] (RatFunc 𝕜) (A.map (Int.castRingHom 𝕜))) = _
  rw [RatFunc.eval_algebraMap, aeval_def, Algebra.algebraMap_self, RingHom.id_apply, eval₂_id,
    eval_map, algebraMap_int_eq]

theorem complex_pow_ne_one {τ : ℝ} (hτ1 : ∀ m : ℕ, 0 < m → τ ^ m ≠ 1) :
    ∀ m : ℕ, 0 < m → (τ : ℂ) ^ m ≠ 1 := by
  intro m hm h
  apply hτ1 m hm
  exact_mod_cast h

/-- **Proposition 3.4**, assuming the local bounds. -/
theorem integrality_of_local_bounds (hε : ε = 1 ∨ ε = -1) (hb : LocalBounds ε ℂ) :
    Integrality ε := by
  intro K i
  obtain ⟨m, A, hA⟩ := exists_integer_laurent hε hb K i
  refine ⟨m, A, fun τ hτ0 hτ1 => ?_⟩
  have hτ0' : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ0
  have hloc := localizationData_of_not_root hε (τ : ℂ) hτ0' K
    (fun n hn => complex_pow_ne_one hτ1 n (mem_Icc.mp hn).1)
  let R := regularAt (τ : ℂ)
  let u : R := ⟨intPolynomialMap (X ^ m), polynomial_mem_regularAt _ _⟩
  let v : R := ⟨intPolynomialMap (CKpoly ε K), polynomial_mem_regularAt _ _⟩
  let c : R := ⟨(Delta ε (RatFunc.X : RatFunc ℂ) K).coeff i, hloc.Delta_coeff_mem i⟩
  let a : R := ⟨intPolynomialMap A, polynomial_mem_regularAt _ _⟩
  have he : u * (v * c) = a := Subtype.ext hA
  have heval := congrArg (localEval (τ : ℂ)) he
  rw [map_mul, map_mul] at heval
  have hc : localEval (τ : ℂ) c = ((Delta ε τ K).coeff i : ℂ) := by
    have h1 := Specialization.specialize_Delta_coeff hloc (localEval (τ : ℂ)) i
    rw [show localEval (τ : ℂ) ⟨RatFunc.X, hloc.base_mem⟩ = (τ : ℂ) from localEval_base _] at h1
    rw [show c = ⟨(Delta ε (RatFunc.X : RatFunc ℂ) K).coeff i, hloc.Delta_coeff_mem i⟩ from rfl, h1]
    have h2 := congrArg (fun f => Polynomial.coeff f i)
      (Specialization.map_Delta hε Complex.ofRealHom τ K)
    simp only [Polynomial.coeff_map, Complex.ofRealHom_eq_coe] at h2
    exact h2.symm
  rw [hc, show u = ⟨intPolynomialMap (X ^ m), _⟩ from rfl, localEval_intPolynomialMap,
    show v = ⟨intPolynomialMap (CKpoly ε K), _⟩ from rfl, localEval_intPolynomialMap,
    show a = ⟨intPolynomialMap A, _⟩ from rfl, localEval_intPolynomialMap] at heval
  have hreal : τ ^ m * (aeval τ (CKpoly ε K) * (Delta ε τ K).coeff i) = aeval τ A := by
    have e1 : (aeval (τ : ℂ) (X ^ m : ℤ[X])) = ((τ ^ m : ℝ) : ℂ) := by simp
    have e2 : aeval (τ : ℂ) (CKpoly ε K) = ((aeval τ (CKpoly ε K) : ℝ) : ℂ) :=
      aeval_algebraMap_apply ℂ τ (CKpoly ε K)
    have e3 : aeval (τ : ℂ) A = ((aeval τ A : ℝ) : ℂ) := aeval_algebraMap_apply ℂ τ A
    rw [e1, e2, e3] at heval
    exact_mod_cast heval
  have hτm : τ ^ m ≠ 0 := pow_ne_zero _ hτ0
  rw [← hreal]
  field_simp

end LucasU.Denom
