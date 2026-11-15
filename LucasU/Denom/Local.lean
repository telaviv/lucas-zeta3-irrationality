/-
Generalised from lean_fibzeta FibZeta/Denom/Local.lean (ε = ±1, general t).
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/CyclotomicLocal.lean and
lean/QZeta3/LocalEvaluation.lean (Apache-2.0, Lean formalisation by F. Solomon Admasu). Changes: only the
construction-independent part (local ring, uniformizer, evaluation) is kept; namespace renamed.
-/
import LucasU.Denom.Localization
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Rational functions regular at a point

The local ring at `ω` is described by polynomial fractions whose denominator does not vanish at
`ω`.  Pole clearing is stated as membership after multiplication by a power of the uniformizer
`X − ω` (PROOF §3.1, "Local setting").
-/

open Polynomial

namespace LucasU.Denom

variable {𝕜 : Type*} [Field 𝕜]

/-- A rational function is regular at `ω` if it has a polynomial fraction presentation with
denominator nonzero at `ω`. -/
def RegularAt (ω : 𝕜) (x : RatFunc 𝕜) : Prop :=
  ∃ f g : 𝕜[X], g.eval ω ≠ 0 ∧ x = algebraMap 𝕜[X] (RatFunc 𝕜) f /
    algebraMap 𝕜[X] (RatFunc 𝕜) g

private theorem map_ne_zero_of_eval_ne_zero (ω : 𝕜) (g : 𝕜[X]) (hg : g.eval ω ≠ 0) :
    algebraMap 𝕜[X] (RatFunc 𝕜) g ≠ 0 := by
  apply RatFunc.algebraMap_ne_zero
  intro heq
  exact hg (by rw [heq, Polynomial.eval_zero])

/-- The local subring of rational functions regular at `ω`. -/
def regularAt (ω : 𝕜) : Subring (RatFunc 𝕜) where
  carrier := {x | RegularAt ω x}
  zero_mem' := ⟨0, 1, by simp, by simp⟩
  one_mem' := ⟨1, 1, by simp, by simp⟩
  neg_mem' := by
    rintro x ⟨f, g, hg, rfl⟩
    exact ⟨-f, g, hg, by rw [map_neg, neg_div]⟩
  add_mem' := by
    rintro x y ⟨f, g, hg, rfl⟩ ⟨u, v, hv, rfl⟩
    refine ⟨f * v + u * g, g * v, ?_, ?_⟩
    · simpa only [Polynomial.eval_mul] using mul_ne_zero hg hv
    · rw [map_add, map_mul, map_mul, map_mul]
      have hg0 := map_ne_zero_of_eval_ne_zero ω g hg
      have hv0 := map_ne_zero_of_eval_ne_zero ω v hv
      field_simp
  mul_mem' := by
    rintro x y ⟨f, g, hg, rfl⟩ ⟨u, v, hv, rfl⟩
    refine ⟨f * u, g * v, ?_, ?_⟩
    · simpa only [Polynomial.eval_mul] using mul_ne_zero hg hv
    · rw [map_mul, map_mul, div_mul_div_comm]

@[simp] theorem mem_regularAt (ω : 𝕜) (x : RatFunc 𝕜) :
    x ∈ regularAt ω ↔ RegularAt ω x := Iff.rfl

theorem polynomial_mem_regularAt (ω : 𝕜) (f : 𝕜[X]) :
    algebraMap 𝕜[X] (RatFunc 𝕜) f ∈ regularAt ω := ⟨f, 1, by simp, by simp⟩

theorem inv_polynomial_mem_regularAt (ω : 𝕜) (f : 𝕜[X]) (hf : f.eval ω ≠ 0) :
    (algebraMap 𝕜[X] (RatFunc 𝕜) f)⁻¹ ∈ regularAt ω :=
  ⟨1, f, hf, by simp⟩

theorem C_mem_regularAt (ω c : 𝕜) : RatFunc.C c ∈ regularAt ω := by
  simpa only [RatFunc.algebraMap_C] using polynomial_mem_regularAt ω (C c)

/-- The local uniformizer `X − ω`. -/
noncomputable def uniformizer (ω : 𝕜) : RatFunc 𝕜 :=
  algebraMap 𝕜[X] (RatFunc 𝕜) (X - C ω)

theorem uniformizer_mem (ω : 𝕜) : uniformizer ω ∈ regularAt ω :=
  polynomial_mem_regularAt ω _

theorem uniformizer_ne_zero (ω : 𝕜) : uniformizer ω ≠ 0 := by
  apply RatFunc.algebraMap_ne_zero
  exact Polynomial.X_sub_C_ne_zero ω

@[simp] theorem uniformizer_eq (ω : 𝕜) : uniformizer ω = RatFunc.X - RatFunc.C ω := by
  simp [uniformizer, RatFunc.algebraMap_X, RatFunc.algebraMap_C]

/-- A simple zero cancels with one uniformizer factor. -/
theorem uniformizer_div_mem_of_simple_root (ω : 𝕜) (f : 𝕜[X])
    (hf : f.eval ω = 0) (hder : (derivative f).eval ω ≠ 0) :
    uniformizer ω / algebraMap 𝕜[X] (RatFunc 𝕜) f ∈ regularAt ω := by
  let q := f /ₘ (X - C ω)
  have hq : f = (X - C ω) * q := ((Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hf).symm
  have hqe : q.eval ω ≠ 0 := by
    rw [hq, Polynomial.derivative_mul, Polynomial.derivative_sub,
      Polynomial.derivative_X, Polynomial.derivative_C] at hder
    simpa using hder
  have hu := uniformizer_ne_zero ω
  rw [hq, map_mul]
  change uniformizer ω / (uniformizer ω * algebraMap 𝕜[X] (RatFunc 𝕜) q) ∈ regularAt ω
  rw [div_mul_eq_div_mul_one_div, div_self hu, one_mul]
  simpa only [one_div] using inv_polynomial_mem_regularAt ω q hqe

/-- A vanishing polynomial has a regular quotient by the uniformizer. -/
theorem polynomial_div_uniformizer_mem (ω : 𝕜) (f : 𝕜[X]) (hf : f.eval ω = 0) :
    algebraMap 𝕜[X] (RatFunc 𝕜) f / uniformizer ω ∈ regularAt ω := by
  have hq : f = (X - C ω) * (f /ₘ (X - C ω)) :=
    ((Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hf).symm
  rw [hq, map_mul]
  change uniformizer ω * algebraMap 𝕜[X] (RatFunc 𝕜) (f /ₘ (X - C ω)) / uniformizer ω ∈
    regularAt ω
  rw [mul_div_cancel_left₀ _ (uniformizer_ne_zero ω)]
  exact polynomial_mem_regularAt ω _

theorem base_mem_regularAt (ω : 𝕜) : (RatFunc.X : RatFunc 𝕜) ∈ regularAt ω := by
  simpa only [RatFunc.algebraMap_X] using polynomial_mem_regularAt ω X

theorem inv_base_mem_regularAt (ω : 𝕜) (hω : ω ≠ 0) :
    (RatFunc.X : RatFunc 𝕜)⁻¹ ∈ regularAt ω := by
  simpa only [RatFunc.algebraMap_X] using inv_polynomial_mem_regularAt ω X (by simpa using hω)

/-- Polynomial evaluation preserves local regularity. -/
theorem eval_mem_regularAt (ω : 𝕜) (f : (RatFunc 𝕜)[X])
    (hf : ∀ i, f.coeff i ∈ regularAt ω) (x : RatFunc 𝕜) (hx : x ∈ regularAt ω) :
    f.eval x ∈ regularAt ω := by
  rw [Polynomial.eval_eq_sum_range]
  exact (regularAt ω).sum_mem fun i _ =>
    (regularAt ω).mul_mem (hf i) ((regularAt ω).pow_mem hx i)

/-- A bound for a smaller clearing exponent also clears at every larger exponent. -/
theorem uniformizer_pow_mul_mem_of_le (ω : 𝕜) (x : RatFunc 𝕜) {a b : ℕ}
    (hab : a ≤ b) (h : uniformizer ω ^ a * x ∈ regularAt ω) :
    uniformizer ω ^ b * x ∈ regularAt ω := by
  have hm := (regularAt ω).mul_mem ((regularAt ω).pow_mem (uniformizer_mem ω) (b - a)) h
  convert hm using 1
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hab]

/-! ### Evaluation on the local ring -/

theorem regularAt_iff_denom_eval_ne_zero (ω : 𝕜) (x : RatFunc 𝕜) :
    x ∈ regularAt ω ↔ x.denom.eval ω ≠ 0 := by
  constructor
  · rintro ⟨A, B, hB, rfl⟩ hzero
    exact hB (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero
      (RatFunc.denom_div_dvd A B) hzero)
  · intro hx
    exact ⟨x.num, x.denom, hx, (RatFunc.num_div_denom x).symm⟩

/-- Evaluation at `ω` as a ring homomorphism on the local ring. -/
noncomputable def localEval (ω : 𝕜) : regularAt ω →+* 𝕜 where
  toFun x := RatFunc.eval (RingHom.id 𝕜) ω x.val
  map_one' := RatFunc.eval_one _ _
  map_zero' := RatFunc.eval_zero _ _
  map_add' x y := by
    apply RatFunc.eval_add
    · simpa only [Polynomial.eval₂_id] using
        (regularAt_iff_denom_eval_ne_zero ω x.val).mp x.property
    · simpa only [Polynomial.eval₂_id] using
        (regularAt_iff_denom_eval_ne_zero ω y.val).mp y.property
  map_mul' x y := by
    apply RatFunc.eval_mul
    · simpa only [Polynomial.eval₂_id] using
        (regularAt_iff_denom_eval_ne_zero ω x.val).mp x.property
    · simpa only [Polynomial.eval₂_id] using
        (regularAt_iff_denom_eval_ne_zero ω y.val).mp y.property

@[simp] theorem localEval_apply (ω : 𝕜) (x : regularAt ω) :
    localEval ω x = RatFunc.eval (RingHom.id 𝕜) ω x.val := rfl

theorem inv_mem_regularAt_of_eval_ne_zero (ω : 𝕜) (x : RatFunc 𝕜)
    (hx : RatFunc.eval (RingHom.id 𝕜) ω x ≠ 0) : x⁻¹ ∈ regularAt ω := by
  have hn : x.num.eval ω ≠ 0 := by
    intro hn
    apply hx
    simp [RatFunc.eval, hn]
  refine ⟨x.denom, x.num, hn, ?_⟩
  conv_lhs => rw [← RatFunc.num_div_denom x]
  rw [inv_div]

/-- A local element with nonzero residue is a unit in the local ring. -/
theorem isUnit_of_localEval_ne_zero (ω : 𝕜) (x : regularAt ω)
    (hx : localEval ω x ≠ 0) : IsUnit x := by
  have hxi := inv_mem_regularAt_of_eval_ne_zero ω x.val hx
  have hx0 : x.val ≠ 0 := by
    intro hx0
    apply hx
    simp [localEval, hx0]
  refine ⟨⟨x, ⟨x.val⁻¹, hxi⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    exact mul_inv_cancel₀ hx0
  · apply Subtype.ext
    exact inv_mul_cancel₀ hx0

theorem localEval_base (ω : 𝕜) :
    localEval ω ⟨RatFunc.X, base_mem_regularAt ω⟩ = ω := by
  simp

end LucasU.Denom
