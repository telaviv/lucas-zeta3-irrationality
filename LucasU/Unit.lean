import LucasU.Statements

-- Generalised from lean_fibzeta FibZeta/Main.lean (the facts about t, φ and Binet, here for a general quadratic unit).

/-!
# The quadratic unit `α`, its inverse `t`, the conjugate `σt = ε/t`, Binet, and `√D ∉ ℚ`

For admissible `(a, E)` (`E = 1, a ≥ 1` or `E = −1, a ≥ 3`), with `ε = −E`, `D = a² + 4E`,
`α = (a + √D)/2`, `t = 1/α`:

* `α² = a α + E`, `t² + aE t − E = 0`, `t (ε/t) = ε`, `t + ε/t = −aE`;
* `√D = a + 2E t` and `a + 2E (ε/t) = −√D`;
* `U_n = (αⁿ − (ε t)ⁿ)/√D` (Binet), hence `1/U_n³ = D √D ψ_n(t)` and `∑ 1/U_n³ = D √D Ξ`;
* `D` is not a perfect square, so `√D` is irrational;
* `0 < t ≤ φ⁻¹`, so `Good (−E) t` holds.
-/

open Polynomial Finset

namespace LucasU

variable {a : ℕ} {E : ℤ}

theorem E_sq (hA : Admissible a E) : E ^ 2 = 1 := by
  rcases hA with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num

theorem E_cases (hA : Admissible a E) : E = 1 ∨ E = -1 := by
  rcases hA with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]

theorem discr_pos (hA : Admissible a E) : 0 < discr a E := by
  unfold discr
  rcases hA with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
  · positivity
  · have : (3 : ℤ) ≤ a := by exact_mod_cast ha
    nlinarith

/-- `D = a² + 4E` is not a perfect square. -/
theorem discr_not_sq (hA : Admissible a E) (m : ℤ) : m ^ 2 ≠ discr a E := by
  intro h
  unfold discr at h
  have hm : m ^ 2 = |m| ^ 2 := (sq_abs m).symm
  rw [hm] at h
  set n := |m| with hn
  have hn0 : 0 ≤ n := abs_nonneg m
  rcases hA with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
  · have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
    -- a² < n² < (a+2)², so n = a + 1, then 2a + 1 = 4
    have h1 : (a : ℤ) < n := by nlinarith
    have h2 : n < (a : ℤ) + 2 := by nlinarith
    have h3 : n = (a : ℤ) + 1 := by omega
    rw [h3] at h
    have : 2 * (a : ℤ) = 3 := by nlinarith
    omega
  · have ha' : (3 : ℤ) ≤ a := by exact_mod_cast ha
    have h1 : n < (a : ℤ) := by nlinarith
    have h2 : (a : ℤ) - 2 < n := by nlinarith
    have h3 : n = (a : ℤ) - 1 := by omega
    rw [h3] at h
    have : 2 * (a : ℤ) = 5 := by nlinarith
    omega

theorem sqrtD_irrational (hA : Admissible a E) : Irrational √((discr a E : ℤ) : ℝ) := by
  have hD := discr_pos hA
  rw [irrational_sqrt_intCast_iff_of_nonneg hD.le]
  rintro ⟨m, hm⟩
  exact discr_not_sq hA m (by rw [hm]; ring)

/-- Shorthand for `√D`. -/
noncomputable abbrev sD (a : ℕ) (E : ℤ) : ℝ := √((discr a E : ℤ) : ℝ)

theorem sD_sq (hA : Admissible a E) : sD a E ^ 2 = (discr a E : ℝ) := by
  rw [Real.sq_sqrt]; exact_mod_cast (discr_pos hA).le

theorem sD_pos (hA : Admissible a E) : 0 < sD a E :=
  Real.sqrt_pos.mpr (by exact_mod_cast discr_pos hA)

theorem alphaR_sq (hA : Admissible a E) : alphaR a E ^ 2 = a * alphaR a E + E := by
  have h := sD_sq hA
  unfold alphaR; unfold discr at h; push_cast at h
  linear_combination h / 4

/-- `α ≥ φ`. -/
theorem gold_le_alphaR (hA : Admissible a E) : Real.goldenRatio ≤ alphaR a E := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs := sD_pos hA
  have hsq := sD_sq hA
  unfold alphaR Real.goldenRatio
  unfold discr at hsq; push_cast at hsq
  have h5le : √5 ≤ √((discr a E : ℤ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    unfold discr
    rcases hA with ⟨rfl, ha⟩ | ⟨rfl, ha⟩
    · have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
      push_cast; nlinarith
    · have ha' : (3 : ℝ) ≤ a := by exact_mod_cast ha
      push_cast; nlinarith
  have ha1 : (1 : ℝ) ≤ a := by
    rcases hA with ⟨-, ha⟩ | ⟨-, ha⟩
    · exact_mod_cast ha
    · have : (3 : ℝ) ≤ a := by exact_mod_cast ha
      linarith
  linarith

theorem alphaR_pos (hA : Admissible a E) : 0 < alphaR a E :=
  lt_of_lt_of_le Real.goldenRatio_pos (gold_le_alphaR hA)

theorem one_lt_alphaR (hA : Admissible a E) : 1 < alphaR a E :=
  lt_of_lt_of_le Real.one_lt_goldenRatio (gold_le_alphaR hA)

theorem tU_pos (hA : Admissible a E) : 0 < tU a E := inv_pos.mpr (alphaR_pos hA)

theorem tU_lt_one (hA : Admissible a E) : tU a E < 1 := inv_lt_one_of_one_lt₀ (one_lt_alphaR hA)

theorem tU_le_inv_gold (hA : Admissible a E) : tU a E ≤ Real.goldenRatio⁻¹ :=
  inv_anti₀ Real.goldenRatio_pos (gold_le_alphaR hA)

theorem good_tU (hA : Admissible a E) : Good (-E) (tU a E) := by
  refine ⟨?_, tU_pos hA, tU_le_inv_gold hA⟩
  rcases E_cases hA with h | h <;> simp [h]

theorem tU_mul_alphaR (hA : Admissible a E) : tU a E * alphaR a E = 1 :=
  inv_mul_cancel₀ (alphaR_pos hA).ne'

/-- `t² + aE t − E = 0`. -/
theorem tU_quad (hA : Admissible a E) : tU a E ^ 2 + a * E * tU a E - E = 0 := by
  have hα := alphaR_sq hA
  have hm := tU_mul_alphaR hA
  have hE : (E : ℝ) ^ 2 = 1 := by exact_mod_cast E_sq hA
  set t := tU a E; set α := alphaR a E
  -- divide `α² = aα + E` by `α²`, then multiply by `E`
  have h1 : 1 = a * t + E * t ^ 2 := by
    linear_combination t ^ 2 * hα - (1 + t * α) * hm + a * t * hm
  linear_combination (-E) * h1 - t ^ 2 * hE

/-- The conjugate `σt = ε/t` with `ε = −E`; it equals `−E α`. -/
theorem sigma_eq (hA : Admissible a E) : ((-E : ℤ) : ℝ) / tU a E = -E * alphaR a E := by
  unfold tU; push_cast; rw [div_inv_eq_mul]

theorem sigma_quad (hA : Admissible a E) :
    (((-E : ℤ) : ℝ) / tU a E) ^ 2 + a * E * (((-E : ℤ) : ℝ) / tU a E) - E = 0 := by
  rw [sigma_eq hA]
  have hα := alphaR_sq hA
  have hE : (E : ℝ) ^ 2 = 1 := by exact_mod_cast E_sq hA
  linear_combination (E : ℝ) ^ 2 * hα + (E : ℝ) * hE


/-! ### Binet -/

theorem sD_eq (hA : Admissible a E) : sD a E = 2 * alphaR a E - a := by
  unfold alphaR; ring

/-- `ᾱ := a − α` satisfies the same quadratic. -/
theorem alphaBar_sq (hA : Admissible a E) :
    ((a : ℝ) - alphaR a E) ^ 2 = a * ((a : ℝ) - alphaR a E) + E := by
  have hα := alphaR_sq hA
  linear_combination hα

/-- `ᾱ = −E t` (as `α ᾱ = −E`). -/
theorem alphaBar_eq (hA : Admissible a E) : (a : ℝ) - alphaR a E = -E * tU a E := by
  have hsq := sD_sq hA
  have hm := tU_mul_alphaR hA
  have hα0 := (alphaR_pos hA).ne'
  -- α (a − α) = (a² − D)/4 = −E
  have hprod : alphaR a E * ((a : ℝ) - alphaR a E) = -E := by
    have hα := alphaR_sq hA
    linear_combination -hα
  have ht : tU a E = (alphaR a E)⁻¹ := rfl
  rw [ht]
  field_simp
  linear_combination hprod

/-- Binet: `U_n = (αⁿ − ᾱⁿ)/√D`. -/
theorem Useq_binet (hA : Admissible a E) (n : ℕ) :
    (Useq a E n : ℝ) = (alphaR a E ^ n - ((a : ℝ) - alphaR a E) ^ n) / sD a E := by
  have hs := (sD_pos hA).ne'
  have hα := alphaR_sq hA
  have hβ := alphaBar_sq hA
  set α := alphaR a E
  set β := (a : ℝ) - alphaR a E
  have key : ∀ n : ℕ, (Useq a E n : ℝ) * sD a E = α ^ n - β ^ n ∧
      (Useq a E (n + 1) : ℝ) * sD a E = α ^ (n + 1) - β ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨by simp [Useq], ?_⟩
      simp only [Useq, Int.cast_one, one_mul, zero_add, pow_one]
      rw [sD_eq hA]; simp only [β]; ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have e : (Useq a E (n + 1 + 1) : ℝ) = a * Useq a E (n + 1) + E * Useq a E n := by
        simp [Useq]
      rw [e, add_mul, mul_assoc, mul_assoc, ih.2, ih.1]
      have hα' : α ^ (n + 2) = a * α ^ (n + 1) + E * α ^ n := by
        rw [pow_add α n 2, hα]; ring
      have hβ' : β ^ (n + 2) = a * β ^ (n + 1) + E * β ^ n := by
        rw [pow_add β n 2, hβ]; ring
      rw [show n + 1 + 1 = n + 2 by ring, hα', hβ']; ring
  rw [eq_div_iff hs]; exact (key n).1

/-- `1/U_n³ = D √D ψ_n(t)` (also for `n = 0`, where both sides are `0`). -/
theorem one_div_U_cube (hA : Admissible a E) (n : ℕ) :
    1 / ((Useq a E n : ℤ) : ℝ) ^ 3 = (discr a E : ℝ) * sD a E * psi (-E) (tU a E) n := by
  have hs := sD_pos hA
  have hsq := sD_sq hA
  have ht := tU_pos hA
  have hm := tU_mul_alphaR hA
  rw [Useq_binet hA, alphaBar_eq hA, psi, wpar]
  have hα : alphaR a E = (tU a E)⁻¹ := by
    rw [← mul_eq_one_iff_eq_inv₀ ht.ne', mul_comm]; exact hm
  rw [hα]
  set t := tU a E
  have hpow : (-(E : ℝ) * t) ^ n = (((-E : ℤ) : ℝ) * t ^ 2) ^ n * (t⁻¹) ^ n := by
    rw [← mul_pow]; congr 1; push_cast; field_simp
  rw [hpow]
  have hfac : ((t⁻¹) ^ n - (((-E : ℤ) : ℝ) * t ^ 2) ^ n * (t⁻¹) ^ n) / sD a E =
      (t⁻¹) ^ n * (1 - (((-E : ℤ) : ℝ) * t ^ 2) ^ n) / sD a E := by ring
  rw [hfac]
  by_cases h1 : (1 - (((-E : ℤ) : ℝ) * t ^ 2) ^ n) = 0
  · rw [h1]; simp
  · have htn : t ^ n ≠ 0 := pow_ne_zero _ ht.ne'
    have h3 : sD a E ^ 3 = (discr a E : ℝ) * sD a E := by rw [pow_succ, hsq]
    rw [div_pow, mul_pow, h3]
    simp only [inv_pow]
    field_simp
    ring

/-- `∑ 1/U_n³ = D √D Ξ`. -/
theorem zetaU_eq (hA : Admissible a E) :
    zetaU a E = (discr a E : ℝ) * sD a E * XiR (-E) (tU a E) := by
  unfold zetaU XiR
  rw [← tsum_mul_left]
  congr 1
  funext n
  exact one_div_U_cube hA (n + 1)

/-- `√D = a + 2E t`. -/
theorem sD_eq_t (hA : Admissible a E) : sD a E = a + 2 * E * tU a E := by
  have h1 := sD_eq hA
  have h2 := alphaBar_eq hA
  have hE : (E : ℝ) ^ 2 = 1 := by exact_mod_cast E_sq hA
  -- α = a + E t (from ᾱ = a − α = −E t), so √D = 2α − a = a + 2E t
  linear_combination h1 - 2 * h2

/-- `a + 2E σt = −√D`. -/
theorem sD_eq_sigma (hA : Admissible a E) :
    (a : ℝ) + 2 * E * (((-E : ℤ) : ℝ) / tU a E) = -sD a E := by
  rw [sigma_eq hA, sD_eq hA]
  have hE : (E : ℝ) ^ 2 = 1 := by exact_mod_cast E_sq hA
  linear_combination (-2 * alphaR a E) * hE

theorem tU_mul_sigma (hA : Admissible a E) : tU a E * (((-E : ℤ) : ℝ) / tU a E) = -E := by
  have := (tU_pos hA).ne'
  push_cast; field_simp

end LucasU
