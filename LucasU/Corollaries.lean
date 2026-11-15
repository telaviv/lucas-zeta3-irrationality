import LucasU.Unit

/-!
# Corollaries: Pell numbers and `∑ 1/F_{kn}³`

Stated for any proof `h` of the main theorem (`∀ a E, Admissible a E → Irrational (zetaU a E)`), so that this
file does not depend on the ingredient proofs; `LucasU/Final.lean` instantiates `h`.

* `irrational_pell_of`: `∑ 1/P_n³ ∉ ℚ`, `P_n = Useq 2 1 n` the Pell numbers.
* `irrational_fib_mul_of`: `∑_{n ≥ 1} 1/F_{kn}³ ∉ ℚ` for every `k ≥ 1`, via `F_{kn} = F_k · U_n(L_k, (−1)^k)`
  (in this library's convention `Useq (L_k) ((−1)^(k+1))`).
-/

open Finset

namespace LucasU

/-- Pell numbers: `P_0 = 0`, `P_1 = 1`, `P_{n+2} = 2 P_{n+1} + P_n`. -/
abbrev pell (n : ℕ) : ℤ := Useq 2 1 n

theorem admissible_pell : Admissible 2 1 := Or.inl ⟨rfl, by norm_num⟩

theorem irrational_pell_of (h : ∀ a E, Admissible a E → Irrational (zetaU a E)) :
    Irrational (∑' n : ℕ, 1 / ((pell (n + 1) : ℤ) : ℝ) ^ 3) :=
  h 2 1 admissible_pell

/-- Lucas numbers `L_k = F_{k−1} + F_{k+1}` (`k ≥ 1`); `L_0 := 2`. -/
def lucasNum : ℕ → ℕ
  | 0 => 2
  | k + 1 => Nat.fib k + Nat.fib (k + 2)

/-- Binet for Lucas numbers: `L_k = φ^k + ψ^k`. -/
theorem lucasNum_eq (k : ℕ) :
    (lucasNum k : ℝ) = Real.goldenRatio ^ k + Real.goldenConj ^ k := by
  cases k with
  | zero => simp [lucasNum]; norm_num
  | succ k =>
    simp only [lucasNum, Nat.cast_add, Real.coe_fib_eq]
    have hs : (√5 : ℝ) ≠ 0 := by positivity
    have h5 : √5 ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
    have hφ2 := Real.goldenRatio_sq
    have hψ2 := Real.goldenConj_sq
    have hφ5 : Real.goldenRatio + 2 = √5 * Real.goldenRatio := by
      rw [Real.goldenRatio]; linear_combination (-1 / 2 : ℝ) * h5
    have hψ5 : Real.goldenConj + 2 = -(√5 * Real.goldenConj) := by
      rw [Real.goldenConj]; linear_combination (-1 / 2 : ℝ) * h5
    rw [← add_div, div_eq_iff hs]
    linear_combination Real.goldenRatio ^ k * hφ2 - Real.goldenConj ^ k * hψ2 +
      Real.goldenRatio ^ k * hφ5 - Real.goldenConj ^ k * hψ5

theorem lucasNum_pos {k : ℕ} : 1 ≤ lucasNum k := by
  cases k with
  | zero => simp [lucasNum]
  | succ k =>
    show 1 ≤ Nat.fib k + Nat.fib (k + 2)
    have := Nat.fib_pos.mpr (show 0 < k + 2 by omega); omega

theorem lucasNum_ge_three {k : ℕ} (hk : 2 ≤ k) : 3 ≤ lucasNum k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  show 3 ≤ Nat.fib (j + 1) + Nat.fib (j + 1 + 2)
  have h1 : 1 ≤ Nat.fib (j + 1) := Nat.fib_pos.mpr (by omega)
  have h2 : Nat.fib (j + 1 + 2) = Nat.fib (j + 1) + Nat.fib (j + 1 + 1) := Nat.fib_add_two
  have h3 : 1 ≤ Nat.fib (j + 1 + 1) := Nat.fib_pos.mpr (by omega)
  omega

/-- The parameters of `α = φ^k`: `a = L_k`, `E = (−1)^{k+1}`. -/
theorem admissible_fib_mul {k : ℕ} (hk : 1 ≤ k) : Admissible (lucasNum k) ((-1) ^ (k + 1)) := by
  rcases Nat.even_or_odd k with he | ho
  · right
    refine ⟨by rw [pow_succ, he.neg_one_pow]; norm_num, lucasNum_ge_three ?_⟩
    obtain ⟨j, rfl⟩ := he; omega
  · left
    exact ⟨by rw [pow_succ, ho.neg_one_pow]; norm_num, lucasNum_pos⟩

/-- `F_{kn} = F_k · U_n(L_k, (−1)^k)` (as reals). -/
theorem fib_mul_eq (k n : ℕ) :
    (Nat.fib (k * n) : ℝ) = Nat.fib k * (Useq (lucasNum k) ((-1) ^ (k + 1)) n : ℝ) := by
  -- both sides satisfy V_{n+2} = L_k V_{n+1} + (−1)^{k+1} V_n with V_0 = 0, V_1 = F_k
  have hrec : ∀ n : ℕ, (Nat.fib (k * (n + 2)) : ℝ) =
      lucasNum k * Nat.fib (k * (n + 1)) + (-1) ^ (k + 1) * Nat.fib (k * n) := by
    intro n
    simp only [Real.coe_fib_eq, lucasNum_eq]
    have hs : (√5 : ℝ) ≠ 0 := by positivity
    have hprod := Real.goldenRatio_mul_goldenConj
    field_simp
    have hφψ : (Real.goldenRatio * Real.goldenConj) ^ k = (-1) ^ k := by rw [hprod]
    rw [mul_pow] at hφψ
    rw [show k * (n + 2) = k * n + k + k by ring, show k * (n + 1) = k * n + k by ring]
    simp only [pow_add]
    linear_combination (Real.goldenConj ^ (k * n) - Real.goldenRatio ^ (k * n)) * hφψ
  have key : ∀ n : ℕ, (Nat.fib (k * n) : ℝ) = Nat.fib k * (Useq (lucasNum k) ((-1) ^ (k + 1)) n : ℝ) ∧
      (Nat.fib (k * (n + 1)) : ℝ) =
        Nat.fib k * (Useq (lucasNum k) ((-1) ^ (k + 1)) (n + 1) : ℝ) := by
    intro n
    induction n with
    | zero => simp [Useq]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      rw [show n + 1 + 1 = n + 2 by ring, hrec n, ih.1, ih.2]
      simp only [Useq]
      push_cast
      ring
  exact (key n).1

theorem irrational_fib_mul_of (h : ∀ a E, Admissible a E → Irrational (zetaU a E)) {k : ℕ}
    (hk : 1 ≤ k) : Irrational (∑' n : ℕ, 1 / (Nat.fib (k * (n + 1)) : ℝ) ^ 3) := by
  have hz := h _ _ (admissible_fib_mul hk)
  have hFk : (Nat.fib k : ℝ) ≠ 0 := by
    have := Nat.fib_pos.mpr (show 0 < k by omega); positivity
  -- ∑ 1/F_{k(n+1)}³ = F_k^{-3} · zetaU
  have heq : (∑' n : ℕ, 1 / (Nat.fib (k * (n + 1)) : ℝ) ^ 3) =
      ((((Nat.fib k : ℚ) ^ 3)⁻¹ : ℚ) : ℝ) * zetaU (lucasNum k) ((-1) ^ (k + 1)) := by
    unfold zetaU
    push_cast
    rw [← tsum_mul_left]
    congr 1
    funext n
    rw [fib_mul_eq]
    field_simp
  rw [heq]
  have hq : ((Nat.fib k : ℚ) ^ 3)⁻¹ ≠ 0 := by
    have : (Nat.fib k : ℚ) ≠ 0 := by exact_mod_cast (Nat.fib_pos.mpr (show 0 < k by omega)).ne'
    positivity
  exact hz.ratCast_mul hq

end LucasU
