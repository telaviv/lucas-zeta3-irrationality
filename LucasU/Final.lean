import LucasU.Main
import LucasU.Corollaries
import LucasU.Analytic.All
import LucasU.NonVan.Nonvanishing
import LucasU.Conj.ConjBound
import LucasU.Cost.CostBound
import LucasU.Denom.Integrality

-- Generalised from lean_fibzeta FibZeta/Final.lean (general (a, E); adds the Pell and F_{kn} corollaries).

/-!
# The theorem: `∑ 1/U_n³` is irrational for every Lucas sequence of a quadratic unit

Combines the proved ingredients (`LucasU.Analytic.decayBound`, `LucasU.Conj.conjBound`,
`LucasU.Denom.integrality`, `LucasU.Cost.costBound`, `LucasU.NonVan.nonvanishing`) with the assembly
`LucasU.irrational_zetaU_of`, at `ε = −E`, `t = tU a E`.
-/

namespace LucasU

theorem neg_E_cases {a : ℕ} {E : ℤ} (hA : Admissible a E) : -E = 1 ∨ -E = -1 := by
  rcases E_cases hA with h | h <;> simp [h]

/-- **Main theorem.** For `E = 1, a ≥ 1` or `E = −1, a ≥ 3`, `∑_{n ≥ 1} 1/U_n³` is irrational, where
`U_0 = 0`, `U_1 = 1`, `U_{n+2} = a U_{n+1} + E U_n`. -/
theorem irrational_zetaU {a : ℕ} {E : ℤ} (hA : Admissible a E) : Irrational (zetaU a E) :=
  irrational_zetaU_of hA (Analytic.decayBound (good_tU hA)) (Conj.conjBound (good_tU hA))
    (Denom.integrality (neg_E_cases hA)) (Cost.costBound (good_tU hA)) (NonVan.nonvanishing (good_tU hA))

/-- Sanity check for the statement: the series defining `zetaU` converges, to `D √D Ξ`. -/
theorem hasSum_zetaU {a : ℕ} {E : ℤ} (hA : Admissible a E) :
    HasSum (fun n : ℕ => 1 / ((Useq a E (n + 1) : ℤ) : ℝ) ^ 3) (zetaU a E) := by
  have hs : Summable (fun N => psi (-E) (tU a E) (N + 1)) :=
    (summable_nat_add_iff 1).mpr (Conj.summable_psi (good_tU hA))
  have h := (hs.mul_left ((discr a E : ℝ) * sD a E)).hasSum
  rw [zetaU_eq hA, XiR, ← tsum_mul_left]
  convert h using 2 with n
  exact one_div_U_cube hA (n + 1)

/-- **Pell numbers.** `∑_{n ≥ 1} 1/P_n³` is irrational. -/
theorem irrational_pell : Irrational (∑' n : ℕ, 1 / ((pell (n + 1) : ℤ) : ℝ) ^ 3) :=
  irrational_pell_of fun _ _ hA => irrational_zetaU hA

/-- **Fibonacci multiples.** For every `k ≥ 1`, `∑_{n ≥ 1} 1/F_{kn}³` is irrational. -/
theorem irrational_fib_mul {k : ℕ} (hk : 1 ≤ k) :
    Irrational (∑' n : ℕ, 1 / (Nat.fib (k * (n + 1)) : ℝ) ^ 3) :=
  irrational_fib_mul_of (fun _ _ hA => irrational_zetaU hA) hk

end LucasU
