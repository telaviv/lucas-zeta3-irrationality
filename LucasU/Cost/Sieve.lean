-- Generalised from lean_fibzeta FibZeta/Cost/Sieve.lean (ε = ±1, general t).
/-
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/TotientSieve.lean (Apache-2.0, Lean
formalisation by F. Solomon Admasu). Changes: the sieve uses the primes 2, 3, 5, 7, and the averages are taken by
expanding the weight over the 16 divisors of 210 (instead of block sums of period 6).
-/
import Mathlib

/-!
# An elementary totient sieve with the primes 2, 3, 5, 7

`φ(e) ≤ e · w(e)` with `w(e) = ∏_{p ∈ {2,3,5,7}, p ∣ e} (1 − 1/p)`, and
`w(e) = ∑_{q ∣ 210} (μ(q)/q) [q ∣ e]`.  For the two test functions of PROOF Prop. 3.6,
`f₁(e) = e(K − e)` and `f₂(e) = (K − 4e)₊²`, each sum `∑_{e ≤ K, q ∣ e} f(e)` is evaluated in closed form, which gives

* `T1_le`: `∑_{e ≤ K} w(e) e (K − e) ≤ μ K³/6 + 120000 K²`,
* `T2_le`: `∑_{e ≤ K} w(e) (K − 4e)₊² ≤ μ K³/12 + 11300000 K²`,

with `μ = ∏_{p ≤ 7} (1 − 1/p²) = 768/1225`.
-/

open Finset

namespace LucasU.Cost

/-! ### Faulhaber -/

theorem sum_Icc_id (n : ℕ) : ∑ k ∈ Icc 1 n, (k : ℝ) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring

theorem sum_Icc_sq (n : ℕ) : ∑ k ∈ Icc 1 n, (k : ℝ) ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-! ### The sieve weight -/

noncomputable def w (n : ℕ) : ℝ :=
  (if 2 ∣ n then 1 / 2 else 1) * (if 3 ∣ n then 2 / 3 else 1) * (if 5 ∣ n then 4 / 5 else 1) *
    (if 7 ∣ n then 6 / 7 else 1)

theorem w_nonneg (n : ℕ) : 0 ≤ w n := by
  unfold w; split_ifs <;> norm_num

theorem w_le_one (n : ℕ) : w n ≤ 1 := by
  unfold w; split_ifs <;> norm_num

theorem totient_le_w (n : ℕ) : (Nat.totient n : ℝ) ≤ n * w n := by
  by_cases hn : n = 0
  · simp [hn]
  have hf : ∀ q ∈ n.primeFactors, (0 : ℚ) ≤ 1 - (q : ℚ)⁻¹ := by
    intro q hq
    have hq1 : (1 : ℚ) ≤ q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).one_le
    have hq0 : (0 : ℚ) < q := by linarith
    have := (inv_le_one₀ hq0).mpr hq1
    linarith
  have hs : ({2, 3, 5, 7} : Finset ℕ).filter (fun q => q ∣ n) ⊆ n.primeFactors := by
    intro q hq
    obtain ⟨hq, hqn⟩ := Finset.mem_filter.mp hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, hqn, hn⟩
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_three, hqn, hn⟩
    · exact Nat.mem_primeFactors.mpr ⟨Nat.prime_five, hqn, hn⟩
    · exact Nat.mem_primeFactors.mpr ⟨by norm_num, hqn, hn⟩
  have hprod := Finset.prod_le_prod_of_subset_of_le_one₀ hs hf
    (fun q _ _ => sub_le_self (1 : ℚ) (by positivity : 0 ≤ (q : ℚ)⁻¹))
  have hbound : (Nat.totient n : ℚ) ≤ n *
      ((if 2 ∣ n then 1 / 2 else 1) * (if 3 ∣ n then 2 / 3 else 1) * (if 5 ∣ n then 4 / 5 else 1) *
        (if 7 ∣ n then 6 / 7 else 1) : ℚ) := by
    rw [Nat.totient_eq_mul_prod_factors]
    refine (mul_le_mul_of_nonneg_left hprod (by positivity)).trans_eq ?_
    congr 1
    rw [Finset.prod_filter]
    by_cases h2 : 2 ∣ n <;> by_cases h3 : 3 ∣ n <;> by_cases h5 : 5 ∣ n <;> by_cases h7 : 7 ∣ n <;>
      norm_num [h2, h3, h5, h7]
  have hr := (Rat.cast_le (K := ℝ)).mpr hbound
  push_cast at hr
  unfold w
  split_ifs at hr ⊢ <;> norm_num at hr ⊢ <;> linarith

/-! ### Expansion over the divisors of 210 -/

def qv : Fin 16 → ℕ := ![1, 2, 3, 5, 7, 6, 10, 14, 15, 21, 35, 30, 42, 70, 105, 210]

noncomputable def cv : Fin 16 → ℝ :=
  ![1, -1/2, -1/3, -1/5, -1/7, 1/6, 1/10, 1/14, 1/15, 1/21, 1/35, -1/30, -1/42, -1/70, -1/105, 1/210]

theorem qv_pos (i : Fin 16) : 0 < qv i := by fin_cases i <;> decide

theorem qv_le (i : Fin 16) : (qv i : ℝ) ≤ 210 := by fin_cases i <;> norm_num [qv]

theorem abs_cv_le (i : Fin 16) : |cv i| ≤ 1 := by
  fin_cases i <;> norm_num [cv, abs_div]

theorem w_expand (e : ℕ) : w e = ∑ i, cv i * (if qv i ∣ e then 1 else 0) := by
  have h6 : 6 ∣ e ↔ 2 ∣ e ∧ 3 ∣ e := by omega
  have h10 : 10 ∣ e ↔ 2 ∣ e ∧ 5 ∣ e := by omega
  have h14 : 14 ∣ e ↔ 2 ∣ e ∧ 7 ∣ e := by omega
  have h15 : 15 ∣ e ↔ 3 ∣ e ∧ 5 ∣ e := by omega
  have h21 : 21 ∣ e ↔ 3 ∣ e ∧ 7 ∣ e := by omega
  have h35 : 35 ∣ e ↔ 5 ∣ e ∧ 7 ∣ e := by omega
  have h30 : 30 ∣ e ↔ 2 ∣ e ∧ 3 ∣ e ∧ 5 ∣ e := by omega
  have h42 : 42 ∣ e ↔ 2 ∣ e ∧ 3 ∣ e ∧ 7 ∣ e := by omega
  have h70 : 70 ∣ e ↔ 2 ∣ e ∧ 5 ∣ e ∧ 7 ∣ e := by omega
  have h105 : 105 ∣ e ↔ 3 ∣ e ∧ 5 ∣ e ∧ 7 ∣ e := by omega
  have h210 : 210 ∣ e ↔ 2 ∣ e ∧ 3 ∣ e ∧ 5 ∣ e ∧ 7 ∣ e := by omega
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, qv, cv, Matrix.cons_val_zero,
    Matrix.cons_val_succ, h6, h10, h14, h15, h21, h35, h30, h42, h70, h105, h210]
  unfold w
  by_cases h2 : 2 ∣ e <;> by_cases h3 : 3 ∣ e <;> by_cases h5 : 5 ∣ e <;> by_cases h7 : 7 ∣ e <;>
    simp [h2, h3, h5, h7] <;> norm_num

theorem sum_cv_div : ∑ i, cv i / (qv i : ℝ) = 768 / 1225 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, qv, cv, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  norm_num

/-- Sums over the multiples of `q`. -/
theorem sum_dvd (K q : ℕ) (hq : 0 < q) (f : ℕ → ℝ) :
    ∑ e ∈ Icc 1 K, (if q ∣ e then f e else 0) = ∑ k ∈ Icc 1 (K / q), f (q * k) := by
  rw [← Finset.sum_filter]
  have hset : (Icc 1 K).filter (fun e => q ∣ e) = (Icc 1 (K / q)).image (fun k => q * k) := by
    ext e
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, hK⟩, ⟨k, rfl⟩⟩
      refine ⟨k, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos k with h | h
        · rw [h] at h1; omega
        · exact h
      · rw [Nat.le_div_iff_mul_le hq, mul_comm]; exact hK
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right q k⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hq.ne' (by omega))
      · rw [Nat.le_div_iff_mul_le hq] at hk2; rw [mul_comm]; exact hk2
  rw [hset, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_left hq hab

/-- The sieve: upper bound for `∑ w(e) f(e)` from two-sided estimates of the sums over multiples. -/
theorem sieve_sum (K : ℕ) (f : ℕ → ℝ) (M E : Fin 16 → ℝ)
    (h : ∀ i, |∑ e ∈ Icc 1 K, (if qv i ∣ e then f e else 0) - M i| ≤ E i) :
    ∑ e ∈ Icc 1 K, w e * f e ≤ ∑ i, (cv i * M i + |cv i| * E i) := by
  have hexp : ∑ e ∈ Icc 1 K, w e * f e =
      ∑ i, cv i * ∑ e ∈ Icc 1 K, (if qv i ∣ e then f e else 0) := by
    simp_rw [w_expand, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e _ => ?_
    split_ifs <;> ring
  rw [hexp]
  refine Finset.sum_le_sum fun i _ => ?_
  set X := ∑ e ∈ Icc 1 K, (if qv i ∣ e then f e else 0)
  have h1 : cv i * (X - M i) ≤ |cv i| * E i := by
    calc cv i * (X - M i) ≤ |cv i * (X - M i)| := le_abs_self _
      _ = |cv i| * |X - M i| := abs_mul _ _
      _ ≤ |cv i| * E i := mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)
  linarith

/-! ### The two test functions -/

theorem T1_q (K q : ℕ) (hq : 0 < q) :
    |∑ e ∈ Icc 1 K, (if q ∣ e then (e : ℝ) * ((K : ℝ) - e) else 0) - (K : ℝ) ^ 3 / (6 * q)| ≤
      ((K : ℝ) * q + (q : ℝ) ^ 2) / 6 := by
  rw [sum_dvd K q hq (fun e => (e : ℝ) * ((K : ℝ) - e))]
  set n := K / q with hn
  have hS : ∑ k ∈ Icc 1 n, ((q * k : ℕ) : ℝ) * ((K : ℝ) - ((q * k : ℕ) : ℝ)) =
      q * K * (n * (n + 1) / 2) - (q : ℝ) ^ 2 * (n * (n + 1) * (2 * n + 1) / 6) := by
    have : ∀ k ∈ Icc 1 n, ((q * k : ℕ) : ℝ) * ((K : ℝ) - ((q * k : ℕ) : ℝ)) =
        q * K * k - (q : ℝ) ^ 2 * (k : ℝ) ^ 2 := by intro k _; push_cast; ring
    rw [Finset.sum_congr rfl this, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      sum_Icc_id, sum_Icc_sq]
  rw [hS]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : (q : ℝ) * n ≤ K := by exact_mod_cast Nat.mul_div_le K q
  have h2 : (K : ℝ) < q * (n + 1) := by exact_mod_cast Nat.lt_mul_div_succ K hq
  set s : ℝ := (K : ℝ) - q * n with hs
  have hs0 : 0 ≤ s := by linarith
  have hsq : s < q := by linarith
  have key : 6 * q * (q * K * (n * (n + 1) / 2) - (q : ℝ) ^ 2 * (n * (n + 1) * (2 * n + 1) / 6)) -
      (K : ℝ) ^ 3 = K * (-(q : ℝ) ^ 2 + 3 * q * s - 3 * s ^ 2) + s * ((q - s) * (q - 2 * s)) := by
    rw [hs]; ring
  have hA : |(-(q : ℝ) ^ 2 + 3 * q * s - 3 * s ^ 2)| ≤ (q : ℝ) ^ 2 := by
    rw [abs_le]; constructor <;> nlinarith [mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ q - s)]
  have hB : |s * ((q - s) * (q - 2 * s))| ≤ (q : ℝ) ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hs0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ q - s)]
    have hc : |(q : ℝ) - 2 * s| ≤ q := by rw [abs_le]; constructor <;> linarith
    calc s * ((q - s) * |(q : ℝ) - 2 * s|) ≤ q * (q * q) := by
          apply mul_le_mul hsq.le _ (by positivity) hq'.le
          exact mul_le_mul (by linarith) hc (abs_nonneg _) hq'.le
      _ = _ := by ring
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have htot : |6 * q * (q * K * (n * (n + 1) / 2) - (q : ℝ) ^ 2 * (n * (n + 1) * (2 * n + 1) / 6)) -
      (K : ℝ) ^ 3| ≤ K * (q : ℝ) ^ 2 + (q : ℝ) ^ 3 := by
    rw [key]
    calc _ ≤ |(K : ℝ) * (-(q : ℝ) ^ 2 + 3 * q * s - 3 * s ^ 2)| + |s * ((q - s) * (q - 2 * s))| :=
          abs_add_le _ _
      _ ≤ _ := by
          rw [abs_mul, abs_of_nonneg hK0]
          nlinarith [mul_le_mul_of_nonneg_left hA hK0]
  have hdiv : q * K * (n * (n + 1) / 2) - (q : ℝ) ^ 2 * (n * (n + 1) * (2 * n + 1) / 6) -
      (K : ℝ) ^ 3 / (6 * q) =
      (6 * q * (q * K * (n * (n + 1) / 2) - (q : ℝ) ^ 2 * (n * (n + 1) * (2 * n + 1) / 6)) -
        (K : ℝ) ^ 3) / (6 * q) := by field_simp
  rw [hdiv, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 6 * q), div_le_iff₀ (by positivity)]
  nlinarith [htot]

theorem T2_q (K q : ℕ) (hq : 0 < q) :
    |∑ e ∈ Icc 1 K, (if q ∣ e then (((K - 4 * e : ℕ) : ℝ)) ^ 2 else 0) - (K : ℝ) ^ 3 / (12 * q)| ≤
      (K : ℝ) ^ 2 + q * K + 16 * (q : ℝ) ^ 2 := by
  rw [sum_dvd K q hq (fun e => (((K - 4 * e : ℕ) : ℝ)) ^ 2)]
  have hp : 0 < 4 * q := by omega
  set m := K / (4 * q) with hm
  have hsub : ∑ k ∈ Icc 1 (K / q), (((K - 4 * (q * k) : ℕ) : ℝ)) ^ 2 =
      ∑ k ∈ Icc 1 m, ((K : ℝ) - 4 * q * k) ^ 2 := by
    have hmle : m ≤ K / q := by
      rw [hm, Nat.le_div_iff_mul_le hq]
      calc K / (4 * q) * q ≤ K / (4 * q) * (4 * q) := Nat.mul_le_mul_left _ (by omega)
        _ ≤ K := Nat.div_mul_le_self K (4 * q)
    rw [← Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hmle)]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk2 := (mem_Icc.mp hk).2
      rw [hm, Nat.le_div_iff_mul_le hp] at hk2
      have : 4 * (q * k) ≤ K := by nlinarith
      rw [Nat.cast_sub this]; push_cast; ring
    · intro k hk hk'
      simp only [mem_Icc, not_and, not_le] at hk'
      have hlt := hk' (mem_Icc.mp hk).1
      rw [hm, Nat.div_lt_iff_lt_mul hp] at hlt
      have : K ≤ 4 * (q * k) := by nlinarith
      rw [Nat.sub_eq_zero_of_le this]; simp
  rw [hsub]
  have hS : ∑ k ∈ Icc 1 m, ((K : ℝ) - 4 * q * k) ^ 2 =
      m * (K : ℝ) ^ 2 - 8 * q * K * (m * (m + 1) / 2) +
        16 * (q : ℝ) ^ 2 * (m * (m + 1) * (2 * m + 1) / 6) := by
    have : ∀ k ∈ Icc 1 m, ((K : ℝ) - 4 * q * k) ^ 2 =
        (K : ℝ) ^ 2 - 8 * q * K * k + 16 * (q : ℝ) ^ 2 * (k : ℝ) ^ 2 := by intro k _; ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, sum_Icc_id, sum_Icc_sq, Finset.sum_const, Nat.card_Icc,
      Nat.add_sub_cancel, nsmul_eq_mul]
  rw [hS]
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 : 4 * (q : ℝ) * m ≤ K := by exact_mod_cast Nat.mul_div_le K (4 * q)
  have h2 : (K : ℝ) < 4 * q * (m + 1) := by exact_mod_cast Nat.lt_mul_div_succ K hp
  set s : ℝ := (K : ℝ) - 4 * q * m with hs
  have hs0 : 0 ≤ s := by linarith
  have hsq : s < 4 * q := by linarith
  set p : ℝ := 4 * q with hpdef
  have key : p * (m * (K : ℝ) ^ 2 - 8 * q * K * (m * (m + 1) / 2) +
      16 * (q : ℝ) ^ 2 * (m * (m + 1) * (2 * m + 1) / 6)) - (K : ℝ) ^ 3 / 3 =
      -(K : ℝ) ^ 2 * p / 2 + K * p ^ 2 / 6 + (-p ^ 2 * s / 6 + p * s ^ 2 / 2 - s ^ 3 / 3) := by
    rw [hs, hpdef]; ring
  have hp0 : 0 < p := by positivity
  have hR : |-p ^ 2 * s / 6 + p * s ^ 2 / 2 - s ^ 3 / 3| ≤ p ^ 3 := by
    have a1 : p ^ 2 * s ≤ p ^ 3 := by nlinarith [sq_nonneg p]
    have a2 : p * s ^ 2 ≤ p ^ 3 := by nlinarith [mul_le_mul hsq.le hsq.le hs0 hp0.le]
    have a3 : s ^ 3 ≤ p ^ 3 := pow_le_pow_left₀ hs0 hsq.le 3
    have b1 : 0 ≤ p ^ 2 * s := by positivity
    have b2 : 0 ≤ p * s ^ 2 := by positivity
    have b3 : 0 ≤ s ^ 3 := by positivity
    rw [abs_le]; constructor <;> nlinarith
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have htot : |p * (m * (K : ℝ) ^ 2 - 8 * q * K * (m * (m + 1) / 2) +
      16 * (q : ℝ) ^ 2 * (m * (m + 1) * (2 * m + 1) / 6)) - (K : ℝ) ^ 3 / 3| ≤
      (K : ℝ) ^ 2 * p / 2 + K * p ^ 2 / 6 + p ^ 3 := by
    rw [key]
    have e1 : |-(K : ℝ) ^ 2 * p / 2 + K * p ^ 2 / 6| ≤ (K : ℝ) ^ 2 * p / 2 + K * p ^ 2 / 6 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (K : ℝ), mul_nonneg hK0 (sq_nonneg p)]
    calc _ ≤ |-(K : ℝ) ^ 2 * p / 2 + K * p ^ 2 / 6| + |-p ^ 2 * s / 6 + p * s ^ 2 / 2 - s ^ 3 / 3| :=
          abs_add_le _ _
      _ ≤ _ := by linarith
  set S := m * (K : ℝ) ^ 2 - 8 * q * K * (m * (m + 1) / 2) +
      16 * (q : ℝ) ^ 2 * (m * (m + 1) * (2 * m + 1) / 6)
  have hdiv : S - (K : ℝ) ^ 3 / (12 * q) = (p * S - (K : ℝ) ^ 3 / 3) / p := by
    rw [hpdef]; field_simp; ring
  rw [hdiv, abs_div, abs_of_pos hp0, div_le_iff₀ hp0]
  have : (K : ℝ) ^ 2 * p / 2 + K * p ^ 2 / 6 + p ^ 3 ≤
      ((K : ℝ) ^ 2 + q * K + 16 * (q : ℝ) ^ 2) * p := by
    rw [hpdef]; nlinarith [sq_nonneg (K : ℝ), mul_nonneg hK0 hq'.le]
  linarith

/-! ### The two sieved sums -/

theorem T1_le (K : ℕ) (hK : 1 ≤ K) :
    ∑ e ∈ Icc 1 K, w e * ((e : ℝ) * ((K : ℝ) - e)) ≤
      768 / 1225 * (K : ℝ) ^ 3 / 6 + 120000 * (K : ℝ) ^ 2 := by
  have h := sieve_sum K (fun e => (e : ℝ) * ((K : ℝ) - e)) (fun i => (K : ℝ) ^ 3 / (6 * qv i))
    (fun i => ((K : ℝ) * qv i + (qv i : ℝ) ^ 2) / 6) (fun i => T1_q K (qv i) (qv_pos i))
  refine h.trans ?_
  rw [Finset.sum_add_distrib]
  have hmain : ∑ i, cv i * ((K : ℝ) ^ 3 / (6 * qv i)) = 768 / 1225 * (K : ℝ) ^ 3 / 6 := by
    have : ∀ i, cv i * ((K : ℝ) ^ 3 / (6 * qv i)) = cv i / qv i * ((K : ℝ) ^ 3 / 6) := by
      intro i
      have : (qv i : ℝ) ≠ 0 := by exact_mod_cast (qv_pos i).ne'
      field_simp
    simp_rw [this]
    rw [← Finset.sum_mul, sum_cv_div]; ring
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have herr : ∑ i, |cv i| * (((K : ℝ) * qv i + (qv i : ℝ) ^ 2) / 6) ≤ ∑ _i : Fin 16, 7500 * (K : ℝ) ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h0 := qv_le i
    have h1 : (0 : ℝ) ≤ qv i := by positivity
    have h2 := abs_cv_le i
    have h3 : ((K : ℝ) * qv i + (qv i : ℝ) ^ 2) / 6 ≤ 7500 * (K : ℝ) ^ 2 := by nlinarith
    calc _ ≤ 1 * (((K : ℝ) * qv i + (qv i : ℝ) ^ 2) / 6) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ _ := by linarith
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at herr
  rw [hmain]; push_cast at herr; linarith

theorem T2_le (K : ℕ) (hK : 1 ≤ K) :
    ∑ e ∈ Icc 1 K, w e * ((((K - 4 * e : ℕ) : ℝ)) ^ 2) ≤
      768 / 1225 * (K : ℝ) ^ 3 / 12 + 11300000 * (K : ℝ) ^ 2 := by
  have h := sieve_sum K (fun e => (((K - 4 * e : ℕ) : ℝ)) ^ 2) (fun i => (K : ℝ) ^ 3 / (12 * qv i))
    (fun i => (K : ℝ) ^ 2 + qv i * K + 16 * (qv i : ℝ) ^ 2) (fun i => T2_q K (qv i) (qv_pos i))
  refine h.trans ?_
  rw [Finset.sum_add_distrib]
  have hmain : ∑ i, cv i * ((K : ℝ) ^ 3 / (12 * qv i)) = 768 / 1225 * (K : ℝ) ^ 3 / 12 := by
    have : ∀ i, cv i * ((K : ℝ) ^ 3 / (12 * qv i)) = cv i / qv i * ((K : ℝ) ^ 3 / 12) := by
      intro i
      have : (qv i : ℝ) ≠ 0 := by exact_mod_cast (qv_pos i).ne'
      field_simp
    simp_rw [this]
    rw [← Finset.sum_mul, sum_cv_div]; ring
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have herr : ∑ i, |cv i| * ((K : ℝ) ^ 2 + qv i * K + 16 * (qv i : ℝ) ^ 2) ≤
      ∑ _i : Fin 16, 706000 * (K : ℝ) ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h0 := qv_le i
    have h1 : (0 : ℝ) ≤ qv i := by positivity
    have h2 := abs_cv_le i
    have h3 : (K : ℝ) ^ 2 + qv i * K + 16 * (qv i : ℝ) ^ 2 ≤ 706000 * (K : ℝ) ^ 2 := by nlinarith
    calc _ ≤ 1 * ((K : ℝ) ^ 2 + qv i * K + 16 * (qv i : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ _ := by linarith
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at herr
  have hK2 : (0 : ℝ) ≤ (K : ℝ) ^ 2 := by positivity
  rw [hmain]; push_cast at herr; linarith

end LucasU.Cost
