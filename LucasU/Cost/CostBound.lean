-- Generalised from lean_fibzeta FibZeta/Cost/CostBound.lean (ε = ±1, general t).
import LucasU.Cost.Cyclo
import LucasU.Cost.RootCount
import LucasU.Cost.Sieve

/-!
# Proposition 3.6 in the frozen form `CostBound`

`log |C_K(t) C_K(ε/t)| ≤ (121/100) K³ log t⁻¹ + C K² (1 + log K)²`, for `ε = ±1`, `0 < t ≤ φ⁻¹`.

* `log_norm_CK_eq`: `log |C_K(t) C_K(ε/t)| = ∑_{d ≤ 4K} n_d (log|Φ_d(t)| + log|Φ_d(ε/t)|)`;
* Lemma 3.5 (`log_norm_cyc_le`) bounds each bracket by `φ(d) log t⁻¹ + 12`;
* `sum_totient_nExp_le`: `∑_d n_d φ(d) ≤ (121/100) K³ + 6610008 K²`
  (W part `≤ 8 T1 + T2/2 + 4K(K+1)`, α part `≤ K³/3`; the cubic constant is
  `(768/1225)(4/3 + 1/24) + 1/3 = 4393/3675 = 1.19537… ≤ 1.21`, for both signs: the root
  counts `∑_{e(d)=e} φ(d) ≤ 2φ(e)` and `∑_{α_j(ζ_d)=1} φ(d) ≤ 2j + 1` hold for `ε = ±1`);
* `sum_nExp_le`: `∑_d n_d ≤ 70 K² (1 + log K)`.
-/

open Polynomial Finset

namespace LucasU.Cost

variable {ε : ℤ} {t : ℝ}

/-! ### The W part -/

theorem mul_sub_div_le (K e : ℕ) : e * (K / e - 4) ≤ K - 4 * e := by
  have h1 := Nat.mul_div_le K e
  rw [Nat.mul_sub]
  generalize e * (K / e) = X at h1 ⊢
  omega

theorem totient_Wc_le (K e : ℕ) (he : 1 ≤ e) (heK : e ≤ K) :
    ((2 * Nat.totient e * Wc K e : ℕ) : ℝ) ≤
      8 * (w e * ((e : ℝ) * ((K : ℝ) - e))) + w e * (((K - 4 * e : ℕ) : ℝ)) ^ 2 / 2 + 8 * e := by
  have hW := Wc_bound he heK
  set a : ℕ := K / e - 4
  have hWr : 4 * (Wc K e : ℝ) ≤ 16 * K - 16 * e + e * (a : ℝ) ^ 2 + 16 := by
    have : ((4 * Wc K e + 16 * e : ℕ) : ℝ) ≤ ((16 * K + e * a ^ 2 + 16 : ℕ) : ℝ) := by
      exact_mod_cast hW
    push_cast at this; linarith
  have hea : (e : ℝ) * a ≤ ((K - 4 * e : ℕ) : ℝ) := by exact_mod_cast mul_sub_div_le K e
  have hea2 : ((e : ℝ) * a) ^ 2 ≤ (((K - 4 * e : ℕ) : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hea 2
  have hphi := totient_le_w e
  have hw0 := w_nonneg e
  have hw1 := w_le_one e
  have he0 : (0 : ℝ) ≤ e := by positivity
  have heK' : (e : ℝ) ≤ K := by exact_mod_cast heK
  have hWc0 : (0 : ℝ) ≤ Wc K e := by positivity
  push_cast
  calc 2 * (Nat.totient e : ℝ) * Wc K e ≤ 2 * (e * w e) * Wc K e := by
        have := mul_le_mul_of_nonneg_right hphi hWc0; nlinarith
    _ ≤ 2 * (e * w e) * ((16 * K - 16 * e + e * (a : ℝ) ^ 2 + 16) / 4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    _ = 8 * (w e * ((e : ℝ) * ((K : ℝ) - e))) + w e * ((e : ℝ) * a) ^ 2 / 2 + 8 * e * w e := by ring
    _ ≤ _ := by
        have h1 : w e * ((e : ℝ) * a) ^ 2 ≤ w e * (((K - 4 * e : ℕ) : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left hea2 hw0
        have h2 : 8 * (e : ℝ) * w e ≤ 8 * e := by nlinarith
        linarith

theorem sum_totient_nW_real (hε : ε = 1 ∨ ε = -1) (K : ℕ) (hK : 1 ≤ K) :
    ∑ d ∈ Icc 1 (4 * K), (Nat.totient d : ℝ) * nW ε K d ≤
      768 / 1225 * (4 / 3 + 1 / 24) * (K : ℝ) ^ 3 + 6610008 * (K : ℝ) ^ 2 := by
  have h := sum_totient_mul_nW_le hε K (4 * K)
  have hr : ∑ d ∈ Icc 1 (4 * K), (Nat.totient d : ℝ) * nW ε K d ≤
      ∑ e ∈ Icc 1 K, ((2 * Nat.totient e * Wc K e : ℕ) : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr h
    push_cast at this ⊢; exact this
  refine hr.trans ?_
  have hs := Finset.sum_le_sum (fun e (he : e ∈ Icc 1 K) =>
    totient_Wc_le K e (mem_Icc.mp he).1 (mem_Icc.mp he).2)
  refine hs.trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.sum_div, sum_Icc_id]
  have h1 := T1_le K hK
  have h2 := T2_le K hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  nlinarith

/-! ### The α part -/

theorem alpha_sum_le (K : ℕ) :
    ((∑ j ∈ Icc 1 (K - 2), (K - 1 - j) * (2 * j + 1) : ℕ) : ℝ) ≤ (K : ℝ) ^ 3 / 3 := by
  rcases Nat.lt_or_ge K 2 with hK | hK
  · rw [show K - 2 = 0 by omega]; simp; positivity
  obtain ⟨n, rfl⟩ : ∃ n, K = n + 2 := ⟨K - 2, by omega⟩
  rw [show n + 2 - 2 = n by omega]
  push_cast
  have : ∀ j ∈ Icc 1 n, (((n + 1 - j : ℕ) : ℝ) * (2 * j + 1)) =
      (2 * n + 1) * (j : ℝ) - 2 * (j : ℝ) ^ 2 + (n + 1) := by
    intro j hj
    have := (mem_Icc.mp hj).2
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, sum_Icc_id, sum_Icc_sq, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul]
  have hn : (0 : ℝ) ≤ n := by positivity
  nlinarith [sq_nonneg (n : ℝ)]

theorem sum_totient_nAlpha_real (hε : ε = 1 ∨ ε = -1) (K : ℕ) :
    ∑ d ∈ Icc 1 (4 * K), (Nat.totient d : ℝ) * nAlpha ε K d ≤ (K : ℝ) ^ 3 / 3 := by
  have h := (Nat.cast_le (α := ℝ)).mpr (sum_totient_mul_nAlpha_le hε K (4 * K))
  push_cast at h
  refine h.trans ?_
  have := alpha_sum_le K
  push_cast at this
  exact this

theorem sum_totient_nExp_le (hε : ε = 1 ∨ ε = -1) (K : ℕ) (hK : 1 ≤ K) :
    ∑ d ∈ Icc 1 (4 * K), (nExp ε K d : ℝ) * Nat.totient d ≤
      121 / 100 * (K : ℝ) ^ 3 + 6610008 * (K : ℝ) ^ 2 := by
  have h1 := sum_totient_nW_real hε K hK
  have h2 := sum_totient_nAlpha_real hε K
  have hsplit : ∑ d ∈ Icc 1 (4 * K), (nExp ε K d : ℝ) * Nat.totient d =
      ∑ d ∈ Icc 1 (4 * K), (Nat.totient d : ℝ) * nW ε K d +
        ∑ d ∈ Icc 1 (4 * K), (Nat.totient d : ℝ) * nAlpha ε K d := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    unfold nExp; push_cast; ring
  rw [hsplit]
  have hK3 : (0 : ℝ) ≤ (K : ℝ) ^ 3 := by positivity
  nlinarith

/-! ### The number of factors -/

theorem Wc_le_real (K e : ℕ) (he : 1 ≤ e) (heK : e ≤ K) :
    8 * (Wc K e : ℝ) ≤ 32 * K + 32 + 2 * (K : ℝ) ^ 2 / e := by
  have hW := Wc_bound he heK
  have hWr : 4 * (Wc K e : ℝ) ≤ 16 * K + e * ((K / e - 4 : ℕ) : ℝ) ^ 2 + 16 := by
    have : ((4 * Wc K e + 16 * e : ℕ) : ℝ) ≤ ((16 * K + e * (K / e - 4) ^ 2 + 16 : ℕ) : ℝ) := by
      exact_mod_cast hW
    push_cast at this
    have : (0 : ℝ) ≤ e := by positivity
    linarith
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  have hb : ((K / e - 4 : ℕ) : ℝ) ≤ (K : ℝ) / e := by
    calc ((K / e - 4 : ℕ) : ℝ) ≤ ((K / e : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le _ _
      _ ≤ _ := Nat.cast_div_le
  have hb2 : (e : ℝ) * ((K / e - 4 : ℕ) : ℝ) ^ 2 ≤ (K : ℝ) ^ 2 / e := by
    calc (e : ℝ) * ((K / e - 4 : ℕ) : ℝ) ^ 2 ≤ e * ((K : ℝ) / e) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb 2) he0.le
      _ = (K : ℝ) ^ 2 / e := by field_simp
  calc 8 * (Wc K e : ℝ) = 2 * (4 * Wc K e) := by ring
    _ ≤ 2 * (16 * K + e * ((K / e - 4 : ℕ) : ℝ) ^ 2 + 16) := by linarith
    _ ≤ 2 * (16 * K + (K : ℝ) ^ 2 / e + 16) := by linarith
    _ = _ := by ring

theorem sum_inv_le (K : ℕ) : ∑ e ∈ Icc 1 K, (1 : ℝ) / e ≤ 1 + Real.log K := by
  have h := harmonic_le_one_add_log K
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  simpa [one_div] using h

theorem sum_nExp_le (hε : ε = 1 ∨ ε = -1) (K : ℕ) (hK : 1 ≤ K) :
    ∑ d ∈ Icc 1 (4 * K), (nExp ε K d : ℝ) ≤ 70 * (K : ℝ) ^ 2 * (1 + Real.log K) := by
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hW : ∑ d ∈ Icc 1 (4 * K), (nW ε K d : ℝ) ≤ ∑ e ∈ Icc 1 K, 8 * (Wc K e : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr (sum_nW_le hε K (4 * K))
    push_cast at this; exact this
  have hW2 : ∑ e ∈ Icc 1 K, 8 * (Wc K e : ℝ) ≤
      ∑ e ∈ Icc 1 K, (32 * K + 32 + 2 * (K : ℝ) ^ 2 * (1 / e)) := by
    refine Finset.sum_le_sum fun e he => ?_
    have := Wc_le_real K e (mem_Icc.mp he).1 (mem_Icc.mp he).2
    calc _ ≤ _ := this
      _ = _ := by ring
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul] at hW2
  have h4 : ∑ e ∈ Icc 1 K, 2 * (K : ℝ) ^ 2 * (1 / e) = 2 * (K : ℝ) ^ 2 * ∑ e ∈ Icc 1 K, (1 : ℝ) / e := by
    rw [Finset.mul_sum]
  have hinv := sum_inv_le K
  have hA : ∑ d ∈ Icc 1 (4 * K), (nAlpha ε K d : ℝ) ≤ ∑ _d ∈ Icc 1 (4 * K), (K : ℝ) :=
    Finset.sum_le_sum fun d _ => by exact_mod_cast nAlpha_le (ε := ε) K d
  rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hA
  have hsplit : ∑ d ∈ Icc 1 (4 * K), (nExp ε K d : ℝ) =
      ∑ d ∈ Icc 1 (4 * K), (nW ε K d : ℝ) + ∑ d ∈ Icc 1 (4 * K), (nAlpha ε K d : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    unfold nExp; push_cast; ring
  rw [hsplit]
  have hK2 : (0 : ℝ) ≤ (K : ℝ) ^ 2 := by positivity
  have h3 : 2 * (K : ℝ) ^ 2 * ∑ e ∈ Icc 1 K, (1 : ℝ) / e ≤ 2 * (K : ℝ) ^ 2 * (1 + Real.log K) :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  push_cast at hA hW2
  have h5 : (K : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
  have h6 := mul_nonneg hK2 hlog
  linarith

/-! ### The norm of `C_K(t)` -/

theorem aeval_cyclotomic (τ : ℝ) (d : ℕ) :
    aeval τ (cyclotomic d ℤ) = (cyclotomic d ℝ).eval τ := by
  rw [aeval_def, ← eval_map, map_cyclotomic]

theorem aeval_CKpoly (ε : ℤ) (τ : ℝ) (K : ℕ) :
    aeval τ (CKpoly ε K) = ∏ d ∈ Icc 1 (4 * K), ((cyclotomic d ℝ).eval τ) ^ nExp ε K d := by
  unfold CKpoly
  rw [map_prod]
  refine Finset.prod_congr rfl fun d _ => ?_
  rw [map_pow, aeval_cyclotomic]

theorem log_abs_aeval_CKpoly (ε : ℤ) {τ : ℝ} (hτ : ∀ m : ℕ, 0 < m → τ ^ m ≠ 1) (K : ℕ) :
    Real.log |aeval τ (CKpoly ε K)| =
      ∑ d ∈ Icc 1 (4 * K), (nExp ε K d : ℝ) * Real.log |(cyclotomic d ℝ).eval τ| := by
  rw [aeval_CKpoly, Finset.abs_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [abs_pow, Real.log_pow]
  · intro d hd
    have hd0 : 0 < d := (mem_Icc.mp hd).1
    rw [abs_pow]
    exact pow_ne_zero _ (abs_ne_zero.mpr (cyc_eval_ne_zero hτ hd0))

theorem log_norm_CK_eq (h : Good ε t) (K : ℕ) :
    Real.log |aeval t (CKpoly ε K) * aeval ((ε : ℝ) / t) (CKpoly ε K)| =
      ∑ d ∈ Icc 1 (4 * K), (nExp ε K d : ℝ) * (Real.log |(cyclotomic d ℝ).eval t| +
        Real.log |(cyclotomic d ℝ).eval ((ε : ℝ) / t)|) := by
  rw [abs_mul, Real.log_mul (abs_ne_zero.mpr (aeval_CKpoly_ne_zero ε (good_not_root h) K))
    (abs_ne_zero.mpr (aeval_CKpoly_ne_zero ε (good_conj_not_root h) K)),
    log_abs_aeval_CKpoly ε (good_not_root h), log_abs_aeval_CKpoly ε (good_conj_not_root h),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-- **Proposition 3.6** (frozen form), for both signs and every `0 < t ≤ φ⁻¹`. -/
theorem costBound {ε : ℤ} {t : ℝ} (h : Good ε t) : CostBound ε t := by
  refine ⟨6610008 * Real.log t⁻¹ + 840, fun K hK => ?_⟩
  rw [log_norm_CK_eq h]
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hL := (good_log_pos h)
  have hstep : ∑ d ∈ Icc 1 (4 * K), (nExp ε K d : ℝ) * (Real.log |(cyclotomic d ℝ).eval t| +
        Real.log |(cyclotomic d ℝ).eval ((ε : ℝ) / t)|) ≤
      ∑ d ∈ Icc 1 (4 * K), (nExp ε K d : ℝ) *
        ((Nat.totient d : ℝ) * Real.log t⁻¹ + 12) :=
    Finset.sum_le_sum fun d hd => mul_le_mul_of_nonneg_left
      (log_norm_cyc_le h (mem_Icc.mp hd).1) (by positivity)
  refine hstep.trans ?_
  have hsplit : ∑ d ∈ Icc 1 (4 * K), (nExp ε K d : ℝ) *
        ((Nat.totient d : ℝ) * Real.log t⁻¹ + 12) =
      Real.log t⁻¹ * ∑ d ∈ Icc 1 (4 * K), (nExp ε K d : ℝ) * Nat.totient d +
        12 * ∑ d ∈ Icc 1 (4 * K), (nExp ε K d : ℝ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring
  rw [hsplit]
  have h1 := sum_totient_nExp_le (good_eps h) K hK
  have h2 := sum_nExp_le (good_eps h) K hK
  have hK2 : (0 : ℝ) ≤ (K : ℝ) ^ 2 := by positivity
  have hA : Real.log t⁻¹ * ∑ d ∈ Icc 1 (4 * K), (nExp ε K d : ℝ) * Nat.totient d ≤
      Real.log t⁻¹ * (121 / 100 * (K : ℝ) ^ 3 + 6610008 * (K : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left h1 hL.le
  have hB : (1 : ℝ) + Real.log K ≤ (1 + Real.log K) ^ 2 := by nlinarith
  have hC : (1 : ℝ) ≤ (1 + Real.log K) ^ 2 := by nlinarith
  have hD : (K : ℝ) ^ 2 * (1 + Real.log K) ≤ (K : ℝ) ^ 2 * (1 + Real.log K) ^ 2 :=
    mul_le_mul_of_nonneg_left hB hK2
  have hE : (K : ℝ) ^ 2 ≤ (K : ℝ) ^ 2 * (1 + Real.log K) ^ 2 := by nlinarith
  have hF : Real.log t⁻¹ * (K : ℝ) ^ 2 ≤ Real.log t⁻¹ * ((K : ℝ) ^ 2 * (1 + Real.log K) ^ 2) :=
    mul_le_mul_of_nonneg_left hE hL.le
  nlinarith

end LucasU.Cost
