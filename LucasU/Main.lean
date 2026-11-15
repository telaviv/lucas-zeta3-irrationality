import LucasU.Unit

/-!
# Assembly (PROOF_U §6)

`irrational_zetaU_of` derives `Irrational (zetaU a E)` from the five frozen ingredients at
`ε = −E`, `t = tU a E = 1/α`.

Suppose `∑ 1/U_n³ = p/b`.  Then `Ξ = (p/b)/(D√D) = u(t)` and `−Ξ = u(σt)` with
`u(τ) = p(a + 2Eτ)/(b D²)` (as `√D = a + 2E t = −(a + 2E σt)`, `σt = ε/t`).  By `Integrality`,
`Y(τ) = C_K(τ) (b D²)^K Δ_{K,τ}(u(τ)) = Q(τ)/τ^N` for one integer polynomial `Q` and both
`τ = t`, `τ = σt`.  These are the two roots of `τ² + aE τ − E`, so `Q(t) Q(σt)` is an integer,
nonzero when `Q(t) ≠ 0` (because `√D ∉ ℚ`).  Hence `1 ≤ |Y(t) Y(σt)|` whenever `Δ_K(Ξ) ≠ 0`,
which happens for infinitely many `K`, while the bounds make the right side
`≤ exp(−(11/9 − 121/100) K³ log α + O(K² log² K))`.
-/

open Polynomial Finset Filter Topology

namespace LucasU

/-! ### Degree and nonvanishing of `C_K` -/

theorem natDegree_Delta_le {𝕜 : Type*} [Field 𝕜] (ε : ℤ) (τ : 𝕜) (K : ℕ) :
    (Delta ε τ K).natDegree ≤ K := by
  unfold Delta
  simpa [Fintype.card_fin] using
    Polynomial.natDegree_det_X_add_C_le (hankelLin ε τ K) (hankelConst ε τ K)

theorem pow_ne_one_of_abs_ne_one {τ : ℝ} (h : |τ| ≠ 1) : ∀ m : ℕ, 0 < m → τ ^ m ≠ 1 := by
  intro m hm hτ
  apply h
  have : |τ| ^ m = 1 := by rw [← abs_pow, hτ, abs_one]
  exact (pow_eq_one_iff_of_nonneg (abs_nonneg τ) hm.ne').mp this

theorem aeval_CKpoly_ne_zero (ε : ℤ) {τ : ℝ} (h : ∀ m : ℕ, 0 < m → τ ^ m ≠ 1) (K : ℕ) :
    aeval τ (CKpoly ε K) ≠ 0 := by
  unfold CKpoly
  rw [map_prod]
  refine Finset.prod_ne_zero_iff.mpr fun d hd => ?_
  rw [map_pow]
  refine pow_ne_zero _ ?_
  have hd0 : 0 < d := by have := (mem_Icc.mp hd).1; omega
  intro h0
  have : NeZero d := ⟨hd0.ne'⟩
  have hroot : (cyclotomic d ℝ).IsRoot τ := by
    rw [IsRoot, ← map_cyclotomic_int, eval_map]
    rw [aeval_def] at h0
    simpa using h0
  rw [isRoot_cyclotomic_iff] at hroot
  exact h d hd0 hroot.pow_eq_one

/-! ### The norm argument -/

/-- For `Q ∈ ℤ[X]`, `Q(t) Q(σt)` is an integer, nonzero when `Q(t) ≠ 0`. -/
theorem norm_ne_zero {a : ℕ} {E : ℤ} (hA : Admissible a E) (Q : ℤ[X]) :
    ∃ z : ℤ, aeval (tU a E) Q * aeval (((-E : ℤ) : ℝ) / tU a E) Q = z ∧
      (aeval (tU a E) Q ≠ 0 → z ≠ 0) := by
  set M : ℤ[X] := X ^ 2 + (C ((a : ℤ) * E) * X - C E) with hM
  have hlow : (C ((a : ℤ) * E) * X - C E : ℤ[X]).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_C_mul_le _ _).trans natDegree_X_le
    · simp
  have hMm : M.Monic := by
    rw [hM]
    refine monic_X_pow_add ?_
    exact lt_of_le_of_lt (degree_le_of_natDegree_le hlow) (by exact_mod_cast (show (1 : ℕ) < 2 by norm_num))
  have hMdeg : M.natDegree = 2 := by
    rw [hM, natDegree_add_eq_left_of_natDegree_lt]
    · simp
    · calc (C ((a : ℤ) * E) * X - C E).natDegree ≤ 1 := hlow
        _ < (X ^ 2 : ℤ[X]).natDegree := by simp
  set R := Q %ₘ M with hR
  have hdecomp : Q = M * (Q /ₘ M) + R := by
    have := modByMonic_add_div Q M
    rw [hR]; linear_combination -this
  have hRdeg : R.natDegree ≤ 1 := by
    have hM1 : M ≠ 1 := by
      intro h; rw [h] at hMdeg; simp at hMdeg
    have := natDegree_modByMonic_lt Q hMm hM1
    rw [hMdeg, ← hR] at this; omega
  have hRform : R = C (R.coeff 0) + C (R.coeff 1) * X := by
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hRdeg]
    ring
  set p := R.coeff 0
  set q := R.coeff 1
  set t := tU a E
  set σ := ((-E : ℤ) : ℝ) / tU a E
  have hMt : aeval t M = 0 := by
    rw [hM]; simp only [map_sub, map_add, map_pow, map_mul, aeval_X, aeval_C, eq_intCast, map_intCast,
      map_natCast]
    push_cast; linear_combination tU_quad hA
  have hMg : aeval σ M = 0 := by
    rw [hM]; simp only [map_sub, map_add, map_pow, map_mul, aeval_X, aeval_C, eq_intCast, map_intCast,
      map_natCast]
    push_cast; linear_combination sigma_quad hA
  have hQt : aeval t Q = p + q * t := by
    rw [hdecomp, map_add, map_mul, hMt, zero_mul, zero_add, hRform]; simp
  have hQg : aeval σ Q = p + q * σ := by
    rw [hdecomp, map_add, map_mul, hMg, zero_mul, zero_add, hRform]; simp
  have hprod : t * σ = -E := tU_mul_sigma hA
  have hsum : t + σ = -(a * E) := by
    have h1 := tU_quad hA
    have h2 := sigma_quad hA
    have hne : t ≠ σ := by
      intro h
      have hh := hprod
      rw [← h] at hh
      have htp := tU_pos hA
      have htl := tU_lt_one hA
      rcases E_cases hA with hE1 | hE1
      · rw [hE1] at hh; push_cast at hh; nlinarith
      · rw [hE1] at hh; push_cast at hh; nlinarith
    have : (t - σ) * (t + σ + a * E) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · linear_combination h
  refine ⟨p ^ 2 - a * E * p * q - E * q ^ 2, ?_, ?_⟩
  · rw [hQt, hQg]
    push_cast
    linear_combination (↑p * ↑q : ℝ) * hsum + (↑q : ℝ) ^ 2 * hprod
  · intro hne hz
    apply hne
    rw [hQt]
    have hEsq := E_sq hA
    -- 4(p² − aEpq − Eq²) = (2p − aEq)² − D q², so q = 0 by `√D ∉ ℚ`, then p = 0
    have hq : q = 0 := by
      by_contra hq
      apply sqrtD_irrational hA
      have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
      have hsq : (((2 * p - a * E * q : ℤ) : ℝ) / q) ^ 2 = (discr a E : ℝ) := by
        have : ((2 * p - a * E * q) ^ 2 : ℤ) = discr a E * q ^ 2 := by
          unfold discr; linear_combination 4 * hz + q ^ 2 * (a : ℤ) ^ 2 * hEsq
        have hR : (((2 * p - a * E * q) ^ 2 : ℤ) : ℝ) = ((discr a E * q ^ 2 : ℤ) : ℝ) := by rw [this]
        push_cast at hR ⊢
        field_simp
        linarith
      refine ⟨|((2 * p - a * E * q : ℤ) : ℚ) / q|, ?_⟩
      rw [Rat.cast_abs, Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast,
        ← Real.sqrt_sq (abs_nonneg _), sq_abs, hsq]
    have hp : p = 0 := by
      rw [hq] at hz; simpa using hz
    rw [hp, hq]; simp

/-! ### The final estimate -/

theorem bK_lower (K : ℕ) : (2 : ℝ) / 9 * ((K : ℝ) ^ 3 - K) ≤ 2 * (bK K : ℝ) := by
  have haj : ∀ j : ℕ, j * (j + 1) ≤ 6 * aj j := by
    intro j
    induction j with
    | zero => simp [aj]
    | succ j ih =>
      have : aj (j + 1) = aj j + (j + 1 + 2) / 3 := by
        unfold aj; rw [Finset.sum_Icc_succ_top (by omega)]
      rw [this]
      have : 3 * ((j + 1 + 2) / 3) ≥ j + 1 := by omega
      nlinarith
  have hsum : ∀ K : ℕ, (K : ℝ) ^ 3 - K = 3 * ∑ j ∈ range K, ((j : ℝ) * (j + 1)) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, mul_add, ← ih]; push_cast; ring
  rw [hsum]
  unfold bK
  push_cast
  rw [show (2 : ℝ) / 9 * (3 * ∑ j ∈ range K, (j : ℝ) * (j + 1)) =
      ∑ j ∈ range K, 2 / 9 * (3 * ((j : ℝ) * (j + 1))) by rw [Finset.mul_sum, Finset.mul_sum]]
  refine le_trans (Finset.sum_le_sum (g := fun i => 2 * (2 * (aj i : ℝ))) ?_)
    (le_of_eq (by rw [Finset.mul_sum, Finset.mul_sum]))
  intro j _
  have := haj j
  have hR : ((j : ℝ) * (j + 1)) ≤ 6 * (aj j : ℝ) := by exact_mod_cast this
  nlinarith

/-- Eventually `C (1 + log K)² + M < ε K`. -/
theorem eventually_log_sq_lt (C M ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ K : ℕ in atTop, C * (1 + Real.log K) ^ 2 + M < ε * K := by
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ 2 / (1 * x + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h2 : Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h3 : Tendsto (fun x : ℝ => (|C| + |M| + 1) * x⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul (|C| + |M| + 1)
  have hsum : Tendsto (fun x : ℝ => |C| * (Real.log x ^ 2 / (1 * x + 0)) +
      2 * |C| * (Real.log x ^ 1 / (1 * x + 0)) + (|C| + |M| + 1) * x⁻¹) atTop (𝓝 0) := by
    simpa using ((h1.const_mul |C|).add (h2.const_mul (2 * |C|))).add h3
  have hev := (hsum.eventually (gt_mem_nhds hε)).and
    ((eventually_ge_atTop (1 : ℝ)))
  have hevN := tendsto_natCast_atTop_atTop.eventually hev
  filter_upwards [hevN] with K ⟨hK, hK1⟩
  have hKpos : (0 : ℝ) < K := by linarith
  have hlog : 0 ≤ Real.log K := Real.log_nonneg hK1
  simp only [one_mul, add_zero, pow_one] at hK
  have key : |C| * (1 + Real.log K) ^ 2 + |M| <
      ε * K := by
    have := (mul_lt_mul_iff_of_pos_right hKpos).mpr hK
    have e : (|C| * (Real.log K ^ 2 / K) + 2 * |C| * (Real.log K / K) +
        (|C| + |M| + 1) * (K : ℝ)⁻¹) * K =
        |C| * (1 + Real.log K) ^ 2 + |M| + 1 := by
      field_simp; ring
    rw [e] at this; linarith
  have hC : C * (1 + Real.log K) ^ 2 ≤ |C| * (1 + Real.log K) ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  linarith [le_abs_self M]

/-- **Main theorem, conditional form.** -/
theorem irrational_zetaU_of {a : ℕ} {E : ℤ} (hA : Admissible a E)
    (hD : DecayBound (-E) (tU a E)) (hC : ConjBound (-E) (tU a E)) (hI : Integrality (-E))
    (hc : CostBound (-E) (tU a E)) (hN : Nonvanishing (-E) (tU a E)) : Irrational (zetaU a E) := by
  rintro ⟨r, hr⟩
  obtain ⟨C1, hC1, hD⟩ := hD
  obtain ⟨C2, hC2, hC⟩ := hC
  obtain ⟨C3, hc⟩ := hc
  set p : ℤ := r.num
  set b : ℕ := r.den
  have hb : (0 : ℝ) < b := by exact_mod_cast r.den_pos
  set t := tU a E with htdef
  set σ := ((-E : ℤ) : ℝ) / tU a E with hσdef
  set Dz : ℤ := discr a E
  have hDpos : (0 : ℝ) < Dz := by exact_mod_cast discr_pos hA
  set B : ℝ := (b : ℝ) * (Dz : ℝ) ^ 2 with hB
  have hBpos : 0 < B := by positivity
  have ht := tU_pos hA
  have hα1 := one_lt_alphaR hA
  have hlogα : 0 < Real.log t⁻¹ := by
    rw [htdef, tU, inv_inv]; exact Real.log_pos hα1
  set u : ℝ → ℝ := fun τ => p * (a + 2 * E * τ) / B with hu
  have hr' : zetaU a E = p / b := by rw [← hr]; exact (Rat.cast_def r)
  have hs := sD_pos hA
  have hsq := sD_sq hA
  have hXi : XiR (-E) t = u t := by
    have h := zetaU_eq hA
    rw [hr'] at h
    rw [hu]; simp only
    rw [← sD_eq_t hA, eq_div_iff hBpos.ne', hB]
    have h' : (p : ℝ) = Dz * sD a E * XiR (-E) t * b := by
      rw [div_eq_iff hb.ne'] at h; linarith
    rw [h']
    have : (Dz : ℝ) = sD a E ^ 2 := hsq.symm
    rw [this]; ring
  have hXi' : -XiR (-E) t = u σ := by
    rw [hXi, hu]; simp only
    rw [hσdef, sD_eq_sigma hA, ← sD_eq_t hA]; ring
  -- the integer polynomial `Q_K`
  have hY : ∀ K : ℕ, ∃ (N : ℕ) (Q : ℤ[X]), ∀ τ : ℝ, τ ≠ 0 → (∀ m : ℕ, 0 < m → τ ^ m ≠ 1) →
      τ ^ N * (aeval τ (CKpoly (-E) K) * B ^ K * (Delta (-E) τ K).eval (u τ)) = aeval τ Q := by
    intro K
    choose n A hA' using hI K
    refine ⟨∑ i ∈ range (K + 1), n i, ∑ i ∈ range (K + 1),
      A i * X ^ (∑ j ∈ range (K + 1), n j - n i) * C (((b : ℤ) * Dz ^ 2) ^ (K - i) * p ^ i) *
        (C (a : ℤ) + C (2 * E) * X) ^ i, ?_⟩
    intro τ hτ hroot
    rw [eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_Delta_le (-E) τ K)), Finset.mul_sum,
      Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hiK : i ≤ K := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hni : n i ≤ ∑ j ∈ range (K + 1), n j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) hi
    have hAi := hA' i τ hτ hroot
    have hτn : τ ^ n i ≠ 0 := pow_ne_zero _ hτ
    simp only [map_mul, map_pow, aeval_X, aeval_C, map_add, eq_intCast, map_natCast,
      map_intCast]
    have hpow : τ ^ (∑ j ∈ range (K + 1), n j) =
        τ ^ (∑ j ∈ range (K + 1), n j - n i) * τ ^ n i := by
      rw [← pow_add, Nat.sub_add_cancel hni]
    have hpowb : B ^ K = B ^ (K - i) * B ^ i := by
      rw [← pow_add, Nat.sub_add_cancel hiK]
    rw [hpow, hpowb]
    have hub : (u τ) ^ i * B ^ i = (p * (a + 2 * E * τ)) ^ i := by
      rw [← mul_pow]; congr 1; exact div_mul_cancel₀ _ hBpos.ne'
    calc τ ^ (∑ j ∈ range (K + 1), n j - n i) * τ ^ n i *
          (aeval τ (CKpoly (-E) K) * (B ^ (K - i) * B ^ i) *
            ((Delta (-E) τ K).coeff i * u τ ^ i))
        = τ ^ (∑ j ∈ range (K + 1), n j - n i) * (τ ^ n i *
            (aeval τ (CKpoly (-E) K) * (Delta (-E) τ K).coeff i)) * B ^ (K - i) *
            ((u τ) ^ i * B ^ i) := by ring
      _ = _ := by
        rw [hAi, hub, mul_div_cancel₀ _ hτn, mul_pow (p : ℝ), hB]
        push_cast
        ring
  -- the points `t` and `σt`
  have ht0 : t ≠ 0 := ht.ne'
  have htr : ∀ m : ℕ, 0 < m → t ^ m ≠ 1 := pow_ne_one_of_abs_ne_one (by
    rw [abs_of_pos ht]; exact (tU_lt_one hA).ne)
  have hE1 : |(E : ℝ)| = 1 := by
    rcases E_cases hA with h | h <;> simp [h]
  have hσabs : |σ| = alphaR a E := by
    rw [hσdef, sigma_eq hA, abs_mul, abs_neg, hE1, one_mul, abs_of_pos (alphaR_pos hA)]
  have hg0 : σ ≠ 0 := by
    intro h; have := hσabs; rw [h, abs_zero] at this; linarith [alphaR_pos hA]
  have hgr : ∀ m : ℕ, 0 < m → σ ^ m ≠ 1 := pow_ne_one_of_abs_ne_one (by
    rw [hσabs]; exact hα1.ne')
  have htσ : |t * σ| = 1 := by
    rw [hσdef, tU_mul_sigma hA, abs_neg, hE1]
  -- the key inequality for every `K` with `Δ_K(Ξ) ≠ 0`
  have hkey : ∀ K : ℕ, 1 ≤ K → (Delta (-E) t K).eval (XiR (-E) t) ≠ 0 →
      (11 / 900 : ℝ) * K ^ 3 * Real.log t⁻¹ ≤
        C3 * K ^ 2 * (1 + Real.log K) ^ 2 +
          K ^ 2 * (2 * |Real.log B| + |Real.log (C1 * C2)| + Real.log t⁻¹) := by
    intro K hK hne
    obtain ⟨N, Q, hQ⟩ := hY K
    have hQt := hQ t ht0 htr
    have hQg := hQ σ hg0 hgr
    rw [← hXi] at hQt
    rw [← hXi'] at hQg
    obtain ⟨z, hz, hz0⟩ := norm_ne_zero hA Q
    have hCt := aeval_CKpoly_ne_zero (-E) htr K
    have hQt0 : aeval t Q ≠ 0 := by
      rw [← hQt]
      exact mul_ne_zero (pow_ne_zero _ ht0) (mul_ne_zero (mul_ne_zero hCt (by positivity)) hne)
    have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
      have := hz0 hQt0
      exact_mod_cast Int.one_le_abs this
    set Yt := aeval t (CKpoly (-E) K) * B ^ K * (Delta (-E) t K).eval (XiR (-E) t)
    set Yg := aeval σ (CKpoly (-E) K) * B ^ K * (Delta (-E) σ K).eval (-XiR (-E) t)
    have hprod : |(z : ℝ)| = |Yt| * |Yg| := by
      rw [← hz, ← hQt, ← hQg]
      have e : t ^ N * Yt * (σ ^ N * Yg) = (t * σ) ^ N * (Yt * Yg) := by rw [mul_pow]; ring
      rw [e, abs_mul, abs_mul, abs_pow, htσ, one_pow, one_mul]
    have hDt := hD K hK
    have hDg := hC K hK
    have hcK := hc K hK
    set P := |aeval t (CKpoly (-E) K) * aeval σ (CKpoly (-E) K)|
    have hbig : (1 : ℝ) ≤ P * B ^ (2 * K) * (C1 * C2) ^ (K ^ 2) *
        t ^ (2 * bK K + K ^ 2 * (K + 1)) := by
      calc (1 : ℝ) ≤ |Yt| * |Yg| := by rw [← hprod]; exact hz1
        _ = P * B ^ (2 * K) * (|(Delta (-E) t K).eval (XiR (-E) t)| *
              |(Delta (-E) σ K).eval (-XiR (-E) t)|) := by
            simp only [Yt, Yg, P, abs_mul, abs_pow]
            rw [abs_of_pos hBpos]
            ring
        _ ≤ P * B ^ (2 * K) * ((C1 ^ (K ^ 2) * t ^ (2 * bK K)) *
              (C2 ^ (K ^ 2) * t ^ (K ^ 2 * (K + 1)))) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg (abs_nonneg _) (by positivity))
            exact mul_le_mul hDt hDg (abs_nonneg _)
              (mul_nonneg (pow_nonneg hC1.le _) (pow_nonneg ht.le _))
        _ = _ := by rw [mul_pow, pow_add]; ring
    have hPpos : 0 < P := by
      have hP0 : 0 ≤ P := abs_nonneg _
      rcases hP0.lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hbig; simp at hbig; linarith
    have hlog := Real.log_le_log one_pos hbig
    have hlogt : Real.log t = -Real.log t⁻¹ := by rw [Real.log_inv]; ring
    rw [Real.log_one, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, hlogt] at hlog
    have hbK := bK_lower K
    have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
    push_cast at hlog
    have hK2 : (K : ℝ) ≤ K ^ 2 := by nlinarith only [hKR]
    have e1a := mul_le_mul_of_nonneg_left (le_abs_self (Real.log B))
      (by positivity : (0 : ℝ) ≤ 2 * K)
    have e1b := mul_le_mul_of_nonneg_right hK2 (abs_nonneg (Real.log B))
    have e2 := mul_le_mul_of_nonneg_left (le_abs_self (Real.log (C1 * C2))) (sq_nonneg (K : ℝ))
    have hb' := mul_le_mul_of_nonneg_right hbK hlogα.le
    have hk' : (K : ℝ) * Real.log t⁻¹ ≤ K ^ 2 * Real.log t⁻¹ :=
      mul_le_mul_of_nonneg_right hK2 hlogα.le
    have hk3 : (0 : ℝ) ≤ K ^ 2 * Real.log t⁻¹ := by positivity
    linarith only [hcK, hlog, hb', e1a, e1b, e2, hk', hk3]
  -- contradiction for large `K`
  have hev := eventually_log_sq_lt C3
    (2 * |Real.log B| + |Real.log (C1 * C2)| + Real.log t⁻¹) (11 / 900 * Real.log t⁻¹)
    (by positivity)
  obtain ⟨K0, hK0⟩ := eventually_atTop.mp hev
  obtain ⟨K, hK, hne⟩ := hN (K0 + 1)
  have hK1 : 1 ≤ K := by omega
  have h1 := hkey K hK1 hne
  have h2 := hK0 K (by omega)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  have hK2 : (0 : ℝ) < K ^ 2 := by positivity
  have : (11 / 900 : ℝ) * K ^ 3 * Real.log t⁻¹ =
      K ^ 2 * (11 / 900 * Real.log t⁻¹ * K) := by ring
  rw [this] at h1
  have h3 : C3 * K ^ 2 * (1 + Real.log K) ^ 2 +
      K ^ 2 * (2 * |Real.log B| + |Real.log (C1 * C2)| + Real.log t⁻¹) =
      K ^ 2 * (C3 * (1 + Real.log K) ^ 2 +
        (2 * |Real.log B| + |Real.log (C1 * C2)| + Real.log t⁻¹)) := by ring
  rw [h3] at h1
  have := (mul_le_mul_iff_of_pos_left hK2).mp h1
  linarith

end LucasU
