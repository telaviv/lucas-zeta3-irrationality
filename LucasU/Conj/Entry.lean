-- Generalised from lean_fibzeta FibZeta/Conj/Entry.lean (ε = ±1, general t).
import LucasU.Conj.Conjugate

/-!
# The entries `T_k = σL_X(s^k/F)` at `X = −Ξ` are bounded (PROOF_U §4, PROOF §4)

`T ε t K k = mConst(ε/t, K, k) − Ξ · mLin(ε/t, K, k)` splits as

* the polynomial part `Lpoly (X^k /ₘ F)`, whose coefficients are `E rr K (k − 1 − j)`
  (`coeff_divByMonic`), bounded by `(1 − t²)^{−K}` (`E_bound`), against `|ν_j(ε/t)| ≤ j(j+1)/(1 − t)`;
* the pole part `2 ∑_a res_a (ε/t)^a (S_a(ε/t) + Ξ)`, which after expanding
  `2(ε/t)^a (S_a(ε/t) + Ξ) = ∑_M 2 r_a t^{3(M+1)} ∑_j C(j+2,2) (r_a w^{M+1})^j` and exchanging the
  finite sum over `a` with the two series becomes `∑_M ∑_j c_{M,j} E rr K (k + j + 1)`
  (`partB_eq`); each `E` is bounded, so the double series is bounded (`abs_partB_le`).
-/

open Polynomial Finset

namespace LucasU.Conj

variable {ε : ℤ} {t : ℝ}

/-- `T_k = L_X(s^k/F)` at `τ = ε/t`, `X = −Ξ`. -/
noncomputable def T (ε : ℤ) (t : ℝ) (K k : ℕ) : ℝ :=
  mConst ε ((ε : ℝ) / t) K k - XiR ε t * mLin ε ((ε : ℝ) / t) K k

/-- The bound `(1 − t²)^{−K}` on all `E rr K m`. -/
noncomputable def BE (t : ℝ) (K : ℕ) : ℝ := ((1 - t ^ 2)⁻¹) ^ K

theorem BE_nonneg (h : Good ε t) (K : ℕ) : 0 ≤ BE t K := by
  unfold BE; exact pow_nonneg (inv_nonneg.mpr (by linarith [Good.sq_lt_one h])) K

theorem abs_E_rr_le (h : Good ε t) (K m : ℕ) : |E (rr ε t) K m| ≤ BE t K :=
  E_bound (Good.sq_pos h).le (Good.sq_lt_one h) (fun _ ha => abs_rr_le h ha)
    (rr_injective h).injOn K m

theorem T_eq (K k : ℕ) :
    T ε t K k = Lpoly ε ((ε : ℝ) / t) (X ^ k /ₘ F ε ((ε : ℝ) / t) K) +
      2 * ∑ a ∈ Icc 1 K, res ε ((ε : ℝ) / t) K k a * ((ε : ℝ) / t) ^ a *
        (S ε ((ε : ℝ) / t) a + XiR ε t) := by
  rw [T, mConst, mLin]
  have : ∑ a ∈ Icc 1 K, res ε ((ε : ℝ) / t) K k a * ((ε : ℝ) / t) ^ a *
        (S ε ((ε : ℝ) / t) a + XiR ε t) =
      ∑ a ∈ Icc 1 K, res ε ((ε : ℝ) / t) K k a * ((ε : ℝ) / t) ^ a * S ε ((ε : ℝ) / t) a +
      (∑ a ∈ Icc 1 K, res ε ((ε : ℝ) / t) K k a * ((ε : ℝ) / t) ^ a) * XiR ε t := by
    rw [sum_mul, ← sum_add_distrib]
    exact sum_congr rfl fun a _ => by ring
  rw [this]; ring

/-! ### The polynomial part -/

theorem abs_Lpoly_le (h : Good ε t) {K : ℕ} (hK : 1 ≤ K) (k : ℕ) :
    |Lpoly ε ((ε : ℝ) / t) (X ^ k /ₘ F ε ((ε : ℝ) / t) K)| ≤
      k * (BE t K * ((k : ℝ) * ((k : ℝ) + 1) * (1 - t)⁻¹)) := by
  rw [F_conj h]
  have hcoeff := coeff_divByMonic hK (rr_injective h).injOn k
  have hsupp : (X ^ k /ₘ Lagrange.nodal (Icc 1 K) (rr ε t)).support ⊆ range k := by
    intro j hj
    rw [mem_support_iff, hcoeff] at hj
    rw [mem_range]
    by_contra h'
    exact hj (by simp [h'])
  have hc0 : 0 ≤ (1 - t)⁻¹ := inv_nonneg.mpr (by linarith [Good.t_lt_one h])
  rw [Lpoly]
  calc |∑ j ∈ (X ^ k /ₘ Lagrange.nodal (Icc 1 K) (rr ε t)).support,
          (X ^ k /ₘ Lagrange.nodal (Icc 1 K) (rr ε t)).coeff j * nu ε ((ε : ℝ) / t) j|
      ≤ ∑ j ∈ (X ^ k /ₘ Lagrange.nodal (Icc 1 K) (rr ε t)).support,
          |(X ^ k /ₘ Lagrange.nodal (Icc 1 K) (rr ε t)).coeff j * nu ε ((ε : ℝ) / t) j| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range k,
          |(X ^ k /ₘ Lagrange.nodal (Icc 1 K) (rr ε t)).coeff j * nu ε ((ε : ℝ) / t) j| :=
        sum_le_sum_of_subset_of_nonneg hsupp (fun _ _ _ => abs_nonneg _)
    _ ≤ ∑ _j ∈ range k, BE t K * ((k : ℝ) * ((k : ℝ) + 1) * (1 - t)⁻¹) := by
        refine sum_le_sum fun j hj => ?_
        have hjk : (j : ℝ) ≤ k := by exact_mod_cast (mem_range.mp hj).le
        have hc : |(X ^ k /ₘ Lagrange.nodal (Icc 1 K) (rr ε t)).coeff j| ≤ BE t K := by
          rw [hcoeff]
          split_ifs
          · exact abs_E_rr_le h _ _
          · rw [abs_zero]; exact BE_nonneg h K
        have hn : |nu ε ((ε : ℝ) / t) j| ≤ (k : ℝ) * ((k : ℝ) + 1) * (1 - t)⁻¹ := by
          refine (abs_nu_conj h j).trans ?_
          have : (j : ℝ) * ((j : ℝ) + 1) ≤ (k : ℝ) * ((k : ℝ) + 1) := by
            have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
            nlinarith
          exact mul_le_mul_of_nonneg_right this hc0
        rw [abs_mul]
        exact mul_le_mul hc hn (abs_nonneg _) (BE_nonneg h K)
    _ = k * (BE t K * ((k : ℝ) * ((k : ℝ) + 1) * (1 - t)⁻¹)) := by
        rw [sum_const, card_range, nsmul_eq_mul]

/-! ### The pole part -/

/-- `c_{M,j} = 2 t^{3(M+1)} C(j+2,2) w^{(M+1)j}`. -/
noncomputable def cc (ε : ℤ) (t : ℝ) (M j : ℕ) : ℝ :=
  2 * (t ^ 3) ^ (M + 1) * ((j + 2).choose 2 : ℝ) * (wpar ε t ^ (M + 1)) ^ j

theorem partB_eq (h : Good ε t) (K k : ℕ) :
    2 * ∑ a ∈ Icc 1 K, res ε ((ε : ℝ) / t) K k a * ((ε : ℝ) / t) ^ a *
        (S ε ((ε : ℝ) / t) a + XiR ε t) =
      ∑' M : ℕ, ∑' j : ℕ, cc ε t M j * E (rr ε t) K (k + j + 1) := by
  -- the summand, indexed by node `a`, outer index `M`, inner index `j`
  set f : ℕ → ℕ → ℕ → ℝ := fun a M j =>
    res ε ((ε : ℝ) / t) K k a * (cc ε t M j * rr ε t a ^ (j + 1)) with hf
  have hx : ∀ a M, ‖rr ε t a * wpar ε t ^ (M + 1)‖ < 1 := fun a M => by
    rw [Real.norm_eq_abs]; exact (abs_rr_mul_q_le h a M).trans_lt (Good.sq_lt_one h)
  have hterm : ∀ a M j, f a M j =
      res ε ((ε : ℝ) / t) K k a * (2 * rr ε t a * (t ^ 3) ^ (M + 1)) *
        (((j + 2).choose 2 : ℝ) * (rr ε t a * wpar ε t ^ (M + 1)) ^ j) := by
    intro a M j; simp only [hf, cc]; ring
  have hsumj : ∀ a M, Summable (f a M) := fun a M => by
    have := (summable_choose_mul_geometric_of_norm_lt_one 2 (hx a M)).mul_left
      (res ε ((ε : ℝ) / t) K k a * (2 * rr ε t a * (t ^ 3) ^ (M + 1)))
    exact this.congr fun j => (hterm a M j).symm
  have hinner : ∀ a M, ∑' j, f a M j =
      res ε ((ε : ℝ) / t) K k a * (2 * ((ε : ℝ) / t) ^ a * psi ε t (M + a + 1)) := by
    intro a M
    simp_rw [hterm]
    rw [tsum_mul_left, ← inv_one_sub_cube (by simpa [Real.norm_eq_abs] using hx a M),
      two_conj_psi h]
    ring
  have hsumM : ∀ a, Summable (fun M => ∑' j, f a M j) := fun a => by
    simp_rw [hinner]
    have hs : Summable (fun M => psi ε t (M + (a + 1))) :=
      (summable_nat_add_iff (a + 1)).mpr (summable_psi h)
    have := hs.mul_left (res ε ((ε : ℝ) / t) K k a * (2 * ((ε : ℝ) / t) ^ a))
    simpa only [add_assoc, mul_assoc] using this
  have hstep1 : ∀ a, 2 * (res ε ((ε : ℝ) / t) K k a * ((ε : ℝ) / t) ^ a *
      (S ε ((ε : ℝ) / t) a + XiR ε t)) = ∑' M, ∑' j, f a M j := by
    intro a
    simp_rw [hinner]
    rw [S_add_Xi h, tsum_mul_left, tsum_mul_left]
    ring
  rw [mul_sum, sum_congr rfl fun a _ => hstep1 a,
    ← Summable.tsum_finsetSum fun a _ => hsumM a]
  refine tsum_congr fun M => ?_
  rw [← Summable.tsum_finsetSum fun a _ => hsumj a M]
  refine tsum_congr fun j => ?_
  rw [E, mul_sum]
  refine sum_congr rfl fun a ha => ?_
  simp only [hf]
  rw [res_conj h ha, show k + j + 1 = k + (j + 1) by ring, pow_add]
  ring

/-- The constant of the pole part: `2 t³/(1 − t³) · (1 − t²)^{−3}`. -/
noncomputable def cB (t : ℝ) : ℝ := 2 * t ^ 3 * (1 - t ^ 3)⁻¹ * (1 / (1 - t ^ 2) ^ 3)

theorem abs_partB_le (h : Good ε t) (K k : ℕ) :
    |∑' M : ℕ, ∑' j : ℕ, cc ε t M j * E (rr ε t) K (k + j + 1)| ≤ BE t K * cB t := by
  have ht3 : 0 ≤ t ^ 3 := (pow_pos (Good.t_pos h) 3).le
  have ht3' : t ^ 3 < 1 := Good.cube_lt_one h
  have hq : ∀ M : ℕ, |wpar ε t ^ (M + 1)| ≤ t ^ 2 := fun M => abs_wpar_pow_le h (by omega)
  have hgeo2 : HasSum (fun j : ℕ => ((j + 2).choose 2 : ℝ) * (t ^ 2) ^ j)
      (1 / (1 - t ^ 2) ^ (2 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 2
      (by rw [Real.norm_eq_abs, abs_of_pos (Good.sq_pos h)]; exact Good.sq_lt_one h)
  -- inner bound
  have hin : ∀ M : ℕ, ‖∑' j : ℕ, cc ε t M j * E (rr ε t) K (k + j + 1)‖ ≤
      2 * (t ^ 3) ^ (M + 1) * BE t K * (1 / (1 - t ^ 2) ^ (2 + 1)) := by
    intro M
    refine tsum_of_norm_bounded (hgeo2.mul_left (2 * (t ^ 3) ^ (M + 1) * BE t K)) fun j => ?_
    have hA : 0 ≤ 2 * (t ^ 3) ^ (M + 1) * ((j + 2).choose 2 : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg ht3 _)) (Nat.cast_nonneg _)
    rw [Real.norm_eq_abs, cc, abs_mul, abs_mul, abs_pow, abs_of_nonneg hA]
    have h1 : |wpar ε t ^ (M + 1)| ^ j ≤ (t ^ 2) ^ j :=
      pow_le_pow_left₀ (abs_nonneg _) (hq M) j
    have h2 := abs_E_rr_le h K (k + j + 1)
    calc 2 * (t ^ 3) ^ (M + 1) * ((j + 2).choose 2 : ℝ) * |wpar ε t ^ (M + 1)| ^ j *
          |E (rr ε t) K (k + j + 1)|
        ≤ 2 * (t ^ 3) ^ (M + 1) * ((j + 2).choose 2 : ℝ) * (t ^ 2) ^ j * BE t K :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hA) h2 (abs_nonneg _)
            (mul_nonneg hA (pow_nonneg (Good.sq_pos h).le j))
      _ = 2 * (t ^ 3) ^ (M + 1) * BE t K * (((j + 2).choose 2 : ℝ) * (t ^ 2) ^ j) := by ring
  have hgeo3 : HasSum (fun M : ℕ => (t ^ 3) ^ M) (1 - t ^ 3)⁻¹ :=
    hasSum_geometric_of_lt_one ht3 ht3'
  have hout := hgeo3.mul_left (2 * t ^ 3 * BE t K * (1 / (1 - t ^ 2) ^ (2 + 1)))
  calc |∑' M : ℕ, ∑' j : ℕ, cc ε t M j * E (rr ε t) K (k + j + 1)|
      = ‖∑' M : ℕ, ∑' j : ℕ, cc ε t M j * E (rr ε t) K (k + j + 1)‖ := (Real.norm_eq_abs _).symm
    _ ≤ 2 * t ^ 3 * BE t K * (1 / (1 - t ^ 2) ^ (2 + 1)) * (1 - t ^ 3)⁻¹ :=
        tsum_of_norm_bounded hout fun M => (hin M).trans_eq (by ring)
    _ = BE t K * cB t := by rw [cB]; ring

end LucasU.Conj
