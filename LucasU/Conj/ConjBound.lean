-- Generalised from lean_fibzeta FibZeta/Conj/ConjBound.lean (ε = ±1, general t).
import LucasU.Conj.Entry

/-!
# Proposition 4: conjugate smallness (`ConjBound`)

`σΔ_K(−Ξ) = det[nrm · T_{i+j}] = nrm^K det[T_{i+j}]` with `|nrm(ε/t, K)| = t^{K(K+1)}`
(`abs_nrm_conj`), so `|nrm|^K = t^{K²(K+1)}`.  Every entry satisfies
`|T_k| ≤ (1 − t²)^{−K} (k²(k+1)/(1 − t) + c_B) ≤ D^K` for `k < 2K` (`abs_T_le_pow`), and the
permutation bound `|det| ≤ K! (D^K)^K ≤ (2D)^{K²}` finishes the proof.  The constant `D` depends
on `t` only.
-/

open Polynomial Finset

namespace LucasU.Conj

variable {ε : ℤ} {t : ℝ}

theorem abs_T_le (h : Good ε t) {K : ℕ} (hK : 1 ≤ K) (k : ℕ) :
    |T ε t K k| ≤ k * (BE t K * ((k : ℝ) * ((k : ℝ) + 1) * (1 - t)⁻¹)) + BE t K * cB t := by
  rw [T_eq, partB_eq h]
  exact (abs_add_le _ _).trans (add_le_add (abs_Lpoly_le h hK k) (abs_partB_le h K k))

theorem cB_nonneg (h : Good ε t) : 0 ≤ cB t := by
  have h3 := Good.cube_lt_one h
  have h2 : 0 < 1 - t ^ 2 := by linarith [Good.sq_lt_one h]
  unfold cB
  have : 0 < (1 - t ^ 3)⁻¹ := inv_pos.mpr (by linarith)
  have : 0 < 1 / (1 - t ^ 2) ^ 3 := by positivity
  have : 0 < t ^ 3 := pow_pos (Good.t_pos h) 3
  positivity

/-- The base of the entry bound `|T_k| ≤ D^K`. -/
noncomputable def Dc (t : ℝ) : ℝ := (1 - t ^ 2)⁻¹ * 8 * max (8 * (1 - t)⁻¹ + cB t) 1

theorem Dc_pos (h : Good ε t) : 0 < Dc t := by
  have h2 : 0 < 1 - t ^ 2 := by linarith [Good.sq_lt_one h]
  unfold Dc
  have : 0 < max (8 * (1 - t)⁻¹ + cB t) 1 := lt_max_of_lt_right one_pos
  have : 0 < (1 - t ^ 2)⁻¹ := inv_pos.mpr h2
  positivity

theorem abs_T_le_pow (h : Good ε t) {K : ℕ} (hK : 1 ≤ K) {k : ℕ} (hk : k < 2 * K) :
    |T ε t K k| ≤ Dc t ^ K := by
  set c₀ := 8 * (1 - t)⁻¹ + cB t with hc₀
  set c₁ := max c₀ 1 with hc₁
  have hinv : 0 ≤ (1 - t)⁻¹ := inv_nonneg.mpr (by linarith [Good.t_lt_one h])
  have hk1 : (k : ℝ) ≤ 2 * K := by exact_mod_cast hk.le
  have hk2 : (k : ℝ) + 1 ≤ 2 * K := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h8 : (k : ℝ) * ((k : ℝ) * ((k : ℝ) + 1)) ≤ 8 * (K : ℝ) ^ 3 := by
    have := mul_le_mul hk1 (mul_le_mul hk1 hk2 (by positivity) (by positivity))
      (by positivity) (by positivity)
    nlinarith
  have hK3 : (1 : ℝ) ≤ (K : ℝ) ^ 3 := one_le_pow₀ (by exact_mod_cast hK)
  have hcB := cB_nonneg h
  have hK8 : (K : ℝ) ^ 3 ≤ 8 ^ K := by
    have : (K : ℝ) ≤ 2 ^ K := by exact_mod_cast Nat.lt_two_pow_self.le
    calc (K : ℝ) ^ 3 ≤ (2 ^ K) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) this 3
      _ = 8 ^ K := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hc₀1 : c₀ ≤ c₁ ^ K := (le_max_left _ _).trans (le_self_pow₀ (le_max_right _ _) (by omega))
  have hc₀0 : 0 ≤ c₀ := by positivity
  calc |T ε t K k|
      ≤ BE t K * ((k : ℝ) * ((k : ℝ) * ((k : ℝ) + 1)) * (1 - t)⁻¹ + cB t) :=
        (abs_T_le h hK k).trans_eq (by ring)
    _ ≤ BE t K * ((K : ℝ) ^ 3 * c₀) := by
        refine mul_le_mul_of_nonneg_left ?_ (BE_nonneg h K)
        rw [hc₀]
        nlinarith [mul_le_mul_of_nonneg_right h8 hinv, mul_le_mul_of_nonneg_right hK3 hcB]
    _ ≤ BE t K * (8 ^ K * c₁ ^ K) := by
        refine mul_le_mul_of_nonneg_left ?_ (BE_nonneg h K)
        exact mul_le_mul hK8 hc₀1 hc₀0 (by positivity)
    _ = Dc t ^ K := by rw [Dc, BE, mul_pow, mul_pow]; ring

theorem eval_Delta (ε : ℤ) (τ x : ℝ) (K : ℕ) :
    (Delta ε τ K).eval x = Matrix.det (Matrix.of fun i j : Fin K =>
      nrm ε τ K * (mConst ε τ K (i.val + j.val) + x * mLin ε τ K (i.val + j.val))) := by
  rw [Delta, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [hankelLin, hankelConst]
  ring

theorem abs_nrm_conj (h : Good ε t) (K : ℕ) :
    |nrm ε ((ε : ℝ) / t) K| = t ^ (K * (K + 1)) := by
  have h2 : 2 * AK K = K * (K + 1) := by
    unfold AK; exact Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self K)
  rw [nrm, wpar_conj h, inv_pow, inv_inv, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_pow, abs_wpar h, ← pow_mul, h2]

/-- **Proposition 4** (conjugate smallness), for `ε = ±1` and `0 < t ≤ φ⁻¹`. -/
theorem conjBound {ε : ℤ} {t : ℝ} (h : Good ε t) : ConjBound ε t := by
  refine ⟨2 * Dc t, by linarith [Dc_pos h], fun K hK => ?_⟩
  rw [eval_Delta]
  have hmat : (Matrix.of fun i j : Fin K => nrm ε ((ε : ℝ) / t) K *
      (mConst ε ((ε : ℝ) / t) K (i.val + j.val) +
        (-XiR ε t) * mLin ε ((ε : ℝ) / t) K (i.val + j.val))) =
      nrm ε ((ε : ℝ) / t) K • Matrix.of fun i j : Fin K => T ε t K (i.val + j.val) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, T]
    ring
  rw [hmat, Matrix.det_smul, Fintype.card_fin, abs_mul, abs_pow, abs_nrm_conj h]
  have hdet := Matrix.det_le (abv := AbsoluteValue.abs)
    (A := Matrix.of fun i j : Fin K => T ε t K (i.val + j.val)) (x := Dc t ^ K)
    (fun i j => by
      simp only [AbsoluteValue.abs_apply, Matrix.of_apply]
      exact abs_T_le_pow h hK (by omega))
  simp only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] at hdet
  have hfac : (K.factorial : ℝ) ≤ (2 ^ K) ^ K := by
    exact_mod_cast (Nat.factorial_le_pow K).trans (Nat.pow_le_pow_left Nat.lt_two_pow_self.le K)
  have hD : 0 ≤ Dc t ^ K := pow_nonneg (Dc_pos h).le K
  have ht : 0 ≤ (t ^ (K * (K + 1))) ^ K := pow_nonneg (pow_nonneg (Good.t_pos h).le _) K
  calc (t ^ (K * (K + 1))) ^ K *
        |Matrix.det (Matrix.of fun i j : Fin K => T ε t K (i.val + j.val))|
      ≤ (t ^ (K * (K + 1))) ^ K * ((2 ^ K) ^ K * (Dc t ^ K) ^ K) := by
        refine mul_le_mul_of_nonneg_left (hdet.trans ?_) ht
        exact mul_le_mul_of_nonneg_right hfac (pow_nonneg hD K)
    _ = (2 * Dc t) ^ (K ^ 2) * t ^ (K ^ 2 * (K + 1)) := by
        rw [← pow_mul, ← pow_mul, ← pow_mul, ← mul_pow, show K * K = K ^ 2 by ring,
          show K * (K + 1) * K = K ^ 2 * (K + 1) by ring]
        ring

end LucasU.Conj
