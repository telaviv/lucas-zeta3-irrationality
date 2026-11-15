-- Generalised from lean_fibzeta FibZeta/Conj/Conjugate.lean (ε = ±1, general t).
import LucasU.Statements
import LucasU.Conj.DivDiff

/-!
# The construction at the conjugate point `τ = ε/t` (PROOF_U §4, PROOF §4)

Write `w = wpar ε t = ε t²`.  At `τ = ε/t` (for `ε = ±1`, `t ≠ 0`):

* `wpar ε (ε/t) = w⁻¹` (`wpar_conj`), so the nodes are `node a = w^a =: rr ε t a`, `|rr a| = t^{2a}`;
* `ψ_N(ε/t) = −ψ_N(t)` (`psi_conj`), hence `S_a(ε/t) + Ξ = ∑_{N > a} ψ_N(t)` (`S_add_Xi`);
* `2(ε/t)^a ψ_{a+M+1}(t) = 2 r_a t^{3(M+1)} (1 − r_a w^{M+1})^{−3}` (`two_conj_psi`; the function
  `Γ(r_a)` of PROOF §4, summand by summand; it is the same for both signs);
* `|ν_j(ε/t)| ≤ j(j+1)/(1 − t)` (`abs_nu_conj`), since `|α_j(ε/t)| = t^{−1−2j} ≥ t⁻¹`.

Only `ε² = 1` and `0 < t < 1` are used.
-/

open Polynomial Finset

namespace LucasU.Conj

variable {ε : ℤ} {t : ℝ}

theorem eps_sq (hε : ε = 1 ∨ ε = -1) : (ε : ℝ) ^ 2 = 1 := by
  rcases hε with rfl | rfl <;> norm_num

theorem abs_eps (hε : ε = 1 ∨ ε = -1) : |(ε : ℝ)| = 1 := by
  rcases hε with rfl | rfl <;> norm_num

theorem eps_pow (hε : ε = 1 ∨ ε = -1) (n : ℕ) : (ε : ℝ) ^ n = 1 ∨ (ε : ℝ) ^ n = -1 := by
  rcases hε with rfl | rfl
  · left; simp
  · push_cast; exact neg_one_pow_eq_or ℝ n

theorem Good.t_pos (h : Good ε t) : 0 < t := h.2.1

theorem Good.t_lt_one (h : Good ε t) : t < 1 :=
  h.2.2.trans_lt (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)

theorem Good.sq_pos (h : Good ε t) : 0 < t ^ 2 := by have := (Good.t_pos h); positivity

theorem Good.sq_lt_one (h : Good ε t) : t ^ 2 < 1 := by
  have := (Good.t_pos h); have := (Good.t_lt_one h); nlinarith

theorem Good.cube_lt_one (h : Good ε t) : t ^ 3 < 1 :=
  pow_lt_one₀ (Good.t_pos h).le (Good.t_lt_one h) (by norm_num)

/-- The conjugate nodes `r_a = w^a`, `w = ε t²`. -/
noncomputable def rr (ε : ℤ) (t : ℝ) (a : ℕ) : ℝ := wpar ε t ^ a

theorem abs_wpar (h : Good ε t) : |wpar ε t| = t ^ 2 := by
  rw [wpar, abs_mul, abs_eps h.1, one_mul, abs_of_pos (Good.sq_pos h)]

theorem abs_wpar_pow_le (h : Good ε t) {n : ℕ} (hn : 1 ≤ n) : |wpar ε t ^ n| ≤ t ^ 2 := by
  rw [abs_pow, abs_wpar h]; exact pow_le_of_le_one (Good.sq_pos h).le (Good.sq_lt_one h).le (by omega)

theorem abs_rr (h : Good ε t) (a : ℕ) : |rr ε t a| = (t ^ 2) ^ a := by
  rw [rr, abs_pow, abs_wpar h]

theorem abs_rr_le (h : Good ε t) {a : ℕ} (ha : 1 ≤ a) : |rr ε t a| ≤ t ^ 2 :=
  abs_wpar_pow_le h ha

theorem abs_rr_le_one (h : Good ε t) (a : ℕ) : |rr ε t a| ≤ 1 := by
  rw [abs_rr h]; exact pow_le_one₀ (Good.sq_pos h).le (Good.sq_lt_one h).le

theorem rr_injective (h : Good ε t) : Function.Injective (rr ε t) := by
  intro a b hab
  have : (t ^ 2) ^ a = (t ^ 2) ^ b := by rw [← abs_rr h, ← abs_rr h, hab]
  exact pow_right_injective₀ (Good.sq_pos h) (Good.sq_lt_one h).ne this

theorem wpar_conj (h : Good ε t) : wpar ε ((ε : ℝ) / t) = (wpar ε t)⁻¹ := by
  have ht := (Good.t_pos h).ne'
  rcases h.1 with rfl | rfl
  · simp [wpar]
  · simp only [wpar]; push_cast; field_simp

theorem node_conj (h : Good ε t) (a : ℕ) : node ε ((ε : ℝ) / t) a = rr ε t a := by
  rw [node, wpar_conj h, inv_pow, inv_inv, rr]

theorem F_conj (h : Good ε t) (K : ℕ) :
    F ε ((ε : ℝ) / t) K = Lagrange.nodal (Icc 1 K) (rr ε t) := by
  rw [F, Lagrange.nodal_eq]
  exact prod_congr rfl fun a _ => by rw [node_conj h]

theorem res_conj (h : Good ε t) {K k a : ℕ} (ha : a ∈ Icc 1 K) :
    res ε ((ε : ℝ) / t) K k a = rr ε t a ^ k * Lagrange.nodalWeight (Icc 1 K) (rr ε t) a := by
  rw [res, node_conj h, F_conj h, Lagrange.nodalWeight_eq_eval_derivative_nodal ha,
    div_eq_mul_inv]

/-! ### `ψ_N` at `ε/t` and the tail `S_a(ε/t) + Ξ` -/

theorem psi_conj (h : Good ε t) (N : ℕ) : psi ε ((ε : ℝ) / t) N = -psi ε t N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [psi]
  have ht := (Good.t_pos h)
  set T := t ^ N with hT
  have hT0 : 0 < T := by positivity
  have hT1 : T < 1 := pow_lt_one₀ ht.le (Good.t_lt_one h) hN.ne'
  have e1 : ((ε : ℝ) / t) ^ (3 * N) = ((ε : ℝ) ^ N / T) ^ 3 := by
    rw [mul_comm 3 N, pow_mul, div_pow]
  have e2 : wpar ε t ^ N = (ε : ℝ) ^ N * T ^ 2 := by
    rw [wpar, mul_pow, ← pow_mul, mul_comm 2 N, pow_mul]
  have e3 : t ^ (3 * N) = T ^ 3 := by rw [mul_comm 3 N, pow_mul]
  rw [psi, psi, wpar_conj h, inv_pow, e1, e2, e3]
  have hA : T ^ 2 - 1 ≠ 0 := by nlinarith
  have hB : 1 - T ^ 2 ≠ 0 := by nlinarith
  have hC : T ^ 2 + 1 ≠ 0 := by nlinarith
  rcases eps_pow h.1 N with he | he <;> rw [he]
  · have : 1 - (1 * T ^ 2)⁻¹ = (T ^ 2 - 1) / T ^ 2 := by field_simp
    rw [this]; field_simp; ring
  · have : 1 - (-1 * T ^ 2)⁻¹ = (T ^ 2 + 1) / T ^ 2 := by field_simp; ring
    rw [this]
    have : 1 - -1 * T ^ 2 = T ^ 2 + 1 := by ring
    rw [this]; field_simp

theorem abs_psi_le (h : Good ε t) (N : ℕ) :
    |psi ε t N| ≤ (t ^ 3) ^ N * ((1 - t ^ 2)⁻¹) ^ 3 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simpa [psi] using pow_nonneg (by linarith [(Good.sq_lt_one h)] : (0 : ℝ) ≤ 1 - t ^ 2) 3
  have h1 : 1 - t ^ 2 ≤ |1 - wpar ε t ^ N| := by
    have h2 := abs_wpar_pow_le h (n := N) hN
    have := abs_sub_abs_le_abs_sub 1 (wpar ε t ^ N)
    rw [abs_one] at this; linarith
  have h0 : 0 < 1 - t ^ 2 := by linarith [(Good.sq_lt_one h)]
  rw [psi, abs_div, abs_pow, abs_of_pos (Good.t_pos h), abs_pow, ← pow_mul, inv_pow, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (pow_pos (Good.t_pos h) _).le (pow_pos h0 3)
    (pow_le_pow_left₀ h0.le h1 3)

/-- `∑ ψ_N(t)` converges (exported). -/
theorem summable_psi (h : Good ε t) : Summable (fun N => psi ε t N) := by
  have hg : Summable (fun N : ℕ => (t ^ 3) ^ N * ((1 - t ^ 2)⁻¹) ^ 3) :=
    (summable_geometric_of_lt_one (pow_pos (Good.t_pos h) 3).le (Good.cube_lt_one h)).mul_right _
  exact Summable.of_norm_bounded hg fun N => by rw [Real.norm_eq_abs]; exact abs_psi_le h N

theorem sum_Icc_eq_sum_range (f : ℕ → ℝ) (a : ℕ) :
    ∑ N ∈ Icc 1 a, f N = ∑ i ∈ range a, f (i + 1) := by
  induction a with
  | zero => simp
  | succ a ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

theorem S_add_Xi (h : Good ε t) (a : ℕ) :
    S ε ((ε : ℝ) / t) a + XiR ε t = ∑' M : ℕ, psi ε t (M + a + 1) := by
  have hs : Summable (fun N => psi ε t (N + 1)) := (summable_nat_add_iff 1).mpr (summable_psi h)
  have h' := hs.sum_add_tsum_nat_add a
  have hS : S ε ((ε : ℝ) / t) a = -∑ i ∈ range a, psi ε t (i + 1) := by
    rw [S]
    simp_rw [psi_conj h]
    rw [sum_neg_distrib, sum_Icc_eq_sum_range]
  rw [hS, XiR, ← h']
  ring

/-- `2(ε/t)^a ψ_{M+a+1}(t) = 2 r_a t^{3(M+1)} / (1 − r_a w^{M+1})³`. -/
theorem two_conj_psi (h : Good ε t) (a M : ℕ) :
    2 * ((ε : ℝ) / t) ^ a * psi ε t (M + a + 1) =
      2 * rr ε t a * (t ^ 3) ^ (M + 1) * (1 / (1 - rr ε t a * wpar ε t ^ (M + 1)) ^ 3) := by
  have ht := (Good.t_pos h).ne'
  have e1 : t ^ (3 * (M + a + 1)) = (t ^ 3) ^ a * (t ^ 3) ^ (M + 1) := by
    rw [← pow_add, ← pow_mul]; ring_nf
  have e2 : wpar ε t ^ (M + a + 1) = rr ε t a * wpar ε t ^ (M + 1) := by
    rw [rr, ← pow_add]; ring_nf
  have e3 : ((ε : ℝ) / t) ^ a * (t ^ 3) ^ a = rr ε t a := by
    rw [← mul_pow, rr]
    congr 1
    rw [wpar]; field_simp
  rw [psi, e1, e2, ← e3]
  ring

/-- `1/(1 − x)³ = ∑_j C(j+2, 2) x^j`. -/
theorem inv_one_sub_cube {x : ℝ} (hx : |x| < 1) :
    1 / (1 - x) ^ 3 = ∑' j : ℕ, ((j + 2).choose 2 : ℝ) * x ^ j :=
  (tsum_choose_mul_geometric_of_norm_lt_one 2 (by rwa [Real.norm_eq_abs])).symm

theorem abs_rr_mul_q_le (h : Good ε t) (a M : ℕ) : |rr ε t a * wpar ε t ^ (M + 1)| ≤ t ^ 2 := by
  rw [abs_mul]
  calc |rr ε t a| * |wpar ε t ^ (M + 1)| ≤ 1 * t ^ 2 := by
        gcongr
        · exact abs_rr_le_one h a
        · exact abs_wpar_pow_le h (by omega)
    _ = t ^ 2 := one_mul _

/-! ### The polynomial moments at `ε/t` -/

theorem abs_nu_conj (h : Good ε t) (j : ℕ) :
    |nu ε ((ε : ℝ) / t) j| ≤ ((j : ℝ) * ((j : ℝ) + 1)) * (1 - t)⁻¹ := by
  have ht0 := (Good.t_pos h)
  have ht1 := (Good.t_lt_one h)
  set α := alpha ε ((ε : ℝ) / t) j with hαdef
  have hα : t * |α| = ((t ^ 2)⁻¹) ^ j := by
    rw [hαdef, alpha, wpar_conj h, abs_mul, abs_mul, abs_div, abs_eps h.1, abs_of_pos ht0,
      abs_pow, abs_inv, abs_wpar h]
    field_simp
  have hα1 : 1 ≤ t * |α| := by
    rw [hα]; exact one_le_pow₀ (one_le_inv₀ (Good.sq_pos h) |>.mpr (Good.sq_lt_one h).le)
  have hd : |α| - 1 ≤ |1 - α| := by
    have := abs_sub_abs_le_abs_sub α 1
    rw [abs_one, abs_sub_comm] at this; linarith
  have hαgt : 1 < |α| := by nlinarith [abs_nonneg α]
  have hdpos : 0 < |1 - α| := by linarith
  have hjj : (0 : ℝ) ≤ (j : ℝ) * ((j : ℝ) + 1) := by positivity
  have hc : (1 - t)⁻¹ * (1 - t) = 1 := inv_mul_cancel₀ (by linarith)
  have hc0 : 0 ≤ (1 - t)⁻¹ := inv_nonneg.mpr (by linarith)
  rw [nu, ← hαdef, mul_div_assoc, abs_mul, abs_div, abs_of_nonneg hjj]
  refine mul_le_mul_of_nonneg_left ?_ hjj
  rw [div_le_iff₀ hdpos]
  nlinarith [mul_nonneg hc0 (sub_nonneg.2 hα1), mul_le_mul_of_nonneg_left hd hc0]

end LucasU.Conj
