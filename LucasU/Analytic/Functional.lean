/-
Generalised from lean_fibzeta FibZeta/Analytic/Functional.lean (ε = ±1, general t).
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/Functional.lean and
lean/QZeta3/Purity.lean (Apache-2.0, Lean formalisation by F. Solomon Admasu). Changes: operator
θ² replaced by θ(θ+1) = s²∂² + 2s∂, positive lattice replaced by the nodes (εt²)ⁿ with
weights (εt)ⁿ, moments rewritten for `LucasU.nu` and `LucasU.psi`.
-/
import LucasU.Statements

/-!
# The real functional: calculus of `θ(θ+1)` and the moments (PROOF_U §1, Lemma 1)

Throughout, `[Fact (Good ε t)]`: `ε = ±1` and `0 < t ≤ φ⁻¹`.  This file only uses `0 < t < 1`
and `ε² = 1`.

* `thetaOp_add`, `thetaOp_const_mul`, `thetaOp_sum`, `thetaOp_congr`: pointwise linearity of
  `θ(θ+1)` on functions `C²` at the point;
* `hasL_*`: the summed functional `∑ ρⁿ⁺¹ [θ(θ+1)h](wⁿ⁺¹)` is linear on `HasSum`s;
* `hasL_pow`: `L(s^k) = ν_k` (Lemma 1(i));
* `hasL_simplePole`: `L(1/(1 − w^a s)) = 2 ρ^{−a} (Ξ − S_a)` (Lemma 1(ii)).
-/

open Polynomial Finset Filter Topology

namespace LucasU.Analytic

variable {ε : ℤ} {t : ℝ} [hG : Fact (Good ε t)]

/-! ### Elementary facts about `t` and `ε` -/

theorem t_pos (ε : ℤ) (t : ℝ) [hG : Fact (Good ε t)] : 0 < t := hG.out.2.1

theorem t_lt_one (ε : ℤ) (t : ℝ) [hG : Fact (Good ε t)] : t < 1 :=
  hG.out.2.2.trans_lt (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)

/-- `t² ≤ 1/2`, from `t ≤ φ⁻¹` and `φ² = φ + 1 ≥ 2`. -/
theorem t_sq_le_half (ε : ℤ) (t : ℝ) [hG : Fact (Good ε t)] : t ^ 2 ≤ 1 / 2 := by
  have h0 := t_pos ε t
  have h1 : t * Real.goldenRatio ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hG.out.2.2 Real.goldenRatio_pos.le
    rwa [inv_mul_cancel₀ Real.goldenRatio_ne_zero] at this
  have hsq := Real.goldenRatio_sq
  have hg1 := Real.one_lt_goldenRatio
  nlinarith [mul_pos h0 (by linarith : (0 : ℝ) < Real.goldenRatio)]

theorem eps_sq (ε : ℤ) (t : ℝ) [hG : Fact (Good ε t)] : ((ε : ℝ)) ^ 2 = 1 := by
  rcases hG.out.1 with rfl | rfl <;> norm_num

theorem abs_eps (ε : ℤ) (t : ℝ) [hG : Fact (Good ε t)] : |(ε : ℝ)| = 1 := by
  rcases hG.out.1 with rfl | rfl <;> norm_num

theorem t_sq_pos (ε : ℤ) (t : ℝ) [Fact (Good ε t)] : 0 < t ^ 2 := pow_pos (t_pos ε t) 2

theorem t_sq_lt_one (ε : ℤ) (t : ℝ) [Fact (Good ε t)] : t ^ 2 < 1 :=
  pow_lt_one₀ (t_pos ε t).le (t_lt_one ε t) (by norm_num)

theorem abs_w : |wpar ε t| = t ^ 2 := by
  rw [wpar, abs_mul, abs_eps ε t, one_mul, abs_of_pos (t_sq_pos ε t)]

theorem abs_w_pow (n : ℕ) : |wpar ε t ^ n| = t ^ (2 * n) := by
  rw [abs_pow, abs_w, pow_mul]

theorem abs_rho : |(ε : ℝ) * t| = t := by
  rw [abs_mul, abs_eps ε t, one_mul, abs_of_pos (t_pos ε t)]

theorem rho_ne_zero : (ε : ℝ) * t ≠ 0 := by
  intro h
  have := congrArg abs h
  rw [abs_rho, abs_zero] at this
  exact (t_pos ε t).ne' this

theorem w_ne_zero : wpar ε t ≠ 0 := by
  intro h
  have := congrArg abs h
  rw [abs_w, abs_zero] at this
  exact (t_sq_pos ε t).ne' this

/-- The `n`-th node `wⁿ⁺¹ = (εt²)ⁿ⁺¹`. -/
noncomputable def pt (ε : ℤ) (t : ℝ) (n : ℕ) : ℝ := wpar ε t ^ (n + 1)

theorem abs_pt_le (n : ℕ) : |pt ε t n| ≤ t ^ 2 := by
  rw [pt, abs_w_pow, pow_mul]
  calc (t ^ 2) ^ (n + 1) ≤ (t ^ 2) ^ 1 :=
        pow_le_pow_of_le_one (t_sq_pos ε t).le (t_sq_lt_one ε t).le (by omega)
    _ = t ^ 2 := pow_one _

theorem abs_pt_lt_one (n : ℕ) : |pt ε t n| < 1 := (abs_pt_le n).trans_lt (t_sq_lt_one ε t)

/-! ### The operator `θ(θ+1)` -/

theorem differentiableAt_deriv {f : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (deriv f) x :=
  (hf.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)

theorem thetaOp_congr {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] g) :
    thetaOp f x = thetaOp g x := by
  simp only [thetaOp, h.deriv.deriv_eq, h.deriv_eq]

theorem thetaOp_add {f g : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    thetaOp (fun y => f y + g y) x = thetaOp f x + thetaOp g x := by
  have he : deriv (fun y => f y + g y) =ᶠ[𝓝 x] fun y => deriv f y + deriv g y := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hyf hyg
    exact deriv_fun_add (hyf.differentiableAt (by norm_num)) (hyg.differentiableAt (by norm_num))
  simp only [thetaOp, he.deriv_eq, he.eq_of_nhds]
  rw [deriv_fun_add (differentiableAt_deriv hf) (differentiableAt_deriv hg)]
  ring

theorem thetaOp_const_mul {f : ℝ → ℝ} {x : ℝ} (hf : ContDiffAt ℝ 2 f x) (c : ℝ) :
    thetaOp (fun y => c * f y) x = c * thetaOp f x := by
  have he : deriv (fun y => c * f y) =ᶠ[𝓝 x] fun y => c * deriv f y := by
    filter_upwards [hf.eventually (by simp)] with y hy
    exact deriv_const_mul c (hy.differentiableAt (by norm_num))
  simp only [thetaOp, he.deriv_eq, he.eq_of_nhds]
  rw [deriv_const_mul c (differentiableAt_deriv hf)]
  ring

theorem thetaOp_zero (x : ℝ) : thetaOp (fun _ => (0 : ℝ)) x = 0 := by
  simp [thetaOp]

theorem thetaOp_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) {x : ℝ}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) :
    thetaOp (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, thetaOp (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using thetaOp_zero x
  | @insert i s hi ih =>
    have hfi := hf i (mem_insert_self i s)
    have hfs : ∀ j ∈ s, ContDiffAt ℝ 2 (f j) x := fun j hj => hf j (mem_insert_of_mem hj)
    simp only [sum_insert hi]
    rw [thetaOp_add hfi (ContDiffAt.sum hfs), ih hfs]

/-! ### The summed functional -/

/-- The `n`-th term `ρⁿ⁺¹ [θ(θ+1)h](wⁿ⁺¹)` of `Lfun ε t h`. -/
noncomputable def Lterm (ε : ℤ) (t : ℝ) (h : ℝ → ℝ) (n : ℕ) : ℝ :=
  ((ε : ℝ) * t) ^ (n + 1) * thetaOp h (pt ε t n)

omit hG in
theorem Lfun_eq_tsum (h : ℝ → ℝ) : Lfun ε t h = ∑' n, Lterm ε t h n := rfl

/-- `h` is `C²` on the open unit interval, which contains every node. -/
def Reg (h : ℝ → ℝ) : Prop := ∀ x : ℝ, |x| < 1 → ContDiffAt ℝ 2 h x

omit hG in
theorem hasL_congr {f g : ℝ → ℝ} {v : ℝ} (he : ∀ n, f =ᶠ[𝓝 (pt ε t n)] g)
    (hs : HasSum (Lterm ε t g) v) : HasSum (Lterm ε t f) v := by
  apply hs.congr_fun
  intro n
  simp only [Lterm, thetaOp_congr (he n)]

theorem hasL_const_mul {f : ℝ → ℝ} {v : ℝ} (hf : Reg f) (hs : HasSum (Lterm ε t f) v) (c : ℝ) :
    HasSum (Lterm ε t (fun y => c * f y)) (c * v) := by
  apply (hs.mul_left c).congr_fun
  intro n
  simp only [Lterm, thetaOp_const_mul (hf _ (abs_pt_lt_one n)) c]
  ring

theorem hasL_add {f g : ℝ → ℝ} {v u : ℝ} (hf : Reg f) (hg : Reg g)
    (hs : HasSum (Lterm ε t f) v) (ht : HasSum (Lterm ε t g) u) :
    HasSum (Lterm ε t (fun y => f y + g y)) (v + u) := by
  apply (hs.add ht).congr_fun
  intro n
  simp only [Lterm, thetaOp_add (hf _ (abs_pt_lt_one n)) (hg _ (abs_pt_lt_one n))]
  ring

theorem hasL_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (v : ι → ℝ)
    (hf : ∀ i ∈ s, Reg (f i)) (hs : ∀ i ∈ s, HasSum (Lterm ε t (f i)) (v i)) :
    HasSum (Lterm ε t (fun y => ∑ i ∈ s, f i y)) (∑ i ∈ s, v i) := by
  apply (hasSum_sum hs).congr_fun
  intro n
  simp only [Lterm, thetaOp_sum s f (fun i hi => hf i hi _ (abs_pt_lt_one n)), mul_sum]

theorem reg_add {f g : ℝ → ℝ} (hf : Reg f) (hg : Reg g) : Reg (fun y => f y + g y) :=
  fun x hx => (hf x hx).add (hg x hx)

theorem reg_const_mul {f : ℝ → ℝ} (hf : Reg f) (c : ℝ) : Reg (fun y => c * f y) :=
  fun x hx => contDiffAt_const.mul (hf x hx)

theorem reg_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (hf : ∀ i ∈ s, Reg (f i)) :
    Reg (fun y => ∑ i ∈ s, f i y) :=
  fun x hx => ContDiffAt.sum (fun i hi => hf i hi x hx)

/-! ### Monomials (Lemma 1(i)) -/

theorem thetaOp_pow (k : ℕ) (x : ℝ) :
    thetaOp (fun y => y ^ k) x = (k : ℝ) * (k + 1) * x ^ k := by
  have h1 : deriv (fun y : ℝ => y ^ k) = fun y => (k : ℝ) * y ^ (k - 1) := by
    funext y; exact deriv_pow_field k
  have h2 : deriv (fun y : ℝ => (k : ℝ) * y ^ (k - 1)) x =
      (k : ℝ) * (((k - 1 : ℕ) : ℝ) * x ^ (k - 1 - 1)) := by
    rw [deriv_const_mul _ (differentiableAt_pow _), deriv_pow_field]
  rw [thetaOp, h1, h2]
  rcases k with _ | _ | k
  · simp
  · norm_num
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring

theorem reg_pow (k : ℕ) : Reg (fun y : ℝ => y ^ k) := fun _ _ => contDiffAt_id.pow k

theorem abs_alpha_lt_one (k : ℕ) : |alpha ε t k| < 1 := by
  rw [alpha, abs_mul, abs_rho, abs_w_pow]
  calc t * t ^ (2 * k) ≤ t * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (t_pos ε t).le (t_lt_one ε t).le) (t_pos ε t).le
    _ < 1 := by rw [mul_one]; exact t_lt_one ε t

/-- `L(s^k) = ν_k`. -/
theorem hasL_pow (k : ℕ) : HasSum (Lterm ε t (fun y => y ^ k)) (nu ε t k) := by
  have hα := abs_alpha_lt_one (ε := ε) (t := t) k
  have hg := ((hasSum_geometric_of_abs_lt_one hα).mul_left
    ((k : ℝ) * (k + 1) * alpha ε t k))
  have h1 : 1 - alpha ε t k ≠ 0 := by
    have := (abs_lt.mp hα).2; linarith
  convert hg using 1
  · funext n
    simp only [Lterm, thetaOp_pow, pt, alpha]
    ring
  · rw [nu]; field_simp

/-- The polynomial part: `L(P) = Lpoly P`. -/
theorem hasL_poly (P : ℝ[X]) : HasSum (Lterm ε t (fun y => P.eval y)) (Lpoly ε t P) := by
  have he : (fun y => P.eval y) = fun y => ∑ j ∈ P.support, P.coeff j * y ^ j := by
    funext y; rw [eval_eq_sum, Polynomial.sum_def]
  rw [he, Lpoly]
  exact hasL_sum _ _ _ (fun j _ => reg_const_mul (reg_pow j) _)
    (fun j _ => hasL_const_mul (reg_pow j) (hasL_pow j) _)

theorem reg_poly (P : ℝ[X]) : Reg (fun y => P.eval y) := by
  have he : (fun y => P.eval y) = fun y => ∑ j ∈ P.support, P.coeff j * y ^ j := by
    funext y; rw [eval_eq_sum, Polynomial.sum_def]
  rw [he]
  exact reg_sum _ _ (fun j _ => reg_const_mul (reg_pow j) _)

/-! ### Simple poles (Lemma 1(ii)) -/

theorem thetaOp_inv_affine {c x : ℝ} (hx : 1 - c * x ≠ 0) :
    thetaOp (fun y => (1 - c * y)⁻¹) x = 2 * c * x / (1 - c * x) ^ 3 := by
  have hd : ∀ y, 1 - c * y ≠ 0 →
      HasDerivAt (fun y => (1 - c * y)⁻¹) (c / (1 - c * y) ^ 2) y := by
    intro y hy
    have h := (((hasDerivAt_id' y).const_mul c).const_sub (1 : ℝ)).fun_inv hy
    convert h using 1
    ring
  have hn : ∀ᶠ y in 𝓝 x, 1 - c * y ≠ 0 :=
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually_ne hx
  have he : deriv (fun y => (1 - c * y)⁻¹) =ᶠ[𝓝 x] fun y => c / (1 - c * y) ^ 2 :=
    hn.mono fun y hy => (hd y hy).deriv
  have h2 : HasDerivAt (fun y => c / (1 - c * y) ^ 2) (2 * c ^ 2 / (1 - c * x) ^ 3) x := by
    have h := (hasDerivAt_const x c).fun_div
      ((((hasDerivAt_id' x).const_mul c).const_sub (1 : ℝ)).fun_pow 2)
      (pow_ne_zero 2 hx)
    convert h using 1
    field_simp
    ring
  rw [thetaOp, he.deriv_eq, h2.deriv, (hd x hx).deriv]
  field_simp
  ring

theorem one_sub_w_pow_ne_zero {N : ℕ} (hN : 0 < N) : 1 - wpar ε t ^ N ≠ 0 := by
  have h : |wpar ε t ^ N| < 1 := by
    rw [abs_w_pow, pow_mul]; exact pow_lt_one₀ (t_sq_pos ε t).le (t_sq_lt_one ε t) (by omega)
  have := (abs_lt.mp h).2
  linarith

theorem abs_psi_le {N : ℕ} (hN : 0 < N) : |psi ε t N| ≤ (t ^ 3) ^ N / (1 - t ^ 2) ^ 3 := by
  have hlow : 1 - t ^ 2 ≤ |1 - wpar ε t ^ N| := by
    have h1 : |wpar ε t ^ N| ≤ t ^ 2 := by
      rw [abs_w_pow, pow_mul]
      calc (t ^ 2) ^ N ≤ (t ^ 2) ^ 1 :=
            pow_le_pow_of_le_one (t_sq_pos ε t).le (t_sq_lt_one ε t).le (by omega)
        _ = t ^ 2 := pow_one _
    have := abs_sub_abs_le_abs_sub 1 (wpar ε t ^ N)
    rw [abs_one] at this
    linarith
  have hpos : 0 < 1 - t ^ 2 := by linarith [t_sq_lt_one ε t]
  rw [psi, abs_div, abs_pow, abs_pow, abs_of_pos (t_pos ε t), ← pow_mul]
  exact div_le_div_of_nonneg_left (pow_nonneg (t_pos ε t).le _) (pow_pos hpos 3)
    (pow_le_pow_left₀ hpos.le hlow 3)

theorem summable_psi : Summable (fun N : ℕ => psi ε t (N + 1)) := by
  have hg : Summable (fun N : ℕ => (t ^ 3) ^ (N + 1) / (1 - t ^ 2) ^ 3) := by
    have h3 : t ^ 3 < 1 := pow_lt_one₀ (t_pos ε t).le (t_lt_one ε t) (by norm_num)
    have := (summable_geometric_of_lt_one (pow_nonneg (t_pos ε t).le 3) h3).mul_left (t ^ 3)
    refine (this.div_const ((1 - t ^ 2) ^ 3)).congr fun N => ?_
    ring
  exact Summable.of_norm_bounded hg fun N => by
    rw [Real.norm_eq_abs]; exact abs_psi_le (by omega)

theorem hasSum_psi : HasSum (fun N : ℕ => psi ε t (N + 1)) (XiR ε t) := summable_psi.hasSum

omit hG in
theorem S_eq_sum_range (a : ℕ) : S ε t a = ∑ i ∈ range a, psi ε t (i + 1) := by
  induction a with
  | zero => simp [S]
  | succ a ih => rw [S, sum_Icc_succ_top (by omega), ← S, ih, sum_range_succ]

/-- `Ξ − S_a` is the tail of the series. -/
theorem hasSum_psi_tail (a : ℕ) :
    HasSum (fun n : ℕ => psi ε t (n + 1 + a)) (XiR ε t - S ε t a) := by
  have hs : Summable (fun n : ℕ => psi ε t (n + 1 + a)) := by
    have := (summable_nat_add_iff a).mpr (summable_psi (ε := ε) (t := t))
    refine this.congr fun n => ?_
    congr 1; omega
  have h := (summable_psi (ε := ε) (t := t)).sum_add_tsum_nat_add a
  have hS := S_eq_sum_range (ε := ε) (t := t) a
  convert hs.hasSum using 1
  rw [hS, XiR, ← h]
  have : (fun i : ℕ => psi ε t (i + a + 1)) = fun n => psi ε t (n + 1 + a) := by
    funext n; congr 1; omega
  rw [this]
  ring

theorem reg_simplePole (c : ℝ) (hc : |c| ≤ 1) : Reg (fun y => (1 - c * y)⁻¹) := by
  intro x hx
  have : |c * x| < 1 := by
    rw [abs_mul]
    calc |c| * |x| ≤ 1 * |x| := mul_le_mul_of_nonneg_right hc (abs_nonneg x)
      _ < 1 := by rw [one_mul]; exact hx
  have hne : 1 - c * x ≠ 0 := by have := (abs_lt.mp this).2; linarith
  exact (contDiffAt_const.sub (contDiffAt_const.mul contDiffAt_id)).inv hne

theorem abs_w_pow_le_one (a : ℕ) : |wpar ε t ^ a| ≤ 1 := by
  rw [abs_w_pow]; exact pow_le_one₀ (t_pos ε t).le (t_lt_one ε t).le

/-- `L(1/(1 − w^a s)) = 2 ρ^{−a} (Ξ − S_a)` (Lemma 1(ii)). -/
theorem hasL_simplePole (a : ℕ) :
    HasSum (Lterm ε t (fun y => (1 - wpar ε t ^ a * y)⁻¹))
      (2 * (((ε : ℝ) * t) ^ a)⁻¹ * (XiR ε t - S ε t a)) := by
  have ht0 : (ε : ℝ) * t ≠ 0 := rho_ne_zero
  convert (hasSum_psi_tail (ε := ε) (t := t) a).mul_left (2 * (((ε : ℝ) * t) ^ a)⁻¹) using 1
  funext n
  have hne : 1 - wpar ε t ^ a * pt ε t n ≠ 0 := by
    rw [pt, ← pow_add]; exact one_sub_w_pow_ne_zero (by omega)
  simp only [Lterm]
  rw [thetaOp_inv_affine hne]
  simp only [psi, pt]
  have hne' : 1 - wpar ε t ^ (n + 1 + a) ≠ 0 := one_sub_w_pow_ne_zero (by omega)
  have hpow : wpar ε t ^ a * wpar ε t ^ (n + 1) = wpar ε t ^ (n + 1 + a) := by ring
  have h3 : ((ε : ℝ) * t) * wpar ε t = t ^ 3 := by
    rw [wpar]; linear_combination t ^ 3 * eps_sq ε t
  have hkey : t ^ (3 * (n + 1 + a)) =
      ((ε : ℝ) * t) ^ (n + 1) * wpar ε t ^ (n + 1 + a) * ((ε : ℝ) * t) ^ a := by
    calc t ^ (3 * (n + 1 + a)) = (((ε : ℝ) * t) * wpar ε t) ^ (n + 1 + a) := by
          rw [h3, ← pow_mul]
      _ = _ := by rw [mul_pow, pow_add ((ε : ℝ) * t) (n + 1) a]; ring
  rw [mul_assoc (2 : ℝ), hpow, hkey]
  have ha : ((ε : ℝ) * t) ^ a ≠ 0 := pow_ne_zero _ ht0
  field_simp

end LucasU.Analytic
