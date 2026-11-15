import LucasU.NonVan.Pole

-- Generalised from lean_fibzeta FibZeta/NonVan/Interp.lean (ε = ±1, general t).
-- Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/CauchyInterpolation.lean and
-- lean/QZeta3/Nonvanishing.lean (Apache-2.0, Lean formalisation by F. Solomon Admasu). Changes: the
-- functional is the formal one of `Defs.lean` (`L_X` at `X = Ξ`, polynomial quotient plus residues)
-- instead of a real functional with derivatives; interpolation is a polynomial identity.

/-!
# Orthogonal polynomials interpolate the Cauchy transform (PROOF §5)

We work directly with the formal Hankel matrix of `Defs.lean` at `τ = t`, `X = Ξ`:

* `Ln ε t n` : the linear functional `P ↦ L_Ξ(P/F_n) = Lpoly(P /ₘ F_n) + ∑_a P(x_a)/F_n'(x_a) · 2t^a(S_a − Ξ)`;
  `Ln ε t n (s^k) = mConst + Ξ · mLin` (`Ln_X_pow`);
* `Delta_eval` : `Δ_n(Ξ) = nrm^n · det[Ln ε t n (s^{i+j})]`;
* `cauchyPart_interpolates` : if `Ln ε t n (s^j Q) = 0` for `j < n`, then `𝓕 Q − T` vanishes at
  every node `x_a = w^{−a}`, `1 ≤ a ≤ n`, where `T` is the polynomial part of `𝓕 Q` at infinity;
* `tendsto_cauchyPart_error` : `𝓕 Q − T → 0` at `+∞`.

The real functional `Lfun` is not needed: the only analytic input is `𝓕(x_a) = 2t^a(Ξ − S_a)`
`cauchyF_node`, which is the formal pole moment `−L_Ξ(1/(s − x_a))`.
-/

open Polynomial Finset Filter Topology

namespace LucasU.NonVan

variable {ε : ℤ} {t : ℝ}

/-! ### The functional on polynomials -/

/-- `Lpoly` at `τ = t` as a linear map. -/
noncomputable def LpolyLin (ε : ℤ) (t : ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun j => (nu ε t j) • LinearMap.id)

theorem LpolyLin_apply (f : ℝ[X]) : LpolyLin ε t f = Lpoly ε t f := by
  simp only [LpolyLin, Polynomial.lsum_apply, LinearMap.smul_apply, LinearMap.id_apply,
    smul_eq_mul, Polynomial.sum_def, Lpoly]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem Lpoly_X_pow (j : ℕ) : Lpoly ε t (X ^ j : ℝ[X]) = nu ε t j := by
  simp [Lpoly, Polynomial.support_X_pow]

theorem F_monic (n : ℕ) : (F ε t n).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

theorem F_natDegree (n : ℕ) : (F ε t n).natDegree = n := by
  unfold F
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp

/-- The linear functional `L_Ξ(P/F_n)`. -/
noncomputable def Ln (ε : ℤ) (t : ℝ) (n : ℕ) : ℝ[X] →ₗ[ℝ] ℝ :=
  LpolyLin ε t ∘ₗ divByMonicHom (F ε t n) +
    ∑ a ∈ Icc 1 n, (2 * t ^ a * (S ε t a - (XiR ε t)) / (derivative (F ε t n)).eval (node ε t a)) •
      leval (node ε t a)

theorem Ln_apply (n : ℕ) (P : ℝ[X]) :
    Ln ε t n P = Lpoly ε t (P /ₘ F ε t n) + ∑ a ∈ Icc 1 n,
      2 * t ^ a * (S ε t a - (XiR ε t)) / (derivative (F ε t n)).eval (node ε t a) *
        P.eval (node ε t a) := by
  simp only [Ln, LinearMap.add_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, leval_apply, smul_eq_mul,
    LpolyLin_apply]
  rfl

theorem Ln_X_pow (n k : ℕ) : Ln ε t n (X ^ k) = mConst ε t n k + (XiR ε t) * mLin ε t n k := by
  rw [Ln_apply, mConst, mLin, add_assoc]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [res, eval_pow, eval_X]
  ring

theorem nrm_ne_zero (hG : Good ε t) (n : ℕ) : nrm ε t n ≠ 0 := by
  unfold nrm
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (inv_ne_zero ((w_pow_ne_zero hG) _))

/-- `Δ_n(Ξ) = nrm^n · det[L_Ξ(s^{i+j}/F_n)]`. -/
theorem Delta_eval (n : ℕ) :
    (Delta ε t n).eval (XiR ε t) =
      nrm ε t n ^ n * (Matrix.of fun i j : Fin n => Ln ε t n (X ^ (i.val + j.val))).det := by
  unfold Delta
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  have hM : (evalRingHom (XiR ε t)).mapMatrix
      ((X : ℝ[X]) • (hankelLin ε t n).map C + (hankelConst ε t n).map C) =
      nrm ε t n • Matrix.of fun i j : Fin n => Ln ε t n (X ^ (i.val + j.val)) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, coe_evalRingHom, eval_add, eval_mul, eval_X, eval_C, hankelLin, hankelConst,
      Matrix.of_apply, Ln_X_pow]
    ring
  rw [hM, Matrix.det_smul, Fintype.card_fin]

/-! ### Divided differences and the polynomial part at infinity -/

/-- Divided difference of a monomial, as a polynomial in the support variable. -/
noncomputable def monomialDivDiff (k : ℕ) (z : ℝ) : ℝ[X] :=
  ∑ j ∈ range k, C (z ^ (k - 1 - j)) * X ^ j

/-- Divided difference `(Q(z) − Q(s))/(z − s)`, as a polynomial in `s`. -/
noncomputable def realDivDiff (Q : ℝ[X]) (z : ℝ) : ℝ[X] :=
  ∑ k ∈ Q.support, Q.coeff k • monomialDivDiff k z

/-- The polynomial part of `𝓕 Q` at infinity: `∑_k Q_k ∑_{j<k} ν_j z^{k−1−j}`. -/
noncomputable def cauchyPart (ε : ℤ) (t : ℝ) (Q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Q.support, Q.coeff k • ∑ j ∈ range k, C (nu ε t j) * X ^ (k - 1 - j)

theorem eval_monomialDivDiff (k : ℕ) (z x : ℝ) :
    (monomialDivDiff k z).eval x = ∑ j ∈ range k, z ^ (k - 1 - j) * x ^ j := by
  simp only [monomialDivDiff, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem monomialDivDiff_identity (k : ℕ) (z x : ℝ) :
    (z - x) * (monomialDivDiff k z).eval x = z ^ k - x ^ k := by
  rw [eval_monomialDivDiff]
  have h := geom_sum₂_mul x z k
  simp_rw [mul_comm (x ^ _) (z ^ _)] at h
  nlinarith

theorem realDivDiff_identity (Q : ℝ[X]) (z x : ℝ) :
    (z - x) * (realDivDiff Q z).eval x = Q.eval z - Q.eval x := by
  simp only [realDivDiff, Polynomial.eval_finsetSum, Polynomial.eval_smul,
    smul_eq_mul, Finset.mul_sum]
  have hterm : ∀ k, (z - x) * (Q.coeff k * (monomialDivDiff k z).eval x) =
      Q.coeff k * (z ^ k - x ^ k) := by
    intro k
    rw [← mul_assoc, mul_comm (z - x) (Q.coeff k), mul_assoc, monomialDivDiff_identity]
  simp_rw [hterm, mul_sub]
  rw [Finset.sum_sub_distrib]
  simp only [Polynomial.eval_eq_sum, Polynomial.sum_def]

/-- As polynomials: `(s − z) · B = Q − Q(z)`. -/
theorem realDivDiff_mul (Q : ℝ[X]) (z : ℝ) :
    (X - C z) * realDivDiff Q z = Q - C (Q.eval z) := by
  apply Polynomial.funext
  intro x
  have h := realDivDiff_identity Q z x
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  linarith

theorem cauchyPart_eval (Q : ℝ[X]) (z : ℝ) :
    (cauchyPart ε t Q).eval z = Lpoly ε t (realDivDiff Q z) := by
  rw [← LpolyLin_apply]
  simp only [cauchyPart, realDivDiff, monomialDivDiff, Polynomial.eval_finsetSum,
    Polynomial.eval_smul, smul_eq_mul, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← Polynomial.smul_eq_C_mul, map_smul, LpolyLin_apply, Lpoly_X_pow, smul_eq_mul, mul_comm]

/-- `𝓕 Q − T → 0` at `+∞`. -/
theorem tendsto_cauchyPart_error (hG : Good ε t) (Q : ℝ[X]) :
    Tendsto (fun z => cauchyF ε t z * Q.eval z - (cauchyPart ε t Q).eval z) atTop (𝓝 0) := by
  have heq : ∀ z : ℝ,
      cauchyF ε t z * Q.eval z - (cauchyPart ε t Q).eval z =
      ∑ k ∈ Q.support, Q.coeff k * (cauchyF ε t z * z ^ k - momentPolynomial ε t k z) := by
    intro z
    simp only [cauchyPart, momentPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_smul,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    congr 1
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have h := tendsto_finsetSum Q.support (fun k _ =>
    ((tendsto_cauchyF_monomial_sub hG) k).const_mul (Q.coeff k))
  simpa only [heq, mul_zero, Finset.sum_const_zero] using h

/-! ### Interpolation at the nodes -/

/-- Orthogonality to monomials extends to every polynomial of lower degree. -/
theorem orthogonal_to_polynomial (L : ℝ[X] →ₗ[ℝ] ℝ) (Q H : ℝ[X]) {n : ℕ}
    (horth : ∀ j : Fin n, L (X ^ j.val * Q) = 0) (hH : H.natDegree < n) :
    L (H * Q) = 0 := by
  conv_lhs => rw [← Polynomial.sum_monomial_eq H]
  simp only [Polynomial.sum_def, Finset.sum_mul, map_sum]
  apply Finset.sum_eq_zero
  intro j hj
  have hjn : j < n := (Polynomial.le_natDegree_of_mem_supp j hj).trans_lt hH
  rw [← Polynomial.C_mul_X_pow_eq_monomial, ← Polynomial.smul_eq_C_mul,
    smul_mul_assoc, map_smul, horth ⟨j, hjn⟩, smul_zero]

theorem node_injective (hG : Good ε t) : Function.Injective (node ε t) := by
  intro a b h
  unfold node at h
  exact (w_pow_injective hG) (inv_inj.mp h)

/-- The cofactor ε t `H_a = ∏_{b ≠ a} (s − x_b)`. -/
noncomputable def cofactor (ε : ℤ) (t : ℝ) (n a : ℕ) : ℝ[X] := ∏ b ∈ (Icc 1 n).erase a, (X - C (node ε t b))

theorem F_eq_mul_cofactor {n a : ℕ} (ha : a ∈ Icc 1 n) :
    F ε t n = (X - C (node ε t a)) * cofactor ε t n a := by
  unfold F cofactor
  exact (Finset.mul_prod_erase _ (fun b => X - C (node ε t b)) ha).symm

theorem cofactor_monic (n a : ℕ) : (cofactor ε t n a).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

theorem cofactor_natDegree {n a : ℕ} (ha : a ∈ Icc 1 n) : (cofactor ε t n a).natDegree = n - 1 := by
  unfold cofactor
  rw [natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp [Finset.card_erase_of_mem ha]

theorem cofactor_eval_ne {n a : ℕ} {b : ℕ} (hb : b ∈ Icc 1 n) (hba : b ≠ a) :
    (cofactor ε t n a).eval (node ε t b) = 0 := by
  unfold cofactor
  rw [eval_prod]
  exact Finset.prod_eq_zero (mem_erase.mpr ⟨hba, hb⟩) (by simp)

theorem cofactor_eval_self (hG : Good ε t) (n a : ℕ) : (cofactor ε t n a).eval (node ε t a) ≠ 0 := by
  unfold cofactor
  rw [eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro b hb
  simp only [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.mpr (fun h => (mem_erase.mp hb).1 ((node_injective hG) h).symm)

theorem derivative_F_eval {n a : ℕ} (ha : a ∈ Icc 1 n) :
    (derivative (F ε t n)).eval (node ε t a) = (cofactor ε t n a).eval (node ε t a) := by
  rw [F_eq_mul_cofactor ha, derivative_mul]
  simp

/-- The functional on `H_a Q`: polynomial part of the divided difference plus one residue. -/
theorem Ln_cofactor_mul (hG : Good ε t) {n a : ℕ} (ha : a ∈ Icc 1 n) (Q : ℝ[X]) :
    Ln ε t n (cofactor ε t n a * Q) = Lpoly ε t (realDivDiff Q (node ε t a)) +
      2 * t ^ a * (S ε t a - (XiR ε t)) * Q.eval (node ε t a) := by
  have hn := Finset.mem_Icc.mp ha
  have hHQ : cofactor ε t n a * Q = C (Q.eval (node ε t a)) * cofactor ε t n a +
      F ε t n * realDivDiff Q (node ε t a) := by
    have h1 := realDivDiff_mul Q (node ε t a)
    rw [F_eq_mul_cofactor ha]
    calc cofactor ε t n a * Q = cofactor ε t n a * ((X - C (node ε t a)) * realDivDiff Q (node ε t a) +
          C (Q.eval (node ε t a))) := by rw [h1]; ring
      _ = _ := by ring
  have hdiv : (cofactor ε t n a * Q) /ₘ F ε t n = realDivDiff Q (node ε t a) := by
    refine (div_modByMonic_unique _ (C (Q.eval (node ε t a)) * cofactor ε t n a) (F_monic n)
      ⟨hHQ.symm, ?_⟩).1
    calc degree (C (Q.eval (node ε t a)) * cofactor ε t n a) ≤ degree (cofactor ε t n a) := by
          rw [← smul_eq_C_mul]; exact degree_smul_le _ _
      _ = (n - 1 : ℕ) := by rw [degree_eq_natDegree (cofactor_monic n a).ne_zero,
          cofactor_natDegree ha]
      _ < n := by exact_mod_cast (by omega : n - 1 < n)
      _ = degree (F ε t n) := by rw [degree_eq_natDegree (F_monic n).ne_zero, F_natDegree]
  rw [Ln_apply, hdiv]
  congr 1
  rw [Finset.sum_eq_single a]
  · rw [eval_mul, derivative_F_eval ha]
    have := (cofactor_eval_self hG) n a
    field_simp
  · intro b hb hba
    rw [eval_mul, cofactor_eval_ne hb hba]
    ring
  · intro h; exact absurd ha h

/-- Orthogonality forces exact interpolation at each node of `F_n`. -/
theorem cauchyPart_interpolates (hG : Good ε t) {n : ℕ} (Q : ℝ[X])
    (horth : ∀ j : Fin n, Ln ε t n (X ^ j.val * Q) = 0) {a : ℕ} (ha : a ∈ Icc 1 n) :
    cauchyF ε t (node ε t a) * Q.eval (node ε t a) - (cauchyPart ε t Q).eval (node ε t a) = 0 := by
  have hdeg : (cofactor ε t n a).natDegree < n := by
    rw [cofactor_natDegree ha]; have := Finset.mem_Icc.mp ha; omega
  have hzero := orthogonal_to_polynomial (Ln ε t n) Q (cofactor ε t n a) horth hdeg
  rw [(Ln_cofactor_mul hG) ha] at hzero
  rw [(cauchyF_node hG), cauchyPart_eval]
  linear_combination (-1 : ℝ) * hzero

end LucasU.NonVan
