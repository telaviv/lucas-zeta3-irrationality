/-
Generalised from lean_fibzeta FibZeta/Denom/Newton.lean (ε = ±1, general t).
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/MovingClusterBasis.lean and
lean/QZeta3/LocalClusterTransport.lean (Apache-2.0, Lean formalisation by F. Solomon Admasu). Changes:
the basis is the Newton cluster basis of PROOF Prop 3.2 (vanishing at the nodes `l = 1, …, j` of the
class), indexed by `Σ r : Fin e, Fin m_r`; nodes are `x_a = w^{-a}` with reductions `θ^a`, `θ = w(ω)⁻¹`.
-/
import LucasU.Denom.Nodes
import LucasU.Denom.Clusters
import LucasU.Denom.ClusterBasis

/-!
# The Newton cluster basis (Proposition 3.2)

`newtonP K e r j x = (F/F_r) · ∏_{l=1}^{j} (s − x_{s_r + l e})`.  At `ω` its reduction is
`(F/F_r)(ω) (s − θ^r)^j` (`newtonP_reduction`), so by the Chinese remainder theorem
(`ClusterBasis`) the change of basis from the monomials has unit determinant at `ω`
(`newton_det_isUnit`).
-/

open Polynomial Finset

namespace LucasU.Denom

section Generic

variable {k : Type*} [CommRing k]

/-- `F/F_r = ∏_{a ∉ I_r} (s − x_a)`. -/
noncomputable def clComp (K e r : ℕ) (x : ℕ → k) : k[X] :=
  ∏ a ∈ (Icc 1 K).filter (fun a => a % e ≠ r), (X - C (x a))

/-- The Newton cluster polynomial `N_{r,j}`. -/
noncomputable def newtonP (K e r j : ℕ) (x : ℕ → k) : k[X] :=
  clComp K e r x * ∏ l ∈ Icc 1 j, (X - C (x (clNode e r l)))

theorem map_newtonP {k' : Type*} [CommRing k'] (f : k →+* k') (K e r j : ℕ) (x : ℕ → k) :
    (newtonP K e r j x).map f = newtonP K e r j (fun a => f (x a)) := by
  simp [newtonP, clComp, Polynomial.map_prod]

theorem newtonP_monic (K e r j : ℕ) (x : ℕ → k) : (newtonP K e r j x).Monic :=
  (Polynomial.monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _).mul
    (Polynomial.monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _)

theorem card_filter_not_class {K e r : ℕ} (he : 1 ≤ e) (heK : e ≤ K) (hr : r < e) :
    ((Icc 1 K).filter (fun a => a % e ≠ r)).card = K - clMult K e r := by
  have h1 : ((Icc 1 K).filter (fun a => a % e = r)).card = clMult K e r :=
    card_clSet he heK hr
  have hc : ((Icc 1 K).filter (fun a => a % e = r)).card +
      ((Icc 1 K).filter (fun a => ¬ a % e = r)).card = K := by
    rw [Finset.card_filter_add_card_filter_not]; simp
  have h2 : ((Icc 1 K).filter (fun a => a % e ≠ r)).card =
      ((Icc 1 K).filter (fun a => ¬ a % e = r)).card := rfl
  omega

theorem natDegree_newtonP [Nontrivial k] {K e r : ℕ} (he : 1 ≤ e) (heK : e ≤ K) (hr : r < e)
    (j : ℕ) (x : ℕ → k) :
    (newtonP K e r j x).natDegree = (K - clMult K e r) + j := by
  unfold newtonP clComp
  rw [Polynomial.Monic.natDegree_mul (Polynomial.monic_prod_of_monic _ _ fun _ _ =>
      monic_X_sub_C _) (Polynomial.monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _),
    Polynomial.natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _,
    Polynomial.natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one, Nat.card_Icc,
    Nat.add_sub_cancel]
  rw [card_filter_not_class he heK hr]

theorem newtonP_coeff_mem (S : Subring k) (K e r j : ℕ) (x : ℕ → k) (hx : ∀ a, x a ∈ S)
    (i : ℕ) : (newtonP K e r j x).coeff i ∈ S := by
  let x' : ℕ → S := fun a => ⟨x a, hx a⟩
  have hmap : (newtonP K e r j x').map S.subtype = newtonP K e r j x := by
    rw [map_newtonP]; rfl
  rw [← hmap, Polynomial.coeff_map]
  exact ((newtonP K e r j x').coeff i).property

end Generic

section Reduction

variable {k : Type*} [Field k]

theorem clComp_reduction {K e : ℕ} (he : 1 ≤ e) (heK : e ≤ K) (θ : k) (hθ : θ ^ e = 1)
    (r : Fin e) :
    clComp K e r.val (fun a => θ ^ a) =
      clusterComplement (fun s : Fin e => θ ^ s.val) (fun s : Fin e => clMult K e s.val) r := by
  classical
  let g : ℕ → Fin e := fun a => ⟨a % e, Nat.mod_lt a (by omega)⟩
  let s := (Icc 1 K).filter (fun a => a % e ≠ r.val)
  have hfiber (t : Fin e) : s.filter (fun a => g a = t) =
      if t = r then ∅ else clSet K e t.val := by
    by_cases h : t = r
    · subst t
      ext a
      simp [s, g, Fin.ext_iff]
    · rw [if_neg h]
      ext a
      simp only [s, clSet, mem_filter, g, Fin.ext_iff]
      constructor
      · intro ha
        exact ⟨ha.1.1, ha.2⟩
      · intro ha
        exact ⟨⟨ha.1, fun he' => h (Fin.ext (ha.2.symm.trans he'))⟩, ha.2⟩
  have hprod (t : Fin e) : (∏ a ∈ s.filter (fun a => g a = t), (X - C (θ ^ a))) =
      if t = r then 1 else (X - C (θ ^ t.val)) ^ (clMult K e t.val) := by
    rw [hfiber]
    split_ifs with h
    · simp
    · calc (∏ a ∈ clSet K e t.val, (X - C (θ ^ a))) =
          ∏ a ∈ clSet K e t.val, (X - C (θ ^ t.val)) := by
            apply Finset.prod_congr rfl
            intro a ha
            rw [pow_eq_pow_mod a hθ, (Finset.mem_filter.mp ha).2]
        _ = _ := by rw [prod_const, card_clSet he heK t.isLt]
  change (∏ a ∈ s, (X - C (θ ^ a))) = _
  rw [← Finset.prod_fiberwise s g (fun a => (X - C (θ ^ a)))]
  simp_rw [hprod]
  unfold clusterComplement clusterFactor
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul]
  congr 1
  ext t
  simp [ne_comm]

theorem newtonP_reduction {K e : ℕ} (he : 1 ≤ e) (heK : e ≤ K) (θ : k) (hθ : θ ^ e = 1)
    (r : Fin e) (j : ℕ) :
    newtonP K e r.val j (fun a => θ ^ a) =
      clusterComplement (fun s : Fin e => θ ^ s.val) (fun s : Fin e => clMult K e s.val) r *
        (X - C (θ ^ r.val)) ^ j := by
  unfold newtonP
  rw [clComp_reduction he heK θ hθ r]
  congr 1
  calc (∏ l ∈ Icc 1 j, (X - C (θ ^ clNode e r.val l))) = ∏ l ∈ Icc 1 j, (X - C (θ ^ r.val)) := by
        apply Finset.prod_congr rfl
        intro l _
        rw [pow_eq_pow_mod _ hθ, clNode_mod r.isLt]
    _ = _ := by rw [prod_const, Nat.card_Icc, Nat.add_sub_cancel]

end Reduction

/-! ### The cluster index and the basis over the rational functions -/

/-- Cluster indices `(r, j)`, `r < e`, `j < m_r`. -/
abbrev CIdx (K e : ℕ) := Σ r : Fin e, Fin (clMult K e r.val)

theorem card_CIdx {K e : ℕ} (he : 1 ≤ e) (heK : e ≤ K) : Fintype.card (CIdx K e) = K := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun r => clMult K e r) e]
  exact sum_clMult he heK

noncomputable def cEquiv {K e : ℕ} (he : 1 ≤ e) (heK : e ≤ K) : CIdx K e ≃ Fin K :=
  (Fintype.equivFin (CIdx K e)).trans (finCongr (card_CIdx he heK))

variable {𝕜 : Type*} [Field 𝕜] {ε : ℤ}

local notation "Xr" => (RatFunc.X : RatFunc 𝕜)

/-- The Newton basis, indexed by `Fin K`. -/
noncomputable def newtonBasis (ε : ℤ) {K e : ℕ} (he : 1 ≤ e) (heK : e ≤ K) (i : Fin K) :
    (RatFunc 𝕜)[X] :=
  newtonP K e ((cEquiv he heK).symm i).1.val ((cEquiv he heK).symm i).2.val (node ε Xr)

theorem newtonBasis_natDegree {K e : ℕ} (he : 1 ≤ e) (heK : e ≤ K) (i : Fin K) :
    (newtonBasis (𝕜 := 𝕜) ε he heK i).natDegree < K := by
  unfold newtonBasis
  rw [natDegree_newtonP he heK ((cEquiv he heK).symm i).1.isLt]
  have hj := ((cEquiv he heK).symm i).2.isLt
  have hm := clMult_le he heK ((cEquiv he heK).symm i).1.isLt
  omega

theorem newtonBasis_coeff_mem (hε : ε = 1 ∨ ε = -1) {K e : ℕ} (he : 1 ≤ e) (heK : e ≤ K) (ω : 𝕜) (hω : ω ≠ 0)
    (i : Fin K) (l : ℕ) : (newtonBasis ε he heK i).coeff l ∈ regularAt ω :=
  newtonP_coeff_mem _ _ _ _ _ _ (fun a => node_mem_regularAt hε ω hω a) l

/-! ### Local reduction and the unit determinant -/

theorem localEval_node (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω : ω ≠ 0) (a : ℕ) :
    localEval ω ⟨node ε Xr a, node_mem_regularAt hε ω hω a⟩ = ((wpar ε ω)⁻¹) ^ a := by
  let y : regularAt ω := ⟨wpar ε Xr, wpar_mem _ (base_mem_regularAt ω)⟩
  have hy : localEval ω y = wpar ε ω := by
    have : y = (ε : regularAt ω) * (⟨Xr, base_mem_regularAt ω⟩ : regularAt ω) ^ 2 :=
      Subtype.ext (by simp [y, wpar])
    rw [this, map_mul, map_intCast, map_pow, localEval_base, wpar]
  have hmul : (⟨node ε Xr a, node_mem_regularAt hε ω hω a⟩ : regularAt ω) * y ^ a = 1 := by
    apply Subtype.ext
    push_cast [y, node]
    have : (wpar ε Xr) ^ a ≠ 0 := pow_ne_zero _ (wpar_ne_zero hε RatFunc.X_ne_zero)
    exact inv_mul_cancel₀ this
  have h := congrArg (localEval ω) hmul
  rw [map_mul, map_pow, hy, map_one] at h
  rw [inv_pow]
  exact eq_inv_of_mul_eq_one_left h

/-- The Newton basis lifted to the local ring. -/
noncomputable def newtonLoc (hε : ε = 1 ∨ ε = -1) {K e : ℕ} (he : 1 ≤ e) (heK : e ≤ K) (ω : 𝕜) (hω : ω ≠ 0)
    (i : Fin K) : (regularAt ω)[X] :=
  newtonP K e ((cEquiv he heK).symm i).1.val ((cEquiv he heK).symm i).2.val
    (fun a => ⟨node ε Xr a, node_mem_regularAt hε ω hω a⟩)

theorem newtonLoc_map (hε : ε = 1 ∨ ε = -1) {K e : ℕ} (he : 1 ≤ e) (heK : e ≤ K) (ω : 𝕜) (hω : ω ≠ 0) (i : Fin K) :
    (newtonLoc hε he heK ω hω i).map (regularAt ω).subtype = newtonBasis ε he heK i := by
  unfold newtonLoc newtonBasis
  rw [map_newtonP]
  rfl

theorem polynomialChange_newton (hε : ε = 1 ∨ ε = -1) {K e : ℕ} (he : 1 ≤ e) (heK : e ≤ K) (ω : 𝕜) (hω : ω ≠ 0) :
    polynomialChange K (newtonBasis ε he heK) =
      (Matrix.of fun i j : Fin K => (newtonLoc hε he heK ω hω i).coeff j.val).map
        (regularAt ω).subtype := by
  ext i j
  simp only [polynomialChange, Matrix.of_apply, Matrix.map_apply, ← newtonLoc_map hε he heK ω hω,
    Polynomial.coeff_map]

theorem newton_det_isUnit (hε : ε = 1 ∨ ε = -1) {K e : ℕ} (he : 1 ≤ e) (heK : e ≤ K) (ω : 𝕜) (hω : ω ≠ 0)
    (horder : orderOf (wpar ε ω) = e) :
    IsUnit (Matrix.of fun i j : Fin K => (newtonLoc hε he heK ω hω i).coeff j.val).det := by
  apply isUnit_of_localEval_ne_zero
  set θ : 𝕜 := (wpar ε ω)⁻¹ with hθdef
  have hprim : IsPrimitiveRoot θ e := by
    rw [hθdef, ← horder]
    exact (IsPrimitiveRoot.orderOf (wpar ε ω)).inv
  have hθ : θ ^ e = 1 := hprim.pow_eq_one
  let P : Fin K → 𝕜[X] := fun i =>
    clusterBasis (fun s : Fin e => θ ^ s.val) (fun s : Fin e => clMult K e s.val)
      ((cEquiv he heK).symm i)
  have hmap : (Matrix.of fun i j : Fin K => (newtonLoc hε he heK ω hω i).coeff j.val).map
      (localEval ω) = Matrix.of fun i j : Fin K => (P i).coeff j.val := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [← Polynomial.coeff_map]
    congr 1
    unfold newtonLoc
    rw [map_newtonP]
    simp only [localEval_node hε ω hω]
    rw [newtonP_reduction he heK θ hθ]
    rfl
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hmap]
  apply coeffMatrix_det_ne_zero
  · intro i
    have h := clusterBasis_natDegree_lt (fun s : Fin e => θ ^ s.val)
      (fun s : Fin e => clMult K e s.val) ((cEquiv he heK).symm i)
    have hs : ∑ s : Fin e, clMult K e s.val = K := by
      rw [Fin.sum_univ_eq_sum_range (fun r => clMult K e r) e]
      exact sum_clMult he heK
    rw [hs] at h
    exact h
  · exact (clusterBasis_linearIndependent (fun s : Fin e => θ ^ s.val) (fun r s h => Fin.ext (hprim.pow_inj r.isLt s.isLt h))
      _ (fun r => clMult_pos)).comp _ (Equiv.injective _)

theorem newton_det_ne_zero (hε : ε = 1 ∨ ε = -1) {K e : ℕ} (he : 1 ≤ e) (heK : e ≤ K) (ω : 𝕜) (hω : ω ≠ 0)
    (horder : orderOf (wpar ε ω) = e) :
    (polynomialChange K (newtonBasis (𝕜 := 𝕜) ε he heK)).det ≠ 0 := by
  rw [polynomialChange_newton hε he heK ω hω]
  have h := RingHom.map_det (regularAt ω).subtype
    (Matrix.of fun i j : Fin K => (newtonLoc hε he heK ω hω i).coeff j.val)
  rw [RingHom.mapMatrix_apply] at h
  rw [← h]
  exact (IsUnit.map (regularAt ω).subtype (newton_det_isUnit hε he heK ω hω horder)).ne_zero

theorem newton_det_inv_mem (hε : ε = 1 ∨ ε = -1) {K e : ℕ} (he : 1 ≤ e) (heK : e ≤ K) (ω : 𝕜) (hω : ω ≠ 0)
    (horder : orderOf (wpar ε ω) = e) :
    (polynomialChange K (newtonBasis (𝕜 := 𝕜) ε he heK)).det⁻¹ ∈ regularAt ω := by
  rw [polynomialChange_newton hε he heK ω hω]
  have h := RingHom.map_det (regularAt ω).subtype
    (Matrix.of fun i j : Fin K => (newtonLoc hε he heK ω hω i).coeff j.val)
  rw [RingHom.mapMatrix_apply] at h
  rw [← h]
  obtain ⟨u, hu⟩ := newton_det_isUnit hε he heK ω hω horder
  rw [← hu]
  have h1 : ((u : regularAt ω) : RatFunc 𝕜) * ((u⁻¹ : (regularAt ω)ˣ) : RatFunc 𝕜) = 1 := by
    rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
  have : ((u : regularAt ω) : RatFunc 𝕜)⁻¹ = ((u⁻¹ : (regularAt ω)ˣ) : RatFunc 𝕜) :=
    inv_eq_of_mul_eq_one_right h1
  change ((u : regularAt ω) : RatFunc 𝕜)⁻¹ ∈ regularAt ω
  rw [this]
  exact ((u⁻¹ : (regularAt ω)ˣ) : regularAt ω).property

end LucasU.Denom
