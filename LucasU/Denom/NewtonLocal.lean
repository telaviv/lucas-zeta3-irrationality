/-
Generalised from lean_fibzeta FibZeta/Denom/NewtonLocal.lean (ε = ±1, general t).
-/
import LucasU.Denom.Newton

/-!
# Proposition 3.2: the local bound at W-roots

At `ω ≠ 0` with `e = ord w(ω) ≤ K`, in the Newton cluster basis with the weights `wRow`, `wCol`
every scaled pole part is regular (Lemma 3.2a):

* (i) entries between different classes vanish, since `F | N_{r,j} N_{r',k}`;
* (ii) at a node `a = s_r + l e` with `1 ≤ l ≤ max(j,k)` the residue vanishes; otherwise the
  numerator has a zero of order `j + k`, `F'(x_a)` has `m_r − 1` simple zeros, and `S_a` has a pole
  of order `≤ 3` (`0` at the regular node `l = 0`, `r ≠ 0`);
* the weights compensate (`weights_singular`, `weights_regular`).

Combined with the rank argument this gives `local_bound_cluster`:
`π^{∑_r cost_r + (K − 1 − k₀)} · coeff ∈ regularAt ω`.
-/

open Polynomial Finset

namespace LucasU.Denom

variable {𝕜 : Type*} [Field 𝕜] {ε : ℤ}

local notation "Xr" => (RatFunc.X : RatFunc 𝕜)

section Vanishing

variable {k : Type*} [CommRing k]

theorem newtonP_eval_eq_zero_of_mod_ne (K e r j : ℕ) (x : ℕ → k) (a : ℕ) (ha : a ∈ Icc 1 K)
    (har : a % e ≠ r) : (newtonP K e r j x).eval (x a) = 0 := by
  unfold newtonP clComp
  rw [eval_mul, eval_prod]
  rw [Finset.prod_eq_zero (mem_filter.mpr ⟨ha, har⟩) (by simp), zero_mul]

theorem newtonP_eval_eq_zero_of_top (K e r j : ℕ) (x : ℕ → k) (l : ℕ) (hl : 1 ≤ l ∧ l ≤ j) :
    (newtonP K e r j x).eval (x (clNode e r l)) = 0 := by
  unfold newtonP
  rw [eval_mul, eval_prod]
  rw [Finset.prod_eq_zero (mem_Icc.mpr hl) (by simp), mul_zero]

end Vanishing

theorem w_pow_eq_iff (ω : 𝕜) {e : ℕ} (he : 1 ≤ e) (horder : orderOf (wpar ε ω) = e) {a b : ℕ} :
    (wpar ε ω) ^ a = (wpar ε ω) ^ b ↔ a % e = b % e := by
  have hfin : IsOfFinOrder (wpar ε ω) := orderOf_pos_iff.mp (by omega)
  rw [hfin.pow_inj_mod, horder]

theorem w_pow_eq_of_mod_eq (ω : 𝕜) {e : ℕ} (he : 1 ≤ e) (horder : orderOf (wpar ε ω) = e)
    {a b : ℕ} (h : a % e = b % e) : (wpar ε ω) ^ a = (wpar ε ω) ^ b :=
  (w_pow_eq_iff ω he horder).mpr h

theorem mod_eq_of_w_pow_eq (ω : 𝕜) {e : ℕ} (he : 1 ≤ e) (horder : orderOf (wpar ε ω) = e)
    {a b : ℕ} (h : (wpar ε ω) ^ a = (wpar ε ω) ^ b) : a % e = b % e :=
  (w_pow_eq_iff ω he horder).mp h

theorem clComp_coeff_mem {k : Type*} [CommRing k] (S : Subring k) (K e r : ℕ) (x : ℕ → k)
    (hx : ∀ a, x a ∈ S) (i : ℕ) : (clComp K e r x).coeff i ∈ S := by
  let x' : ℕ → S := fun a => ⟨x a, hx a⟩
  have hmap : (clComp K e r x').map S.subtype = clComp K e r x := by
    simp [clComp, Polynomial.map_prod, x']
  rw [← hmap, Polynomial.coeff_map]
  exact ((clComp K e r x').coeff i).property

/-- The Newton polynomial has a zero of order `j` at every node of its own class. -/
theorem newtonP_eval_div_mem (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω : ω ≠ 0) {K e r : ℕ} (he : 1 ≤ e) (hr : r < e)
    (horder : orderOf (wpar ε ω) = e) (j a : ℕ) (har : a % e = r) :
    (newtonP K e r j (node ε Xr)).eval (node ε Xr a) / uniformizer ω ^ j ∈ regularAt ω := by
  unfold newtonP
  rw [eval_mul, eval_prod, mul_div_assoc]
  apply (regularAt ω).mul_mem
  · exact eval_mem_regularAt ω _ (clComp_coeff_mem _ K e r _
      (fun b => node_mem_regularAt hε ω hω b)) _ (node_mem_regularAt hε ω hω a)
  · have h : (∏ l ∈ Icc 1 j, (node ε Xr a - node ε Xr (clNode e r l)) / uniformizer ω) ∈
        regularAt ω := by
      apply (regularAt ω).prod_mem
      intro l _
      exact node_diff_div_uniformizer_mem hε ω hω a _
        (w_pow_eq_of_mod_eq ω he horder (by rw [har, clNode_mod hr]))
    rw [Finset.prod_div_distrib, prod_const, Nat.card_Icc, Nat.add_sub_cancel] at h
    simpa only [eval_sub, eval_X, eval_C] using h

variable [CharZero 𝕜]

omit [CharZero 𝕜] in
theorem collisionCount_cluster (ω : 𝕜) {K e r : ℕ} (he : 1 ≤ e) (heK : e ≤ K) (hr : r < e)
    (horder : orderOf (wpar ε ω) = e) (a : ℕ) (ha : a ∈ clSet K e r) :
    collisionCount ε ω K a = clMult K e r - 1 := by
  classical
  have har : a % e = r := (mem_filter.mp ha).2
  have hset : ((Icc 1 K).erase a).filter (fun b => (wpar ε ω) ^ a = (wpar ε ω) ^ b) =
      (clSet K e r).erase a := by
    ext b
    simp only [mem_filter, mem_erase, clSet]
    constructor
    · rintro ⟨⟨hba, hb⟩, hw⟩
      exact ⟨hba, hb, (mod_eq_of_w_pow_eq ω he horder hw).symm.trans har⟩
    · rintro ⟨hba, hb, hbr⟩
      exact ⟨⟨hba, hb⟩, w_pow_eq_of_mod_eq ω he horder (har.trans hbr.symm)⟩
  unfold collisionCount
  rw [hset, card_erase_of_mem ha, card_clSet he heK hr]

/-- One residue term of the scaled pole part in the Newton basis. -/
theorem newton_term_mem (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω : ω ≠ 0) {K e : ℕ} (he : 1 ≤ e) (heK : e ≤ K)
    (horder : orderOf (wpar ε ω) = e) (r r' : Fin e) (j : Fin (clMult K e r.val))
    (k : Fin (clMult K e r'.val)) (a : ℕ) (ha : a ∈ Icc 1 K) (i : ℕ) :
    (C (uniformizer ω ^ (wRow K e r.val j.val + wCol K e r'.val k.val) *
      ((newtonP K e r.val j.val (node ε Xr) * newtonP K e r'.val k.val (node ε Xr)).eval
        (node ε Xr a) * (2 * Xr ^ a) / (derivative (F ε Xr K)).eval (node ε Xr a))) *
      (X - C (S ε Xr a))).coeff i ∈ regularAt ω := by
  set N := (newtonP K e r.val j.val (node ε Xr) * newtonP K e r'.val k.val (node ε Xr)).eval
    (node ε Xr a) with hNdef
  have hzero : N = 0 → (C (uniformizer ω ^ (wRow K e r.val j.val + wCol K e r'.val k.val) *
      (N * (2 * Xr ^ a) / (derivative (F ε Xr K)).eval (node ε Xr a))) *
      (X - C (S ε Xr a))).coeff i ∈ regularAt ω := by
    intro h0
    rw [h0, zero_mul, zero_div, mul_zero, map_zero, zero_mul, coeff_zero]
    exact (regularAt ω).zero_mem
  by_cases har : a % e = r.val
  swap
  · apply hzero
    rw [hNdef, eval_mul, newtonP_eval_eq_zero_of_mod_ne _ _ _ _ _ a ha har, zero_mul]
  by_cases har' : a % e = r'.val
  swap
  · apply hzero
    rw [hNdef, eval_mul, newtonP_eval_eq_zero_of_mod_ne _ _ _ _ _ a ha har', mul_zero]
  have hrr : r' = r := Fin.ext (har'.symm.trans har)
  subst hrr
  have haset : a ∈ clSet K e r'.val := mem_filter.mpr ⟨ha, har⟩
  obtain ⟨l, hl, rfl⟩ := (mem_clSet_iff he heK r'.isLt a).mp haset
  by_cases hlj : 1 ≤ l ∧ l ≤ j.val
  · apply hzero
    rw [hNdef, eval_mul, newtonP_eval_eq_zero_of_top _ _ _ _ _ l hlj, zero_mul]
  by_cases hlk : 1 ≤ l ∧ l ≤ k.val
  · apply hzero
    rw [hNdef, eval_mul, newtonP_eval_eq_zero_of_top _ _ _ _ _ l hlk, mul_zero]
  have hN : N / uniformizer ω ^ (j.val + k.val) ∈ regularAt ω := by
    rw [hNdef, eval_mul, pow_add, ← div_mul_div_comm]
    exact (regularAt ω).mul_mem (newtonP_eval_div_mem hε ω hω he r'.isLt horder _ _ har)
      (newtonP_eval_div_mem hε ω hω he r'.isLt horder _ _ har)
  have hcoll := collisionCount_cluster ω he heK r'.isLt horder _ haset
  by_cases hreg : r'.val ≠ 0 ∧ l = 0
  · -- the regular node `x_r`: `S_a` is regular
    have hlt : clNode e r'.val l < e := (clNode_lt_iff r'.isLt l).mpr hreg
    have hS : uniformizer ω ^ 0 * S ε Xr (clNode e r'.val l) ∈ regularAt ω := by
      rw [pow_zero, one_mul]
      apply S_mem_regularAt
      intro M hM
      apply pow_ne_one_of_lt_orderOf (by have := (mem_Icc.mp hM).1; omega)
      rw [horder]; have := (mem_Icc.mp hM).2; omega
    have hw := weights_regular (K := K) (e := e) (r := r'.val) j.val k.val j.isLt k.isLt
    exact proper_term_coeff_mem hε ω hω K _ ha N _ 0 _ hN hS (by omega) i
  · have hS := uniformizer_cube_mul_S_mem hε ω hω (clNode e r'.val l)
    have hw := weights_singular (K := K) (e := e) (r := r'.val) j.val k.val l hl hreg hlj hlk
    exact proper_term_coeff_mem hε ω hω K _ ha N _ 3 _ hN hS (by omega) i

/-- **Proposition 3.2** (with the rank correction of the ε-term). -/
theorem local_bound_cluster (hε : ε = 1 ∨ ε = -1) (ω : 𝕜) (hω0 : ω ≠ 0) {K e : ℕ} (he : 1 ≤ e) (heK : e ≤ K)
    (horder : orderOf (wpar ε ω) = e) (k₀ : ℕ)
    (hnu : ∀ l, 1 ≤ l → l < k₀ → nu ε Xr l ∈ regularAt ω) (i : ℕ) :
    uniformizer ω ^ ((∑ r ∈ range e, if r = 0 then cW' (clMult K e r) else cW (clMult K e r)) +
      (K - 1 - k₀)) * (Delta ε Xr K).coeff i ∈ regularAt ω := by
  let ι := (cEquiv he heK).symm
  let rw' : Fin K → ℕ := fun i => wRow K e (ι i).1.val (ι i).2.val
  let cw' : Fin K → ℕ := fun i => wCol K e (ι i).1.val (ι i).2.val
  have h := local_bound_of_basis hε ω hω0 K (newtonBasis ε he heK)
    (newtonBasis_natDegree he heK) (newtonBasis_coeff_mem hε he heK ω hω0)
    (newton_det_ne_zero hε he heK ω hω0 horder) (newton_det_inv_mem hε he heK ω hω0 horder)
    rw' cw'
    (fun i i' => by
      apply (coeff_mem_iff_lifts (regularAt ω) _).mp
      intro n
      unfold properPart
      rw [Finset.mul_sum, finsetSum_coeff]
      apply (regularAt ω).sum_mem
      intro a ha
      rw [← mul_assoc, ← map_mul]
      exact newton_term_mem hε ω hω0 he heK horder (ι i).1 (ι i').1 (ι i).2 (ι i').2 a ha n)
    k₀ hnu i
  have hsum : (∑ i, rw' i) + (∑ i, cw' i) =
      ∑ r ∈ range e, if r = 0 then cW' (clMult K e r) else cW (clMult K e r) := by
    rw [← Finset.sum_add_distrib]
    have he' := (cEquiv he heK).symm.sum_comp (fun x : CIdx K e =>
      wRow K e x.1.val x.2.val + wCol K e x.1.val x.2.val)
    simp only [rw', cw', ι]
    rw [he', Fintype.sum_sigma]
    rw [Fin.sum_univ_eq_sum_range (fun r => ∑ j : Fin (clMult K e r),
      (wRow K e r j.val + wCol K e r j.val)) e]
    apply sum_congr rfl
    intro r _
    rw [Fin.sum_univ_eq_sum_range (fun j => wRow K e r j + wCol K e r j) (clMult K e r)]
    exact sum_weights
  rw [hsum] at h
  exact h

end LucasU.Denom
