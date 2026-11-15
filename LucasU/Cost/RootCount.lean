-- Generalised from lean_fibzeta FibZeta/Cost/RootCount.lean (ε = ±1, general t).
import LucasU.Roots
import LucasU.Cost.Cluster

/-!
# Counting roots of each type (PROOF §3.1)

* `sum_totient_eW_le`: `∑_{d : e(d) = e} φ(d) ≤ 2 φ(e)` (the primitive `d`-th roots with `e(d) = e` are square
  roots of `ε ω`, `ω` a primitive `e`-th root of unity);
* `card_eW_fiber_le`: at most `8` orders `d` have `e(d) = e` (`d ∣ 4e` and `e ∣ 2d`);
* `sum_totient_alpha_le`: `∑_{d : α_j(ζ_d) = 1} φ(d) ≤ 2j + 1` (roots of `X^{2j+1} = ε^{j+1}`);
* `sum_mul_nW_eq`, `nAlpha_le_sum`: the regrouping of `∑_d g(d) n_W(K, d)` by `e = e(d)`, and
  `n_α(K, d) ≤ ∑_j [α_j(ζ_d) = 1] (K − 1 − j)`.
-/

open Finset Polynomial

namespace LucasU.Cost

variable {ε : ℤ}

theorem w_pow_two_mul (hε : ε = 1 ∨ ε = -1) {d : ℕ} (hd : 0 < d) :
    ((ε : ℂ) * zetaC d ^ 2) ^ (2 * d) = 1 := by
  rw [mul_pow, eps_pow_two_mul hε, one_mul, ← pow_mul, show 2 * (2 * d) = d * 4 by ring, pow_mul,
    (zetaC_primitive hd).pow_eq_one, one_pow]

theorem eW_pos (hε : ε = 1 ∨ ε = -1) {d : ℕ} (hd : 0 < d) : 0 < eW ε d :=
  orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨2 * d, by omega, w_pow_two_mul hε hd⟩)

theorem eW_dvd (hε : ε = 1 ∨ ε = -1) {d : ℕ} (hd : 0 < d) : eW ε d ∣ 2 * d :=
  orderOf_dvd_of_pow_eq_one (w_pow_two_mul hε hd)

theorem dvd_four_mul_eW (hε : ε = 1 ∨ ε = -1) {d : ℕ} (hd : 0 < d) : d ∣ 4 * eW ε d := by
  apply (zetaC_primitive hd).dvd_of_pow_eq_one
  have h : ((ε : ℂ) * zetaC d ^ 2) ^ eW ε d = 1 := pow_orderOf_eq_one _
  have h2 : (((ε : ℂ) * zetaC d ^ 2) ^ eW ε d) ^ 2 = zetaC d ^ (4 * eW ε d) := by
    rw [← pow_mul, mul_comm (eW ε d) 2, pow_mul,
      show ((ε : ℂ) * zetaC d ^ 2) ^ 2 = zetaC d ^ 4 by
        rw [mul_pow, eps_sq hε, one_mul, ← pow_mul], ← pow_mul]
  rw [← h2, h, one_pow]

theorem card_eW_fiber_le (hε : ε = 1 ∨ ε = -1) (N e : ℕ) :
    ((Icc 1 N).filter (fun d => eW ε d = e)).card ≤ 8 := by
  calc _ ≤ ((Icc 1 8).image (fun j => 4 * e / j)).card := by
        apply Finset.card_le_card
        intro d hd
        simp only [mem_filter, mem_Icc] at hd
        obtain ⟨⟨hd1, -⟩, hde⟩ := hd
        have hd0 : 0 < d := hd1
        have he0 := eW_pos hε hd0
        rw [hde] at he0
        have h1 := dvd_four_mul_eW hε hd0
        have h2 := Nat.le_of_dvd (by omega) (eW_dvd hε hd0)
        rw [hde] at h1 h2
        obtain ⟨j, hj⟩ := h1
        simp only [mem_image, mem_Icc]
        refine ⟨j, ⟨?_, ?_⟩, ?_⟩
        · rcases Nat.eq_zero_or_pos j with h | h
          · rw [h] at hj; omega
          · exact h
        · by_contra hc
          have : d * 9 ≤ d * j := Nat.mul_le_mul_left d (by omega)
          omega
        · rw [hj]
          rcases Nat.eq_zero_or_pos j with h | h
          · rw [h] at hj; omega
          · exact Nat.mul_div_cancel _ h
    _ ≤ (Icc 1 8).card := card_image_le
    _ = 8 := by simp

theorem disjoint_primitiveRoots (s : Finset ℕ) :
    (s : Set ℕ).PairwiseDisjoint (fun d => primitiveRoots d ℂ) :=
  fun _ _ _ _ hne => IsPrimitiveRoot.disjoint hne

theorem card_biUnion_primitiveRoots (s : Finset ℕ) :
    (s.biUnion (fun d => primitiveRoots d ℂ)).card = ∑ d ∈ s, Nat.totient d := by
  rw [card_biUnion (disjoint_primitiveRoots s)]
  exact Finset.sum_congr rfl fun d _ => Complex.card_primitiveRoots d

theorem sum_totient_eW_le (hε : ε = 1 ∨ ε = -1) (N e : ℕ) (he : 0 < e) :
    ∑ d ∈ (Icc 1 N).filter (fun d => eW ε d = e), Nat.totient d ≤ 2 * Nat.totient e := by
  set D := (Icc 1 N).filter (fun d => eW ε d = e)
  set S := D.biUnion (fun d => primitiveRoots d ℂ)
  rw [← card_biUnion_primitiveRoots D]
  have hS : ∀ z ∈ S, ∃ d, 0 < d ∧ eW ε d = e ∧ IsPrimitiveRoot z d := by
    intro z hz
    obtain ⟨d, hdD, hz⟩ := mem_biUnion.mp hz
    simp only [D, mem_filter, mem_Icc] at hdD
    exact ⟨d, hdD.1.1, hdD.2, (mem_primitiveRoots hdD.1.1).mp hz⟩
  have hsq : ((ε : ℂ)) ^ 2 = 1 := eps_sq hε
  calc S.card ≤ 2 * (S.image (fun z => (ε : ℂ) * z ^ 2)).card := by
        apply Finset.card_le_mul_card_image
        intro b hb
        obtain ⟨z0, -, hz0⟩ := mem_image.mp hb
        calc _ ≤ ({z0, -z0} : Finset ℂ).card := by
              apply Finset.card_le_card
              intro z hz
              simp only [mem_filter] at hz
              have h : (z - z0) * (z + z0) = 0 := by
                linear_combination (ε : ℂ) * (hz.2 - hz0) - (z ^ 2 - z0 ^ 2) * hsq
              rcases mul_eq_zero.mp h with h | h
              · simp [sub_eq_zero.mp h]
              · simp [eq_neg_of_add_eq_zero_left h]
          _ ≤ 2 := card_le_two
    _ ≤ 2 * (primitiveRoots e ℂ).card := by
        apply Nat.mul_le_mul_left
        apply Finset.card_le_card
        intro w hw
        obtain ⟨z, hz, rfl⟩ := mem_image.mp hw
        obtain ⟨d, hd, hde, hzd⟩ := hS z hz
        rw [mem_primitiveRoots he, ← hde, ← orderOf_w_of_primitive hε hd hzd]
        exact IsPrimitiveRoot.orderOf _
    _ = 2 * Nat.totient e := by rw [Complex.card_primitiveRoots]

open Classical in
theorem sum_totient_alpha_le (hε : ε = 1 ∨ ε = -1) (N j : ℕ) :
    ∑ d ∈ (Icc 1 N).filter (fun d => IsAlphaRoot ε d j), Nat.totient d ≤ 2 * j + 1 := by
  classical
  set D := (Icc 1 N).filter (fun d => IsAlphaRoot ε d j)
  rw [← card_biUnion_primitiveRoots D]
  set s : ℂ := (ε : ℂ) ^ (j + 1)
  calc _ ≤ (nthRoots (2 * j + 1) s).toFinset.card := by
        apply Finset.card_le_card
        intro z hz
        obtain ⟨d, hdD, hz⟩ := mem_biUnion.mp hz
        simp only [D, mem_filter, mem_Icc] at hdD
        have hzd := (mem_primitiveRoots hdD.1.1).mp hz
        have ha := (alpha_eq_one_iff_of_primitive hε hdD.1.1 hzd j).mpr hdD.2
        rw [Multiset.mem_toFinset, mem_nthRoots (by omega)]
        have hss : s * s = 1 := by
          simp only [s]; rw [← mul_pow, ← sq, eps_sq hε, one_pow]
        have h2 : ((ε : ℂ) * z) * ((ε : ℂ) * z ^ 2) ^ j = s * z ^ (2 * j + 1) := by
          simp only [s]; ring
        rw [h2] at ha
        linear_combination s * ha - z ^ (2 * j + 1) * hss
    _ ≤ Multiset.card (nthRoots (2 * j + 1) s) := Multiset.toFinset_card_le _
    _ ≤ 2 * j + 1 := card_nthRoots _ _

/-- `n_W(K, d)` as a sum over the possible values of `e(d)`. -/
theorem nW_eq_sum (K d : ℕ) :
    nW ε K d = ∑ e ∈ Icc 1 K, if eW ε d = e then Wc K e else 0 := by
  rw [Finset.sum_ite_eq]
  unfold nW Wc
  simp only [mem_Icc]

theorem sum_mul_nW_eq (K N : ℕ) (g : ℕ → ℕ) :
    ∑ d ∈ Icc 1 N, g d * nW ε K d =
      ∑ e ∈ Icc 1 K, (∑ d ∈ (Icc 1 N).filter (fun d => eW ε d = e), g d) * Wc K e := by
  simp_rw [nW_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

theorem sum_totient_mul_nW_le (hε : ε = 1 ∨ ε = -1) (K N : ℕ) :
    ∑ d ∈ Icc 1 N, Nat.totient d * nW ε K d ≤ ∑ e ∈ Icc 1 K, 2 * Nat.totient e * Wc K e := by
  rw [sum_mul_nW_eq]
  refine Finset.sum_le_sum fun e he => Nat.mul_le_mul_right _ ?_
  exact sum_totient_eW_le hε N e (mem_Icc.mp he).1

theorem sum_nW_le (hε : ε = 1 ∨ ε = -1) (K N : ℕ) :
    ∑ d ∈ Icc 1 N, nW ε K d ≤ ∑ e ∈ Icc 1 K, 8 * Wc K e := by
  have := sum_mul_nW_eq (ε := ε) K N (fun _ => 1)
  simp only [one_mul, Finset.sum_const, smul_eq_mul, mul_one] at this
  rw [this]
  exact Finset.sum_le_sum fun e _ => Nat.mul_le_mul_right _ (card_eW_fiber_le hε N e)

open Classical in
theorem nAlpha_le_sum (K d : ℕ) :
    nAlpha ε K d ≤ ∑ j ∈ Icc 1 (K - 2), if IsAlphaRoot ε d j then K - 1 - j else 0 := by
  unfold nAlpha
  split_ifs with h
  · have hs := Nat.find_spec h
    have hmem : Nat.find h ∈ Icc 1 (K - 2) := mem_Icc.mpr ⟨hs.1, hs.2.1⟩
    have := Finset.single_le_sum (f := fun j => if IsAlphaRoot ε d j then K - 1 - j else 0)
      (fun _ _ => Nat.zero_le _) hmem
    simpa [hs.2.2] using this
  · exact Nat.zero_le _

theorem nAlpha_le (K d : ℕ) : nAlpha ε K d ≤ K := by
  unfold nAlpha; split_ifs <;> omega

open Classical in
theorem sum_totient_mul_nAlpha_le (hε : ε = 1 ∨ ε = -1) (K N : ℕ) :
    ∑ d ∈ Icc 1 N, Nat.totient d * nAlpha ε K d ≤
      ∑ j ∈ Icc 1 (K - 2), (K - 1 - j) * (2 * j + 1) := by
  calc _ ≤ ∑ d ∈ Icc 1 N, Nat.totient d *
        ∑ j ∈ Icc 1 (K - 2), (if IsAlphaRoot ε d j then K - 1 - j else 0) :=
        Finset.sum_le_sum fun d _ => Nat.mul_le_mul_left _ (nAlpha_le_sum K d)
    _ = ∑ j ∈ Icc 1 (K - 2), (K - 1 - j) *
        ∑ d ∈ (Icc 1 N).filter (fun d => IsAlphaRoot ε d j), Nat.totient d := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun d _ => ?_
        split_ifs <;> simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun j _ => Nat.mul_le_mul_left _ (sum_totient_alpha_le hε N j)

end LucasU.Cost
