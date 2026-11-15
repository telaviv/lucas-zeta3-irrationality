-- Generalised from lean_fibzeta FibZeta/Cost/Cluster.lean (ε = ±1, general t).
import LucasU.Defs

/-!
# Cluster costs (PROOF Prop. 3.6, W part, per `e`)

* `cW_bound`: `4 c(m) + 16 ≤ 16 m + (m − 5)₊²` for `m ≥ 1` (i.e. `c(m) ≤ 4(m − 1) + (m − 5)₊²/4`);
* `cW'_le`: `c′(m) ≤ c(m) + 4`;
* cluster sizes: `1 ≤ m_r ≤ K/e + 1`, `∑_{r=1}^e m_r = K`;
* `Wc_bound`: the W cost `Wc K e = ∑_{r<e} c(m_r) + c′(m_e)` satisfies
  `4 Wc + 16 e ≤ 16 K + e (K/e − 4)₊² + 16` for `1 ≤ e ≤ K`.
-/

open Finset

namespace LucasU.Cost

theorem cW_add_two {m : ℕ} (hm : 1 ≤ m) : cW (m + 2) = cW m + (m + 4) + (4 - m) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  unfold cW
  rw [show n + 1 + 2 - 1 = n + 1 + 1 by omega, Finset.sum_range_succ', Finset.sum_range_succ,
    show n + 1 - 1 = n by omega]
  have h : ∀ j ∈ range n, n + 1 + 2 + 2 - 2 * (j + 1) = n + 1 + 2 - 2 * j := fun j _ => by omega
  rw [Finset.sum_congr rfl h]
  omega

theorem cW_bound (m : ℕ) (hm : 1 ≤ m) : 4 * cW m + 16 ≤ 16 * m + (m - 5) ^ 2 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases h6 : m ≤ 6
    · interval_cases m <;> decide
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      have hk := ih k (by omega) (by omega)
      rw [cW_add_two (by omega), show 4 - k = 0 by omega,
        show k + 2 - 5 = (k - 5) + 2 by omega]
      have e1 : ((k - 5) + 2) ^ 2 = (k - 5) ^ 2 + 4 * (k - 5) + 4 := by ring
      rw [e1]
      omega

theorem cW'_le (m : ℕ) : cW' m ≤ cW m + 4 := by
  rcases m with _ | n
  · simp [cW', cW]
  · unfold cW' cW
    rw [Finset.sum_range_succ, show n + 1 - 1 = n by omega]
    omega

theorem one_le_clusterSize {K e r : ℕ} (hr : 1 ≤ r) (hre : r ≤ e) (heK : e ≤ K) :
    1 ≤ clusterSize K e r := by
  unfold clusterSize
  exact Finset.card_pos.mpr ⟨r, mem_filter.mpr ⟨mem_Icc.mpr ⟨hr, by omega⟩, rfl⟩⟩

theorem clusterSize_le {K e : ℕ} (r : ℕ) : clusterSize K e r ≤ K / e + 1 := by
  unfold clusterSize
  calc _ ≤ (range (K / e + 1)).card := by
        apply Finset.card_le_card_of_injOn (fun a => a / e)
        · intro a ha
          simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at ha
          simp only [coe_range, Set.mem_Iio]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right ha.1.2)
        · intro a ha b hb hab
          simp only [coe_filter, mem_Icc, Set.mem_ofPred_eq] at ha hb
          simp only at hab
          rw [← Nat.div_add_mod a e, ← Nat.div_add_mod b e, hab, ha.2, hb.2]
    _ = K / e + 1 := card_range _

theorem sum_clusterSize {K e : ℕ} (he : 0 < e) : ∑ r ∈ Icc 1 e, clusterSize K e r = K := by
  have H : ∀ a ∈ Icc 1 K, (fun a => if a % e = 0 then e else a % e) a ∈ Icc 1 e := by
    intro a _
    have := Nat.mod_lt a he
    simp only [mem_Icc]
    split_ifs <;> omega
  have hc := Finset.card_eq_sum_card_fiberwise
    (f := fun a => if a % e = 0 then e else a % e) (s := Icc 1 K) (t := Icc 1 e) H
  rw [Nat.card_Icc, Nat.add_sub_cancel] at hc
  conv_rhs => rw [hc]
  refine Finset.sum_congr rfl fun r hr => ?_
  unfold clusterSize
  congr 1
  ext a
  simp only [mem_filter]
  refine and_congr_right fun _ => ?_
  have hr' := mem_Icc.mp hr
  have ha := Nat.mod_lt a he
  rcases Nat.lt_or_ge r e with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt]
    split_ifs <;> omega
  · have hre : r = e := by omega
    subst hre
    rw [Nat.mod_self]
    split_ifs <;> omega

/-- The W cost of the root type `e`: `∑_{r=1}^{e−1} c(m_r) + c′(m_e)`. -/
def Wc (K e : ℕ) : ℕ :=
  (∑ r ∈ Icc 1 (e - 1), cW (clusterSize K e r)) + cW' (clusterSize K e e)

theorem Wc_bound {K e : ℕ} (he : 1 ≤ e) (heK : e ≤ K) :
    4 * Wc K e + 16 * e ≤ 16 * K + e * (K / e - 4) ^ 2 + 16 := by
  have hsplit : ∑ r ∈ Icc 1 e, cW (clusterSize K e r) =
      (∑ r ∈ Icc 1 (e - 1), cW (clusterSize K e r)) + cW (clusterSize K e e) := by
    conv_lhs => rw [show e = e - 1 + 1 by omega]
    rw [Finset.sum_Icc_succ_top (by omega), show e - 1 + 1 = e by omega]
  have hW : Wc K e ≤ (∑ r ∈ Icc 1 e, cW (clusterSize K e r)) + 4 := by
    unfold Wc; rw [hsplit]; have := cW'_le (clusterSize K e e); omega
  have hper : ∀ r ∈ Icc 1 e, 4 * cW (clusterSize K e r) + 16 ≤
      16 * clusterSize K e r + (K / e - 4) ^ 2 := by
    intro r hr
    have hr' := mem_Icc.mp hr
    have h1 := one_le_clusterSize hr'.1 hr'.2 heK
    have h2 := clusterSize_le (K := K) (e := e) r
    have h3 := cW_bound _ h1
    have h4 : (clusterSize K e r - 5) ^ 2 ≤ (K / e - 4) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    omega
  have hsum := Finset.sum_le_sum hper
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_clusterSize (by omega : 0 < e), Finset.sum_const, Finset.sum_const, Nat.card_Icc,
    Nat.add_sub_cancel, smul_eq_mul, smul_eq_mul] at hsum
  nlinarith [hsum, hW]

end LucasU.Cost
