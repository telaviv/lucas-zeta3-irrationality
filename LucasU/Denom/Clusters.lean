/-
Generalised from lean_fibzeta FibZeta/Denom/Clusters.lean (ε = ±1, general t).
-/
import LucasU.Defs

/-!
# Cluster combinatorics and the weights of Proposition 3.2

For `1 ≤ e ≤ K` the nodes `1, …, K` split into the residue classes `I_r = {a ≡ r mod e}`,
`r < e`.  The class `r` is `{s_r + l e : l < m_r}` with smallest element `s_r = r` (`r ≠ 0`, a
regular node, `s_r < e`) or `s_r = e` (`r = 0`, the paper's cluster `r = e`; every node singular),
and `m_r = (K − s_r)/e + 1` (`mem_clSet_iff`, `card_clSet`).

The integer weights `wRow = ⌈w_j⌉`, `wCol = ⌊w_j⌋` with `w_j = max(0, (m+2)/2 − j)` (and
`w_{m−1} = 0` for `r ≠ 0`) satisfy the inequalities of Prop 3.2 (`weights_singular`,
`weights_regular`) and their total is `c(m)` resp. `c′(m)` (`sum_weights`).
-/

open Finset

namespace LucasU.Denom

/-- Smallest node of the class `r` (`r < e`). -/
def clSmall (e r : ℕ) : ℕ := if r = 0 then e else r

/-- Size `m_r` of the class `r`. -/
def clMult (K e r : ℕ) : ℕ := (K - clSmall e r) / e + 1

/-- The `l`-th node `s_r + l e` of the class `r`. -/
def clNode (e r l : ℕ) : ℕ := clSmall e r + l * e

/-- The class `I_r`. -/
def clSet (K e r : ℕ) : Finset ℕ := (Icc 1 K).filter (fun a => a % e = r)

variable {K e r : ℕ}

theorem clSmall_pos (he : 1 ≤ e) : 1 ≤ clSmall e r := by
  unfold clSmall; split_ifs <;> omega

theorem clSmall_le (hr : r < e) : clSmall e r ≤ e := by
  unfold clSmall; split_ifs <;> omega

theorem clSmall_mod (hr : r < e) : clSmall e r % e = r := by
  unfold clSmall
  split_ifs with h
  · subst h; exact Nat.mod_self e
  · exact Nat.mod_eq_of_lt hr

theorem clNode_mod (hr : r < e) (l : ℕ) : clNode e r l % e = r := by
  unfold clNode
  rw [Nat.add_mul_mod_self_right, clSmall_mod hr]

theorem clNode_injective (he : 1 ≤ e) : Function.Injective (clNode e r) := by
  intro l l' h
  unfold clNode at h
  have : l * e = l' * e := by omega
  exact Nat.eq_of_mul_eq_mul_right (by omega) this

theorem clNode_le (he : 1 ≤ e) (heK : e ≤ K) (hr : r < e) {l : ℕ} (hl : l < clMult K e r) :
    clNode e r l ≤ K := by
  unfold clNode
  have hs := clSmall_le hr
  have hl' : l ≤ (K - clSmall e r) / e := by unfold clMult at hl; omega
  have := (Nat.le_div_iff_mul_le (by omega : 0 < e)).mp hl'
  omega

theorem clNode_mem (he : 1 ≤ e) (heK : e ≤ K) (hr : r < e) {l : ℕ} (hl : l < clMult K e r) :
    clNode e r l ∈ clSet K e r := by
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, clNode_le he heK hr hl⟩, clNode_mod hr l⟩
  have := clSmall_pos (r := r) he
  unfold clNode
  omega

theorem mem_clSet_iff (he : 1 ≤ e) (heK : e ≤ K) (hr : r < e) (a : ℕ) :
    a ∈ clSet K e r ↔ ∃ l < clMult K e r, clNode e r l = a := by
  constructor
  · intro ha
    obtain ⟨ha1, haK, hmod⟩ : 1 ≤ a ∧ a ≤ K ∧ a % e = r := by
      simpa only [clSet, mem_filter, mem_Icc, and_assoc] using ha
    set s := clSmall e r with hs
    have hsa : s ≤ a := by
      rw [hs]; unfold clSmall
      split_ifs with h0
      · subst h0
        exact Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hmod)
      · rw [← hmod]; exact Nat.mod_le a e
    have hsmod : s % e = a % e := by rw [hs, clSmall_mod hr, hmod]
    have hdvd : e ∣ a - s := by
      apply Nat.dvd_of_mod_eq_zero
      exact Nat.sub_mod_eq_zero_of_mod_eq hsmod.symm
    obtain ⟨l, hl⟩ := hdvd
    refine ⟨l, ?_, ?_⟩
    · unfold clMult
      have : l ≤ (K - s) / e := by
        apply (Nat.le_div_iff_mul_le (by omega : 0 < e)).mpr
        rw [mul_comm]; omega
      rw [← hs]; omega
    · unfold clNode; rw [← hs, mul_comm]; omega
  · rintro ⟨l, hl, rfl⟩
    exact clNode_mem he heK hr hl

theorem clSet_eq_image (he : 1 ≤ e) (heK : e ≤ K) (hr : r < e) :
    clSet K e r = (range (clMult K e r)).image (clNode e r) := by
  ext a
  rw [mem_clSet_iff he heK hr, mem_image]
  simp only [mem_range]

theorem card_clSet (he : 1 ≤ e) (heK : e ≤ K) (hr : r < e) :
    (clSet K e r).card = clMult K e r := by
  rw [clSet_eq_image he heK hr, card_image_of_injective _ (clNode_injective he), card_range]

theorem clusterSize_eq (he : 1 ≤ e) (heK : e ≤ K) (hr : r < e) :
    clusterSize K e r = clMult K e r := by
  rw [← card_clSet he heK hr]
  unfold clusterSize clSet
  congr 1
  apply filter_congr
  intro a _
  rw [Nat.mod_eq_of_lt hr]

theorem clusterSize_self (he : 1 ≤ e) (heK : e ≤ K) :
    clusterSize K e e = clMult K e 0 := by
  rw [← card_clSet he heK (by omega : 0 < e)]
  unfold clusterSize clSet
  congr 1
  apply filter_congr
  intro a _
  rw [Nat.mod_self]

theorem sum_clMult (he : 1 ≤ e) (heK : e ≤ K) : ∑ r ∈ range e, clMult K e r = K := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Icc 1 K) (t := range e) (f := fun a : ℕ => a % e)
    (fun a _ => mem_range.mpr (Nat.mod_lt a (by omega)))
  calc ∑ r ∈ range e, clMult K e r = ∑ r ∈ range e, ((Icc 1 K).filter (fun a => a % e = r)).card :=
        sum_congr rfl fun r hr => (card_clSet he heK (mem_range.mp hr)).symm
    _ = (Icc 1 K).card := h.symm
    _ = K := by simp

theorem clMult_pos : 0 < clMult K e r := Nat.succ_pos _

theorem clMult_le (he : 1 ≤ e) (heK : e ≤ K) (hr : r < e) : clMult K e r ≤ K := by
  rw [← card_clSet he heK hr]
  calc (clSet K e r).card ≤ (Icc 1 K).card := card_filter_le _ _
    _ = K := by simp

/-- The node `l = 0` of a class `r ≠ 0` is regular (`< e`); every other node is `≥ e`. -/
theorem clNode_lt_iff (hr : r < e) (l : ℕ) :
    clNode e r l < e ↔ r ≠ 0 ∧ l = 0 := by
  unfold clNode clSmall
  split_ifs with h0
  · constructor
    · intro h; omega
    · rintro ⟨h, -⟩; exact absurd h0 h
  · constructor
    · intro h
      refine ⟨h0, ?_⟩
      rcases Nat.eq_zero_or_pos l with hl | hl
      · exact hl
      · have : e ≤ l * e := Nat.le_mul_of_pos_left e hl
        omega
    · rintro ⟨-, rfl⟩; simpa using hr

/-! ### Weights -/

/-- Row weight `⌈w_j⌉`. -/
def wRow (K e r j : ℕ) : ℕ :=
  if r ≠ 0 ∧ j + 1 = clMult K e r then 0 else (clMult K e r + 3) / 2 - j

/-- Column weight `⌊w_j⌋`. -/
def wCol (K e r j : ℕ) : ℕ :=
  if r ≠ 0 ∧ j + 1 = clMult K e r then 0 else (clMult K e r + 2) / 2 - j

/-- First case of Prop 3.2(iv): a singular node `x_{a_i}` with `i > max(j,k)` survives. -/
theorem weights_singular (j k l : ℕ) (hl : l < clMult K e r)
    (hcase : ¬ (r ≠ 0 ∧ l = 0)) (hj : ¬ (1 ≤ l ∧ l ≤ j)) (hk : ¬ (1 ≤ l ∧ l ≤ k)) :
    clMult K e r + 2 ≤ wRow K e r j + wCol K e r k + j + k := by
  unfold wRow wCol
  by_cases hr : r = 0
  · simp only [hr, ne_eq, not_true_eq_false, false_and, ite_false]
    omega
  · have hl0 : 1 ≤ l := by omega
    have hjl : j < l := by omega
    have hkl : k < l := by omega
    have h1 : ¬ (r ≠ 0 ∧ j + 1 = clMult K e r) := by omega
    have h2 : ¬ (r ≠ 0 ∧ k + 1 = clMult K e r) := by omega
    rw [if_neg h1, if_neg h2]
    omega

/-- Second case: only the regular node `x_r` (`r ≠ 0`, `l = 0`) survives. -/
theorem weights_regular (j k : ℕ) (hj : j < clMult K e r) (hk : k < clMult K e r) :
    clMult K e r - 1 ≤ wRow K e r j + wCol K e r k + j + k := by
  unfold wRow wCol
  split_ifs <;> omega

theorem sum_weights :
    ∑ j ∈ range (clMult K e r), (wRow K e r j + wCol K e r j) =
      if r = 0 then cW' (clMult K e r) else cW (clMult K e r) := by
  have hm0 : 0 < clMult K e r := clMult_pos
  unfold wRow wCol
  generalize clMult K e r = m at hm0 ⊢
  have hcost (j : ℕ) : (m + 3) / 2 - j + ((m + 2) / 2 - j) = m + 2 - 2 * j := by omega
  split_ifs with hr
  · unfold cW'
    apply sum_congr rfl
    intro j _
    simp only [hr, ne_eq, not_true_eq_false, false_and, ite_false]
    exact hcost j
  · unfold cW
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [sum_range_succ, Nat.add_sub_cancel]
    have hlast : (if r ≠ 0 ∧ n + 1 = n + 1 then 0 else (n + 1 + 3) / 2 - n) +
        (if r ≠ 0 ∧ n + 1 = n + 1 then 0 else (n + 1 + 2) / 2 - n) = 0 := by simp [hr]
    rw [hlast, add_zero]
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.mp hj
    have hne : ¬ (r ≠ 0 ∧ j + 1 = n + 1) := by omega
    rw [if_neg hne, if_neg hne, hcost]

end LucasU.Denom
