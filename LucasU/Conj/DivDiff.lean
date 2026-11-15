-- Generalised from lean_fibzeta FibZeta/Conj/DivDiff.lean (ε = ±1, general t).
import Mathlib

/-!
# Divided differences of powers at real nodes (PROOF §4)

For a node function `r : ℕ → ℝ`, injective on `{1, 2, …}`, and `F_K = ∏_{a=1}^K (X − r_a)`
(`Lagrange.nodal (Icc 1 K) r`), set

  `E r K m = ∑_{a=1}^K r_a^m / F_K'(r_a) = ∑_a r_a^m · nodalWeight_a`.

(This is the complete homogeneous symmetric polynomial `h_{m−K+1}(r_1, …, r_K)`, but we never need
that name.)  We prove

* `E_base`: `E r K m = [m = K − 1]` for `m < K` (Lagrange interpolation, leading coefficient);
* `E_succ`: `E r (K+1) (m+1) = r_{K+1} E r (K+1) m + E r K m`;
* `E_bound`: if `|r_a| ≤ ρ < 1` for all `a ≥ 1`, then `|E r K m| ≤ (1 − ρ)^{−K}` for every `m`;
* `coeff_divByMonic`: the coefficients of the polynomial part `X^k /ₘ F_K` are
  `coeff_j = E r K (k − 1 − j)` for `j < k` and `0` otherwise.

So all the "reorganised residue sums" of PROOF §4 are bounded, although the individual residues
`1/F_K'(r_a)` are exponentially large.
-/

open Polynomial Finset

namespace LucasU.Conj

/-- `E r K m = ∑_{a=1}^K r_a^m / F_K'(r_a)`. -/
noncomputable def E (r : ℕ → ℝ) (K m : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 K, r a ^ m * Lagrange.nodalWeight (Icc 1 K) r a

theorem E_zero (r : ℕ → ℝ) (m : ℕ) : E r 0 m = 0 := by
  simp [E]

theorem E_base {r : ℕ → ℝ} {K m : ℕ} (hr : Set.InjOn r (Icc 1 K)) (hm : m < K) :
    E r K m = if m = K - 1 then 1 else 0 := by
  have hdeg : (X ^ m : ℝ[X]).degree < ((#(Icc 1 K) : ℕ) : WithBot ℕ) := by
    rw [degree_X_pow, Nat.card_Icc]; exact_mod_cast (by omega : m < K + 1 - 1)
  have h := Lagrange.coeff_eq_sum hr hdeg
  rw [Nat.card_Icc, coeff_X_pow] at h
  have hK : K + 1 - 1 - 1 = K - 1 := by omega
  rw [hK] at h
  have hterm : ∀ a ∈ Icc 1 K, r a ^ m * Lagrange.nodalWeight (Icc 1 K) r a =
      eval (r a) (X ^ m) / ∏ j ∈ (Icc 1 K).erase a, (r a - r j) := by
    intro a _
    rw [eval_X_pow, Lagrange.nodalWeight, prod_inv_distrib, div_eq_mul_inv]
  rw [E, sum_congr rfl hterm, ← h]
  by_cases hmK : m = K - 1
  · simp [hmK]
  · simp [hmK, Ne.symm hmK]

theorem nodalWeight_succ {r : ℕ → ℝ} {K a : ℕ} (ha : a ∈ Icc 1 K) :
    Lagrange.nodalWeight (Icc 1 (K + 1)) r a =
      (r a - r (K + 1))⁻¹ * Lagrange.nodalWeight (Icc 1 K) r a := by
  have hI : Icc 1 (K + 1) = insert (K + 1) (Icc 1 K) := by ext x; simp; omega
  have hne : K + 1 ≠ a := by simp at ha; omega
  have hnot : K + 1 ∉ (Icc 1 K).erase a := by simp
  rw [Lagrange.nodalWeight, Lagrange.nodalWeight, hI, erase_insert_of_ne hne, prod_insert hnot]

theorem E_succ {r : ℕ → ℝ} {K : ℕ} (hr : Set.InjOn r (Icc 1 (K + 1))) (m : ℕ) :
    E r (K + 1) (m + 1) = r (K + 1) * E r (K + 1) m + E r K m := by
  have key : E r (K + 1) (m + 1) - r (K + 1) * E r (K + 1) m =
      ∑ a ∈ Icc 1 (K + 1),
        r a ^ m * (r a - r (K + 1)) * Lagrange.nodalWeight (Icc 1 (K + 1)) r a := by
    rw [E, E, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    ring
  rw [sum_Icc_succ_top (by omega), sub_self, mul_zero, zero_mul, add_zero] at key
  have hsum : ∑ a ∈ Icc 1 K,
        r a ^ m * (r a - r (K + 1)) * Lagrange.nodalWeight (Icc 1 (K + 1)) r a = E r K m := by
    rw [E]
    refine sum_congr rfl fun a ha => ?_
    have hne : r a - r (K + 1) ≠ 0 := by
      refine sub_ne_zero.mpr fun h => ?_
      have h1 : a ∈ (Icc 1 (K + 1) : Set ℕ) := by simp at ha ⊢; omega
      have h2 : K + 1 ∈ (Icc 1 (K + 1) : Set ℕ) := by simp
      have := hr h1 h2 h
      simp at ha; omega
    rw [nodalWeight_succ ha]
    field_simp
  rw [hsum] at key
  linarith

theorem E_bound {r : ℕ → ℝ} {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hr : ∀ a, 1 ≤ a → |r a| ≤ ρ) (hinj : Set.InjOn r (Set.Ici 1)) :
    ∀ K m, |E r K m| ≤ ((1 - ρ)⁻¹) ^ K := by
  have hpos : 0 < 1 - ρ := by linarith
  have hge1 : 1 ≤ (1 - ρ)⁻¹ := one_le_inv₀ hpos |>.mpr (by linarith)
  have hinjK : ∀ K, Set.InjOn r (Icc 1 K) := fun K =>
    hinj.mono (by intro x hx; simp at hx ⊢; omega)
  intro K
  induction K with
  | zero => intro m; simp [E_zero]
  | succ K ihK =>
    intro m
    have hbase : ∀ m, m < K + 1 → |E r (K + 1) m| ≤ ((1 - ρ)⁻¹) ^ (K + 1) := by
      intro m hm
      rw [E_base (hinjK _) hm]
      have : (1 : ℝ) ≤ ((1 - ρ)⁻¹) ^ (K + 1) := one_le_pow₀ hge1
      split_ifs
      · rw [abs_one]; exact this
      · rw [abs_zero]; exact le_trans zero_le_one this
    induction m with
    | zero => exact hbase 0 (by omega)
    | succ m ihm =>
      by_cases hm : m + 1 < K + 1
      · exact hbase _ hm
      · rw [E_succ (hinjK _)]
        have h1 := hr (K + 1) (by omega)
        have h2 := ihK m
        calc |r (K + 1) * E r (K + 1) m + E r K m|
            ≤ |r (K + 1)| * |E r (K + 1) m| + |E r K m| := by
              rw [← abs_mul]; exact abs_add_le _ _
          _ ≤ ρ * ((1 - ρ)⁻¹) ^ (K + 1) + ((1 - ρ)⁻¹) ^ K := by
              gcongr
          _ = ((1 - ρ)⁻¹) ^ (K + 1) := by
              rw [pow_succ]; field_simp; ring

/-! ### The polynomial part `X^k /ₘ F_K` -/

theorem divByMonic_step {r : ℕ → ℝ} {K : ℕ} (hK : 1 ≤ K) (hr : Set.InjOn r (Icc 1 K)) (k : ℕ) :
    X ^ (k + 1) /ₘ Lagrange.nodal (Icc 1 K) r =
      X * (X ^ k /ₘ Lagrange.nodal (Icc 1 K) r) + C (E r K k) := by
  have hF : (Lagrange.nodal (Icc 1 K) r).Monic := Lagrange.nodal_monic
  have hFnat : (Lagrange.nodal (Icc 1 K) r).natDegree = K := by
    rw [Lagrange.natDegree_nodal, Nat.card_Icc]; omega
  have hFdeg : (Lagrange.nodal (Icc 1 K) r).degree = K := by
    rw [Lagrange.degree_nodal, Nat.card_Icc, Nat.add_sub_cancel]
  have hnode : ∀ a ∈ Icc 1 K, eval (r a) (Lagrange.nodal (Icc 1 K) r) = 0 :=
    fun a ha => Lagrange.eval_nodal_at_node ha
  have hEk : E r K k = ∑ a ∈ Icc 1 K, r a ^ k / ∏ j ∈ (Icc 1 K).erase a, (r a - r j) := by
    rw [E]; refine sum_congr rfl fun a _ => ?_
    rw [Lagrange.nodalWeight, prod_inv_distrib, div_eq_mul_inv]
  rw [hEk]
  generalize Lagrange.nodal (Icc 1 K) r = F at hF hFnat hFdeg hnode ⊢
  generalize hq : X ^ k /ₘ F = q
  generalize hR : X ^ k %ₘ F = R
  have hRq : R + F * q = X ^ k := by rw [← hR, ← hq]; exact modByMonic_add_div _ _
  have hRdeg : R.degree < K := by rw [← hFdeg, ← hR]; exact degree_modByMonic_lt _ hF
  -- the leading coefficient of the remainder is `E r K k`
  have hc : R.coeff (K - 1) = ∑ a ∈ Icc 1 K, r a ^ k / ∏ j ∈ (Icc 1 K).erase a, (r a - r j) := by
    have hdeg : R.degree < ((#(Icc 1 K) : ℕ) : WithBot ℕ) := by
      rw [Nat.card_Icc]; convert hRdeg using 2; omega
    have h := Lagrange.coeff_eq_sum hr hdeg
    rw [Nat.card_Icc, show K + 1 - 1 - 1 = K - 1 by omega] at h
    rw [h]
    refine sum_congr rfl fun a ha => ?_
    have hev : eval (r a) R = r a ^ k := by
      have := congrArg (eval (r a)) hRq
      rw [eval_add, eval_mul, hnode a ha, zero_mul, add_zero, eval_X_pow] at this
      exact this
    rw [hev]
  have huniq := (div_modByMonic_unique (f := X ^ (k + 1)) (X * q + C (R.coeff (K - 1)))
    (X * R - C (R.coeff (K - 1)) * F) hF ⟨?_, ?_⟩).1
  · rw [huniq, hc]
  · rw [pow_succ, ← hRq]; ring
  · rw [hFdeg, degree_lt_iff_coeff_zero]
    intro m hm
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [coeff_sub, coeff_X_mul, coeff_C_mul]
    rcases Nat.lt_or_ge n K with hn | hn
    · have hnK : n = K - 1 := by omega
      have hF1 : F.coeff (n + 1) = 1 := by
        rw [show n + 1 = F.natDegree by omega]; exact hF.coeff_natDegree
      rw [hF1, hnK]; ring
    · rw [coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hRdeg (by exact_mod_cast hn)),
        coeff_eq_zero_of_natDegree_lt (p := F) (by omega)]
      ring

theorem coeff_divByMonic {r : ℕ → ℝ} {K : ℕ} (hK : 1 ≤ K) (hr : Set.InjOn r (Icc 1 K)) :
    ∀ k j, (X ^ k /ₘ Lagrange.nodal (Icc 1 K) r).coeff j =
      if j < k then E r K (k - 1 - j) else 0 := by
  intro k
  induction k with
  | zero =>
    intro j
    have h0 : (X ^ 0 : ℝ[X]) /ₘ Lagrange.nodal (Icc 1 K) r = 0 := by
      rw [divByMonic_eq_zero_iff Lagrange.nodal_monic, Lagrange.degree_nodal, Nat.card_Icc,
        pow_zero, degree_one]
      exact_mod_cast (by omega : 0 < K + 1 - 1)
    rw [h0]; simp
  | succ k ih =>
    intro j
    rw [divByMonic_step hK hr]
    cases j with
    | zero => simp
    | succ j =>
      rw [coeff_add, coeff_X_mul, coeff_C_succ, add_zero, ih j]
      by_cases hj : j < k
      · simp only [hj, show j + 1 < k + 1 by omega, ↓reduceIte]; congr 1; omega
      · simp only [hj, show ¬ j + 1 < k + 1 by omega, ↓reduceIte]

end LucasU.Conj
