import Mathlib

-- Generalised from lean_fibzeta FibZeta/NonVan/Algebra.lean (ε = ±1, general t).
-- Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/NonvanishingAlgebra.lean and
-- lean/QZeta3/NonvanishingAnalytic.lean (Apache-2.0, Lean formalisation by F. Solomon Admasu).
-- Changes: namespace; nodes only need `|t a| → ∞` (ours alternate in sign), so the nonflatness
-- hypothesis also returns eventual nonvanishing of the error near infinity; q-specific node lemmas dropped.

/-!
# Algebraic part of the moving-denominator nonvanishing argument

These lemmas do not assume any q-zeta theorem.  They isolate the polynomial
arguments in Proposition 5.1: uniqueness without division at interpolation
nodes, propagation through a singular tail, extraction of common factors,
and the final contradiction from a bounded degree and increasing root count.

The analytic inputs needed to apply them to `gramR` are deliberately stated
as hypotheses; this file does not claim to establish those inputs.
-/

open Polynomial Filter Topology Asymptotics

namespace LucasU.NonVan

/-- A singular moment matrix supplies a nonzero orthogonal polynomial with
the exact degree bound needed in the interpolation argument. -/
theorem exists_orthogonal_polynomial {n : ℕ} (hn : 0 < n)
    (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hdet : (Matrix.of fun i j : Fin n => L (Polynomial.X ^ (i.val + j.val))).det = 0) :
    ∃ Q : ℝ[X], Q ≠ 0 ∧ Q.natDegree < n ∧
      ∀ j : Fin n, L (Polynomial.X ^ j.val * Q) = 0 := by
  classical
  obtain ⟨v, hv, hkernel⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let Q : ℝ[X] := ∑ i : Fin n, v i • Polynomial.X ^ i.val
  have hcoeff : ∀ i : Fin n, Q.coeff i.val = v i := by
    intro i
    simp [Q, Polynomial.coeff_X_pow, ← Fin.ext_iff]
  have hQ : Q ≠ 0 := by
    intro h
    apply hv
    ext i
    simpa [h] using (hcoeff i).symm
  have hdegree : Q.natDegree ≤ n - 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    apply (Polynomial.natDegree_smul_le (v i) (Polynomial.X ^ i.val)).trans
    simp only [Polynomial.natDegree_X_pow]
    omega
  refine ⟨Q, hQ, by omega, ?_⟩
  intro j
  have hterm : ∀ i : Fin n, (Polynomial.X : ℝ[X]) ^ j.val *
      (v i • Polynomial.X ^ i.val) = v i • Polynomial.X ^ (j.val + i.val) := by
    intro i
    rw [mul_smul_comm, pow_add]
  have hkernelj := congrFun hkernel j
  simpa [Q, Finset.mul_sum, hterm, map_sum, map_smul, Matrix.mulVec,
    dotProduct, mul_comm] using hkernelj

/-- A polynomial growing strictly slower than `xⁿ` has degree below `n`. -/
theorem natDegree_lt_of_isLittleO_pow (P : ℝ[X]) {n : ℕ} (hn : 0 < n)
    (hP : P.eval =o[atTop] (fun x : ℝ => x ^ n)) : P.natDegree < n := by
  by_cases hzero : P = 0
  · simpa [hzero] using hn
  by_contra hdegree
  have hle : n ≤ P.natDegree := by omega
  have hbig : (fun x : ℝ => x ^ n) =O[atTop] P.eval := by
    simpa using (Polynomial.X ^ n : ℝ[X]).isBigO_atTop_of_degree_le P
      (by simpa [Polynomial.degree_eq_natDegree hzero] using hle)
  have hfrequent : ∃ᶠ x in atTop, P.eval x ≠ 0 :=
    (P.eventually_atTop_not_isRoot hzero).frequently
  exact Asymptotics.isLittleO_irrefl hfrequent (hP.trans_isBigO hbig)

/-- A polynomial of degree at most `n`, times an error tending to zero,
is little-o of `xⁿ`. -/
theorem mul_error_isLittleO_pow (Q : ℝ[X]) (n : ℕ) (E : ℝ → ℝ)
    (hdegree : Q.natDegree ≤ n) (hE : Tendsto E atTop (𝓝 0)) :
    (fun x => Q.eval x * E x) =o[atTop] (fun x => x ^ n) := by
  have hQ : Q.eval =O[atTop] (fun x : ℝ => x ^ n) := by
    simpa using Q.isBigO_atTop_of_degree_le (Polynomial.X ^ n)
      (by simpa using Polynomial.degree_le_of_natDegree_le hdegree)
  have hE' : E =o[atTop] (fun _ : ℝ => (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).mpr hE
  simpa using hQ.mul_isLittleO hE'

/-- The degree drop in the cross product of consecutive approximants follows
just from convergence of both approximation errors to zero. -/
theorem cross_natDegree_lt (F : ℝ → ℝ) (P Q R S : ℝ[X])
    {n : ℕ} (hn : 0 < n) (hQ : Q.natDegree ≤ n) (hS : S.natDegree ≤ n)
    (hfirst : Tendsto (fun x => F x * Q.eval x - P.eval x) atTop (𝓝 0))
    (hsecond : Tendsto (fun x => F x * S.eval x - R.eval x) atTop (𝓝 0)) :
    (R * Q - P * S).natDegree < n := by
  apply natDegree_lt_of_isLittleO_pow _ hn
  convert (mul_error_isLittleO_pow S n _ hS hfirst).sub
    (mul_error_isLittleO_pow Q n _ hQ hsecond) using 1
  ext x
  simp only [Polynomial.eval_sub, Polynomial.eval_mul]
  ring

/-- Uniqueness of consecutive rational interpolants.  No polynomial value
at an interpolation node is required to be nonzero. -/
theorem cross_eq_of_interpolation {n : ℕ} (F : ℝ → ℝ)
    (t : Fin n → ℝ) (ht : Function.Injective t)
    (P Q R S : ℝ[X])
    (hdegree : (R * Q - P * S).natDegree < n)
    (hfirst : ∀ i, F (t i) * Q.eval (t i) - P.eval (t i) = 0)
    (hsecond : ∀ i, F (t i) * S.eval (t i) - R.eval (t i) = 0) :
    R * Q = P * S := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    (R * Q - P * S) ht
  · intro i
    simp only [Polynomial.eval_sub, Polynomial.eval_mul]
    have hP := hfirst i
    have hR := hsecond i
    rw [← sub_eq_zero.mp hP, ← sub_eq_zero.mp hR]
    ring
  · simpa using hdegree

/-- Analytic uniqueness of consecutive rational interpolants, with the
polynomial degree bound derived rather than assumed. -/
theorem cross_eq_of_errors_tendsto {n : ℕ} (hn : 0 < n) (F : ℝ → ℝ)
    (t : Fin n → ℝ) (ht : Function.Injective t)
    (P Q R S : ℝ[X]) (hQ : Q.natDegree ≤ n) (hS : S.natDegree ≤ n)
    (hfirstLimit : Tendsto (fun x => F x * Q.eval x - P.eval x) atTop (𝓝 0))
    (hsecondLimit : Tendsto (fun x => F x * S.eval x - R.eval x) atTop (𝓝 0))
    (hfirst : ∀ i, F (t i) * Q.eval (t i) - P.eval (t i) = 0)
    (hsecond : ∀ i, F (t i) * S.eval (t i) - R.eval (t i) = 0) :
    R * Q = P * S :=
  cross_eq_of_interpolation F t ht P Q R S
    (cross_natDegree_lt F P Q R S hn hQ hS hfirstLimit hsecondLimit)
    hfirst hsecond

/-- Equality of fractions is transitive without any evaluation or division. -/
theorem cross_eq_trans {P₁ Q₁ P₂ Q₂ P₃ Q₃ : ℝ[X]}
    (hQ₂ : Q₂ ≠ 0) (h₁₂ : P₁ * Q₂ = P₂ * Q₁)
    (h₂₃ : P₂ * Q₃ = P₃ * Q₂) : P₁ * Q₃ = P₃ * Q₁ := by
  apply mul_right_cancel₀ hQ₂
  calc
    P₁ * Q₃ * Q₂ = (P₁ * Q₂) * Q₃ := by ring
    _ = (P₂ * Q₁) * Q₃ := by rw [h₁₂]
    _ = (P₂ * Q₃) * Q₁ := by ring
    _ = (P₃ * Q₂) * Q₁ := by rw [h₂₃]
    _ = P₃ * Q₁ * Q₂ := by ring

/-- Consecutive equalities force a single rational approximant on a tail. -/
theorem cross_eq_on_tail (P Q : ℕ → ℝ[X]) (N : ℕ)
    (hQ : ∀ n, N ≤ n → Q n ≠ 0)
    (hstep : ∀ n, N ≤ n → P n * Q (n + 1) = P (n + 1) * Q n) :
    ∀ n, N ≤ n → P N * Q n = P n * Q N := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
      exact cross_eq_trans (hQ n hn) ih (hstep n hn)

/-- A common reduced fraction divides both components of every equal pair. -/
theorem factor_pair_of_coprime (P Q P' Q' : ℝ[X])
    (hQ : Q ≠ 0) (hQ' : Q' ≠ 0) (hcoprime : IsCoprime P Q)
    (hcross : P * Q' = P' * Q) :
    ∃ U : ℝ[X], U ≠ 0 ∧ Q' = U * Q ∧ P' = U * P := by
  have hdiv : Q ∣ P * Q' := by
    rw [hcross]
    exact dvd_mul_left Q P'
  obtain ⟨U, hU⟩ := hcoprime.symm.dvd_of_dvd_mul_left hdiv
  have hQ'U : Q' = U * Q := hU.trans (mul_comm Q U)
  have hUne : U ≠ 0 := by
    intro h
    exact hQ' (by simpa [h] using hQ'U)
  refine ⟨U, hUne, hQ'U, ?_⟩
  apply mul_right_cancel₀ hQ
  calc
    P' * Q = P * Q' := hcross.symm
    _ = P * (U * Q) := by rw [hQ'U]
    _ = U * P * Q := by ring

/-- Every polynomial fraction with nonzero denominator has a reduced pair. -/
theorem exists_coprime_pair (P Q : ℝ[X]) (hQ : Q ≠ 0) :
    ∃ P₀ Q₀ : ℝ[X], Q₀ ≠ 0 ∧ IsCoprime P₀ Q₀ ∧ P₀ * Q = P * Q₀ := by
  obtain ⟨P₀, Q₀, hP₀, hQ₀, hcoprime⟩ := extract_gcd P Q
  have hQ₀ne : Q₀ ≠ 0 := by
    intro h
    exact hQ (by simpa [h] using hQ₀)
  refine ⟨P₀, Q₀, hQ₀ne, (gcd_isUnit_iff P₀ Q₀).mp hcoprime, ?_⟩
  calc
    P₀ * Q = P₀ * (gcd P Q * Q₀) := congrArg (P₀ * ·) hQ₀
    _ = (gcd P Q * P₀) * Q₀ := by ring
    _ = P * Q₀ := congrArg (· * Q₀) hP₀.symm

/-- Dividing an error tending to zero by a nonzero polynomial preserves
convergence to zero at positive infinity. -/
theorem tendsto_zero_of_polynomial_mul (U : ℝ[X]) (hU : U ≠ 0)
    (E : ℝ → ℝ) (hUE : Tendsto (fun x => U.eval x * E x) atTop (𝓝 0)) :
    Tendsto E atTop (𝓝 0) := by
  have hbig : (fun _ : ℝ => (1 : ℝ)) =O[atTop] U.eval := by
    simpa using (1 : ℝ[X]).isBigO_atTop_of_degree_le U
      (by simp [Polynomial.degree_eq_natDegree hU])
  have hbigE : E =O[atTop] (fun x => U.eval x * E x) := by
    simpa using hbig.mul (Asymptotics.isBigO_refl E atTop)
  exact hbigE.trans_tendsto hUE

/-- A nonzero polynomial cannot vanish on more distinct nodes than its degree. -/
theorem false_of_bounded_degree_roots (t : ℕ → ℝ) (ht : Function.Injective t)
    (N A d : ℕ) (U : ℕ → ℝ[X])
    (hU : ∀ n, N ≤ n → U n ≠ 0)
    (hdegree : ∀ n, N ≤ n → (U n).natDegree ≤ d)
    (hzero : ∀ n a, N ≤ n → A ≤ a → a < n → (U n).eval (t a) = 0) :
    False := by
  let n := max N (A + d + 1)
  have hn : N ≤ n := le_max_left _ _
  have hlarge : A + d + 1 ≤ n := le_max_right _ _
  have hnodes : Function.Injective (fun i : Fin (d + 1) => t (A + i.val)) := by
    intro i j hij
    apply Fin.ext
    exact Nat.add_left_cancel (ht hij)
  have hpoly : U n = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      (U n) hnodes
    · intro i
      exact hzero n (A + i.val) hn (by omega) (by omega)
    · simpa using Nat.lt_succ_of_le (hdegree n hn)
  exact hU n hn hpoly

/-- The final root-count contradiction, applied to the errors `Uₙ E`.
Eventual nonvanishing of `E` at the nodes comes from its first nonzero
Laurent coefficient at infinity in the analytic argument. -/
theorem false_of_bounded_degree_errors (t : ℕ → ℝ) (ht : Function.Injective t)
    (E : ℝ → ℝ) (N A d : ℕ) (U : ℕ → ℝ[X])
    (hU : ∀ n, N ≤ n → U n ≠ 0)
    (hdegree : ∀ n, N ≤ n → (U n).natDegree ≤ d)
    (hE : ∀ a, A ≤ a → E (t a) ≠ 0)
    (hzero : ∀ n a, N ≤ n → a < n → (U n).eval (t a) * E (t a) = 0) :
    False := by
  apply false_of_bounded_degree_roots t ht N A d U hU hdegree
  intro n a hn ha han
  exact (mul_eq_zero.mp (hzero n a hn han)).resolve_right (hE a ha)

/-- A nonzero Laurent limit and a vanishing product bound the degree of
the polynomial multiplier. -/
theorem natDegree_lt_of_laurent_limit (U : ℝ[X]) (hU : U ≠ 0)
    (E : ℝ → ℝ) (h : ℕ) (c : ℝ) (hc : c ≠ 0)
    (hE : Tendsto (fun x : ℝ => x ^ h * E x) atTop (𝓝 c))
    (hUE : Tendsto (fun x => U.eval x * E x) atTop (𝓝 0)) :
    U.natDegree < h := by
  by_contra hdegree
  have hle : h ≤ U.natDegree := by omega
  have hbig : (fun x : ℝ => x ^ h) =O[atTop] U.eval := by
    simpa using (Polynomial.X ^ h : ℝ[X]).isBigO_atTop_of_degree_le U
      (by simpa [Polynomial.degree_eq_natDegree hU] using hle)
  have hbigE : (fun x : ℝ => x ^ h * E x) =O[atTop]
      (fun x => U.eval x * E x) := hbig.mul (Asymptotics.isBigO_refl E atTop)
  exact hc (tendsto_nhds_unique hE (hbigE.trans_tendsto hUE))


/-- A germ at infinity that is eventually nonzero has no zeros far along any sequence whose
inverses tend to `0` through nonzero values (the nodes may alternate in sign). -/
theorem eventually_ne_zero_of_inv (E : ℝ → ℝ)
    (hE : ∀ᶠ u : ℝ in 𝓝[≠] 0, E u⁻¹ ≠ 0)
    (t : ℕ → ℝ) (ht : Tendsto (fun a => (t a)⁻¹) atTop (𝓝[≠] 0)) :
    ∃ A : ℕ, ∀ a, A ≤ a → E (t a) ≠ 0 := by
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.1 (ht.eventually hE)
  refine ⟨A, fun a ha => ?_⟩
  simpa using hA a ha

/-- The final normality contradiction with its degree and eventual
nonvanishing conclusions derived from one Laurent limit. -/
theorem false_of_laurent_limit_errors (t : ℕ → ℝ) (ht : Function.Injective t)
    (htop : Tendsto (fun a => (t a)⁻¹) atTop (𝓝[≠] 0)) (E : ℝ → ℝ) (N h : ℕ) (c : ℝ)
    (hc : c ≠ 0) (hE : Tendsto (fun x : ℝ => x ^ h * E x) atTop (𝓝 c))
    (hEne : ∀ᶠ u : ℝ in 𝓝[≠] 0, E u⁻¹ ≠ 0)
    (U : ℕ → ℝ[X]) (hU : ∀ n, N ≤ n → U n ≠ 0)
    (hlimit : ∀ n, N ≤ n →
      Tendsto (fun x => (U n).eval x * E x) atTop (𝓝 0))
    (hzero : ∀ n a, N ≤ n → a < n → (U n).eval (t a) * E (t a) = 0) :
    False := by
  obtain ⟨A, hA⟩ := eventually_ne_zero_of_inv E hEne t htop
  apply false_of_bounded_degree_errors t ht E N A h U hU
    (fun n hn => Nat.le_of_lt (natDegree_lt_of_laurent_limit (U n) (hU n hn)
      E h c hc hE (hlimit n hn))) hA hzero

/-- The nonflatness property of a germ `F` at infinity: every error `F Q − P → 0` has a first
nonzero Laurent coefficient and is eventually nonzero near infinity. -/
def Nonflat (F : ℝ → ℝ) : Prop :=
  ∀ P Q : ℝ[X], Q ≠ 0 →
    Tendsto (fun x => F x * Q.eval x - P.eval x) atTop (𝓝 0) →
      ∃ h : ℕ, ∃ c : ℝ, c ≠ 0 ∧
        Tendsto (fun x : ℝ => x ^ h * (F x * Q.eval x - P.eval x)) atTop (𝓝 c) ∧
        ∀ᶠ u : ℝ in 𝓝[≠] 0, F u⁻¹ * Q.eval u⁻¹ - P.eval u⁻¹ ≠ 0

/-- Normality for nested rational interpolants. -/
theorem no_tail_of_interpolants (F : ℝ → ℝ) (t : ℕ → ℝ)
    (ht : Function.Injective t) (htop : Tendsto (fun a => (t a)⁻¹) atTop (𝓝[≠] 0))
    (hnonflat : Nonflat F)
    (N : ℕ) (hN : 0 < N) (P Q : ℕ → ℝ[X])
    (hQ : ∀ n, N ≤ n → Q n ≠ 0)
    (hdegree : ∀ n, N ≤ n → (Q n).natDegree < n)
    (hlimit : ∀ n, N ≤ n →
      Tendsto (fun x => F x * (Q n).eval x - (P n).eval x) atTop (𝓝 0))
    (hzero : ∀ n a, N ≤ n → a < n →
      F (t a) * (Q n).eval (t a) - (P n).eval (t a) = 0) :
    False := by
  classical
  have hstep : ∀ n, N ≤ n → P n * Q (n + 1) = P (n + 1) * Q n := by
    intro n hn
    apply Eq.symm
    apply cross_eq_of_errors_tendsto (by omega) F (fun i : Fin n => t i.val)
      (ht.comp Fin.val_injective) (P n) (Q n) (P (n + 1)) (Q (n + 1))
      (by have := hdegree n hn; omega)
      (by have := hdegree (n + 1) (by omega); omega)
      (hlimit n hn) (hlimit (n + 1) (by omega))
    · intro i
      exact hzero n i.val hn i.isLt
    · intro i
      exact hzero (n + 1) i.val (by omega) (by omega)
  have hsame := cross_eq_on_tail P Q N hQ hstep
  obtain ⟨P₀, Q₀, hQ₀, hcoprime, hcross⟩ := exists_coprime_pair (P N) (Q N) (hQ N le_rfl)
  have hsame₀ : ∀ n, N ≤ n → P₀ * Q n = P n * Q₀ := by
    intro n hn
    exact cross_eq_trans (hQ N le_rfl) hcross (hsame n hn)
  have hfactors : ∀ n, N ≤ n → ∃ U : ℝ[X],
      U ≠ 0 ∧ Q n = U * Q₀ ∧ P n = U * P₀ := by
    intro n hn
    exact factor_pair_of_coprime P₀ Q₀ (P n) (Q n) hQ₀ (hQ n hn)
      hcoprime (hsame₀ n hn)
  let U : ℕ → ℝ[X] := fun n => if hn : N ≤ n then (hfactors n hn).choose else 1
  have hU : ∀ n, N ≤ n → U n ≠ 0 ∧ Q n = U n * Q₀ ∧ P n = U n * P₀ := by
    intro n hn
    simpa only [U, dite_eq_left hn] using (hfactors n hn).choose_spec
  let E : ℝ → ℝ := fun x => F x * Q₀.eval x - P₀.eval x
  have herror : ∀ n, N ≤ n → ∀ x,
      (U n).eval x * E x = F x * (Q n).eval x - (P n).eval x := by
    intro n hn x
    rw [(hU n hn).2.1, (hU n hn).2.2]
    simp only [Polynomial.eval_mul, E]
    ring
  have hUE : ∀ n, N ≤ n → Tendsto (fun x => (U n).eval x * E x) atTop (𝓝 0) := by
    intro n hn
    simpa only [herror n hn] using hlimit n hn
  have hE : Tendsto E atTop (𝓝 0) :=
    tendsto_zero_of_polynomial_mul (U N) (hU N le_rfl).1 E (hUE N le_rfl)
  obtain ⟨h, c, hc, hleading, hne⟩ := hnonflat P₀ Q₀ hQ₀ hE
  apply false_of_laurent_limit_errors t ht htop E N h c hc hleading hne U
    (fun n hn => (hU n hn).1) hUE
  intro n a hn ha
  rw [herror n hn]
  exact hzero n a hn ha

/-- General moving-moment normality theorem. -/
theorem frequently_nonsingular_moment_matrix (F : ℝ → ℝ) (t : ℕ → ℝ)
    (ht : Function.Injective t) (htop : Tendsto (fun a => (t a)⁻¹) atTop (𝓝[≠] 0))
    (L : ℕ → (ℝ[X] →ₗ[ℝ] ℝ))
    (hnonflat : Nonflat F)
    (hinterpolant : ∀ n, 0 < n → ∀ Q : ℝ[X], Q ≠ 0 → Q.natDegree < n →
      (∀ j : Fin n, L n (Polynomial.X ^ j.val * Q) = 0) →
      ∃ P : ℝ[X],
        Tendsto (fun x => F x * Q.eval x - P.eval x) atTop (𝓝 0) ∧
        ∀ a, a < n → F (t a) * Q.eval (t a) - P.eval (t a) = 0) :
    ∀ N : ℕ, ∃ n, N ≤ n ∧
      (Matrix.of fun i j : Fin n => L n (Polynomial.X ^ (i.val + j.val))).det ≠ 0 := by
  classical
  intro N
  by_contra h
  push Not at h
  let N' := max N 1
  have hN' : 0 < N' := by dsimp [N']; omega
  have hpairs : ∀ n, N' ≤ n → ∃ P Q : ℝ[X],
      Q ≠ 0 ∧ Q.natDegree < n ∧
      Tendsto (fun x => F x * Q.eval x - P.eval x) atTop (𝓝 0) ∧
      ∀ a, a < n → F (t a) * Q.eval (t a) - P.eval (t a) = 0 := by
    intro n hn
    have hnpos : 0 < n := by omega
    have hNn : N ≤ n := (le_max_left N 1).trans hn
    obtain ⟨Q, hQ, hdegree, horth⟩ := exists_orthogonal_polynomial hnpos (L n) (h n hNn)
    obtain ⟨P, hlimit, hzero⟩ := hinterpolant n hnpos Q hQ hdegree horth
    exact ⟨P, Q, hQ, hdegree, hlimit, hzero⟩
  let P : ℕ → ℝ[X] := fun n => if hn : N' ≤ n then (hpairs n hn).choose else 0
  let Q : ℕ → ℝ[X] := fun n => if hn : N' ≤ n then
    (hpairs n hn).choose_spec.choose else 1
  have hpair : ∀ n, N' ≤ n → Q n ≠ 0 ∧ (Q n).natDegree < n ∧
      Tendsto (fun x => F x * (Q n).eval x - (P n).eval x) atTop (𝓝 0) ∧
      ∀ a, a < n → F (t a) * (Q n).eval (t a) - (P n).eval (t a) = 0 := by
    intro n hn
    simpa only [P, Q, dite_eq_left hn] using (hpairs n hn).choose_spec.choose_spec
  exact no_tail_of_interpolants F t ht htop hnonflat N' hN' P Q
    (fun n hn => (hpair n hn).1)
    (fun n hn => (hpair n hn).2.1)
    (fun n hn => (hpair n hn).2.2.1)
    (fun n a hn ha => (hpair n hn).2.2.2 a ha)

/-! ### Meromorphic input (from `NonvanishingAnalytic.lean`) -/

/-- Inversion takes positive infinity into a punctured neighborhood of zero. -/
theorem inv_tendsto_punctured_zero :
    Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨tendsto_inv_atTop_zero, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simpa using inv_ne_zero (ne_of_gt hx)

/-- A polynomial evaluated at the inverse variable is meromorphic at zero. -/
theorem polynomial_eval_inv_meromorphic (P : ℝ[X]) :
    MeromorphicAt (fun u : ℝ => P.eval u⁻¹) 0 := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      convert hP.add hQ using 1
      ext u
      simp
  | monomial n c =>
      convert (MeromorphicAt.const c 0).mul (((MeromorphicAt.id (0 : ℝ)).inv).pow n) using 1
      ext u
      simp

/-- A meromorphic function with a nonzero germ at infinity and a vanishing
limit has a finite Laurent leading term, and is eventually nonzero near infinity. -/
theorem exists_laurent_limit_of_meromorphic_inv (E : ℝ → ℝ)
    (hmeromorphic : MeromorphicAt (fun u : ℝ => E u⁻¹) 0)
    (hnonzero : ¬ ∀ᶠ u : ℝ in 𝓝[≠] 0, E u⁻¹ = 0)
    (hlimit : Tendsto E atTop (𝓝 0)) :
    ∃ h : ℕ, ∃ c : ℝ, c ≠ 0 ∧
      Tendsto (fun x : ℝ => x ^ h * E x) atTop (𝓝 c) ∧
      ∀ᶠ u : ℝ in 𝓝[≠] 0, E u⁻¹ ≠ 0 := by
  let f : ℝ → ℝ := fun u => E u⁻¹
  have htop : meromorphicOrderAt f 0 ≠ ⊤ := by
    exact fun h => hnonzero (meromorphicOrderAt_eq_top_iff.mp h)
  have hinv := inv_tendsto_punctured_zero
  have hlimf : Tendsto (fun x : ℝ => f x⁻¹) atTop (𝓝 0) := by
    simpa [f] using hlimit
  have hnonneg : 0 ≤ meromorphicOrderAt f 0 := by
    by_contra h
    have hnegative : meromorphicOrderAt f 0 < 0 := lt_of_not_ge h
    have hdiverges := (tendsto_cobounded_of_meromorphicOrderAt_neg hnegative).comp hinv
    have hnorm : Tendsto (fun x : ℝ => ‖f x⁻¹‖) atTop atTop :=
      tendsto_norm_atTop_iff_cobounded.mpr hdiverges
    exact not_tendsto_atTop_of_tendsto_nhds hlimf.norm hnorm
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp htop
  have hk0 : 0 ≤ k := by simpa [← hk] using hnonneg
  obtain ⟨g, hga, hg0, hfactor⟩ :=
    (meromorphicOrderAt_eq_int_iff hmeromorphic).mp hk.symm
  refine ⟨k.toNat, g 0, hg0, ?_, ?_⟩
  · have hcont : Tendsto (fun x : ℝ => g x⁻¹) atTop (𝓝 (g 0)) :=
      hga.continuousAt.tendsto.comp tendsto_inv_atTop_zero
    apply hcont.congr'
    filter_upwards [hinv.eventually hfactor, eventually_gt_atTop (0 : ℝ)] with x hx hxpos
    have hxn : x ≠ 0 := ne_of_gt hxpos
    have hknat : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
    simp only [sub_zero, smul_eq_mul, inv_inv] at hx
    rw [← hknat, zpow_natCast] at hx
    rw [hx, ← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hxn), one_mul]
  · have hgne : ∀ᶠ u : ℝ in 𝓝[≠] 0, g u ≠ 0 :=
      (hga.continuousAt.eventually_ne hg0).filter_mono nhdsWithin_le_nhds
    filter_upwards [hfactor, hgne, self_mem_nhdsWithin] with u hu hgu hu0
    have hu0' : u ≠ 0 := hu0
    show E u⁻¹ ≠ 0
    rw [hu]
    simp only [sub_zero, smul_eq_mul]
    exact mul_ne_zero (zpow_ne_zero _ hu0') hgu

/-- Meromorphicity at infinity and exclusion of rational germs supply all
nonflatness hypotheses of the interpolation normality theorem. -/
theorem nonflat_of_meromorphic_nonrational (F : ℝ → ℝ)
    (hmeromorphic : MeromorphicAt (fun u : ℝ => F u⁻¹) 0)
    (hnonrational : ∀ P Q : ℝ[X], Q ≠ 0 →
      ¬ ∀ᶠ x : ℝ in atTop, F x * Q.eval x - P.eval x = 0) :
    Nonflat F := by
  intro P Q hQ hlimit
  apply exists_laurent_limit_of_meromorphic_inv
    (fun x => F x * Q.eval x - P.eval x)
    ((hmeromorphic.mul (polynomial_eval_inv_meromorphic Q)).sub
      (polynomial_eval_inv_meromorphic P)) _ hlimit
  intro hzero
  apply hnonrational P Q hQ
  simpa using inv_tendsto_punctured_zero.eventually hzero

/-- The general analytic normality theorem, phrased in terms of a nonrational meromorphic
Cauchy transform and orthogonal interpolants. -/
theorem frequently_nonsingular_of_meromorphic_nonrational
    (F : ℝ → ℝ) (t : ℕ → ℝ)
    (ht : Function.Injective t) (htop : Tendsto (fun a => (t a)⁻¹) atTop (𝓝[≠] 0))
    (L : ℕ → (ℝ[X] →ₗ[ℝ] ℝ))
    (hmeromorphic : MeromorphicAt (fun u : ℝ => F u⁻¹) 0)
    (hnonrational : ∀ P Q : ℝ[X], Q ≠ 0 →
      ¬ ∀ᶠ x : ℝ in atTop, F x * Q.eval x - P.eval x = 0)
    (hinterpolant : ∀ n, 0 < n → ∀ Q : ℝ[X], Q ≠ 0 → Q.natDegree < n →
      (∀ j : Fin n, L n (Polynomial.X ^ j.val * Q) = 0) →
      ∃ P : ℝ[X],
        Tendsto (fun x => F x * Q.eval x - P.eval x) atTop (𝓝 0) ∧
        ∀ a, a < n → F (t a) * Q.eval (t a) - P.eval (t a) = 0) :
    ∀ N : ℕ, ∃ n, N ≤ n ∧
      (Matrix.of fun i j : Fin n => L n (Polynomial.X ^ (i.val + j.val))).det ≠ 0 :=
  frequently_nonsingular_moment_matrix F t ht htop L
    (nonflat_of_meromorphic_nonrational F hmeromorphic hnonrational) hinterpolant

end LucasU.NonVan
