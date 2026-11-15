/-
Generalised from lean_fibzeta FibZeta/Denom/Specialization.lean (ε = ±1, general t).
Adapted from uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/GenericSpecialization.lean
(Apache-2.0, Lean formalisation by F. Solomon Admasu). Changes: the `maps_*` lemmas are redone for the
Fibonacci construction (`alpha`, `nu`, `psi`, `S`, `node`, `F`, `res`, `mConst`, `mLin`, `nrm`).
-/
import LucasU.Denom.Localization

/-!
# Specialization of the construction along partial ring homomorphisms

A ring homomorphism `φ : R →+* 𝕝` defined on a subring `R ⊆ 𝕜` satisfying `LocalizationData R ε τ K`
carries every coefficient of `Delta ε τ K` to the corresponding coefficient of `Delta ε (φ τ) K`
(`specialize_Delta_coeff`).  In particular `Delta` commutes with field homomorphisms (`map_Delta`).
-/

open Polynomial Finset

namespace LucasU.Denom.Specialization

variable {𝕜 𝕝 : Type*} [Field 𝕜] [Field 𝕝] {R : Subring 𝕜}

/-- Graph of a specialization defined on a subring of the source field. -/
def Maps (φ : R →+* 𝕝) (a : 𝕜) (b : 𝕝) : Prop :=
  ∃ r : R, (r : 𝕜) = a ∧ φ r = b

variable {φ : R →+* 𝕝}

namespace Maps

theorem of_mem {a : 𝕜} (ha : a ∈ R) : Maps φ a (φ ⟨a, ha⟩) := ⟨⟨a, ha⟩, rfl, rfl⟩
theorem zero : Maps φ 0 0 := ⟨0, rfl, map_zero φ⟩
theorem one : Maps φ 1 1 := ⟨1, rfl, map_one φ⟩
theorem natCast (n : ℕ) : Maps φ (n : 𝕜) (n : 𝕝) := ⟨n, by simp, map_natCast φ n⟩
theorem intCast (n : ℤ) : Maps φ (n : 𝕜) (n : 𝕝) := ⟨n, by simp, map_intCast φ n⟩
theorem neg {a : 𝕜} {b : 𝕝} (h : Maps φ a b) : Maps φ (-a) (-b) := by
  obtain ⟨r, rfl, rfl⟩ := h
  exact ⟨-r, rfl, map_neg φ r⟩
theorem add {a c : 𝕜} {b d : 𝕝} (h : Maps φ a b) (h' : Maps φ c d) :
    Maps φ (a + c) (b + d) := by
  obtain ⟨r, rfl, rfl⟩ := h
  obtain ⟨s, rfl, rfl⟩ := h'
  exact ⟨r + s, rfl, map_add φ r s⟩
theorem sub {a c : 𝕜} {b d : 𝕝} (h : Maps φ a b) (h' : Maps φ c d) :
    Maps φ (a - c) (b - d) := by
  simpa only [sub_eq_add_neg] using h.add h'.neg
theorem mul {a c : 𝕜} {b d : 𝕝} (h : Maps φ a b) (h' : Maps φ c d) :
    Maps φ (a * c) (b * d) := by
  obtain ⟨r, rfl, rfl⟩ := h
  obtain ⟨s, rfl, rfl⟩ := h'
  exact ⟨r * s, rfl, map_mul φ r s⟩
theorem pow {a : 𝕜} {b : 𝕝} (h : Maps φ a b) (n : ℕ) : Maps φ (a ^ n) (b ^ n) := by
  obtain ⟨r, rfl, rfl⟩ := h
  exact ⟨r ^ n, by simp, map_pow φ r n⟩
theorem sum {ι : Type*} (s : Finset ι) {f : ι → 𝕜} {g : ι → 𝕝}
    (h : ∀ i ∈ s, Maps φ (f i) (g i)) : Maps φ (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (φ := φ))
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun i hi => h i (mem_insert_of_mem hi))
theorem prod {ι : Type*} (s : Finset ι) {f : ι → 𝕜} {g : ι → 𝕝}
    (h : ∀ i ∈ s, Maps φ (f i) (g i)) : Maps φ (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one (φ := φ))
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))
theorem inv {a : 𝕜} {b : 𝕝} (h : Maps φ a b) (hi : a⁻¹ ∈ R) :
    Maps φ a⁻¹ b⁻¹ := by
  by_cases ha : a = 0
  · subst a
    obtain ⟨r, hr, hφ⟩ := h
    have hr0 : r = 0 := Subtype.ext hr
    simp only [hr0, map_zero] at hφ
    subst b
    simpa using (zero (φ := φ))
  obtain ⟨r, hr, hφ⟩ := h
  let s : R := ⟨a⁻¹, hi⟩
  have he : r * s = 1 := by apply Subtype.ext; simpa [s, hr] using mul_inv_cancel₀ ha
  have heφ : φ r * φ s = 1 := by rw [← map_mul, he, map_one]
  refine ⟨s, rfl, ?_⟩
  rw [← hφ]
  exact eq_inv_of_mul_eq_one_right heφ
theorem div {a c : 𝕜} {b d : 𝕝} (h : Maps φ a b) (h' : Maps φ c d) (hi : c⁻¹ ∈ R) :
    Maps φ (a / c) (b / d) := by
  simpa only [div_eq_mul_inv] using h.mul (h'.inv hi)

theorem value {a : 𝕜} {b : 𝕝} (h : Maps φ a b) (ha : a ∈ R) : φ ⟨a, ha⟩ = b := by
  obtain ⟨r, hr, hφ⟩ := h
  have : (⟨a, ha⟩ : R) = r := Subtype.ext hr.symm
  simpa [this] using hφ

end Maps

/-- Coefficientwise specialization of a polynomial, witnessed by a polynomial in the subring. -/
def MapsPolynomial (φ : R →+* 𝕝) (f : 𝕜[X]) (g : 𝕝[X]) : Prop :=
  ∃ F : R[X], F.map R.subtype = f ∧ F.map φ = g

namespace MapsPolynomial

theorem add {f f' : 𝕜[X]} {g g' : 𝕝[X]} (h : MapsPolynomial φ f g)
    (h' : MapsPolynomial φ f' g') : MapsPolynomial φ (f + f') (g + g') := by
  obtain ⟨F, rfl, rfl⟩ := h
  obtain ⟨G, rfl, rfl⟩ := h'
  exact ⟨F + G, by simp, by simp⟩
theorem mul {f f' : 𝕜[X]} {g g' : 𝕝[X]} (h : MapsPolynomial φ f g)
    (h' : MapsPolynomial φ f' g') : MapsPolynomial φ (f * f') (g * g') := by
  obtain ⟨F, rfl, rfl⟩ := h
  obtain ⟨G, rfl, rfl⟩ := h'
  exact ⟨F * G, by simp, by simp⟩
theorem X : MapsPolynomial φ (Polynomial.X : 𝕜[X]) (Polynomial.X : 𝕝[X]) :=
  ⟨Polynomial.X, by simp, by simp⟩
theorem C {a : 𝕜} {b : 𝕝} (h : Maps φ a b) :
    MapsPolynomial φ (Polynomial.C a) (Polynomial.C b) := by
  obtain ⟨r, rfl, rfl⟩ := h
  exact ⟨Polynomial.C r, by simp, by simp⟩
theorem sub {f f' : 𝕜[X]} {g g' : 𝕝[X]} (h : MapsPolynomial φ f g)
    (h' : MapsPolynomial φ f' g') : MapsPolynomial φ (f - f') (g - g') := by
  obtain ⟨F, rfl, rfl⟩ := h
  obtain ⟨G, rfl, rfl⟩ := h'
  exact ⟨F - G, by simp, by simp⟩
theorem pow {f : 𝕜[X]} {g : 𝕝[X]} (h : MapsPolynomial φ f g) (n : ℕ) :
    MapsPolynomial φ (f ^ n) (g ^ n) := by
  obtain ⟨F, rfl, rfl⟩ := h
  exact ⟨F ^ n, by simp, by simp⟩
theorem prod {ι : Type*} (s : Finset ι) {f : ι → 𝕜[X]} {g : ι → 𝕝[X]}
    (h : ∀ i ∈ s, MapsPolynomial φ (f i) (g i)) :
    MapsPolynomial φ (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  choose F hF using fun i : s => h i i.property
  refine ⟨∏ i : s, F i, ?_, ?_⟩
  · simp only [Polynomial.map_prod, hF, Finset.prod_coe_sort]
  · simp only [Polynomial.map_prod, hF, Finset.prod_coe_sort]
theorem coeff {f : 𝕜[X]} {g : 𝕝[X]} (h : MapsPolynomial φ f g) (i : ℕ) :
    Maps φ (f.coeff i) (g.coeff i) := by
  obtain ⟨F, rfl, rfl⟩ := h
  exact ⟨F.coeff i, by simp, by simp⟩
theorem derivative {f : 𝕜[X]} {g : 𝕝[X]} (h : MapsPolynomial φ f g) :
    MapsPolynomial φ f.derivative g.derivative := by
  obtain ⟨F, rfl, rfl⟩ := h
  exact ⟨F.derivative, by simp, by simp⟩
theorem eval {f : 𝕜[X]} {g : 𝕝[X]} {a : 𝕜} {b : 𝕝}
    (h : MapsPolynomial φ f g) (hab : Maps φ a b) : Maps φ (f.eval a) (g.eval b) := by
  obtain ⟨F, rfl, rfl⟩ := h
  obtain ⟨r, rfl, rfl⟩ := hab
  exact ⟨F.eval r, (Polynomial.eval_map_apply R.subtype r).symm,
    (Polynomial.eval_map_apply φ r).symm⟩
theorem divByMonic {f d : 𝕜[X]} {g e : 𝕝[X]} (h : MapsPolynomial φ f g)
    (hd : MapsPolynomial φ d e) (hm : d.Monic) :
    MapsPolynomial φ (f /ₘ d) (g /ₘ e) := by
  obtain ⟨F, rfl, rfl⟩ := h
  obtain ⟨D, rfl, rfl⟩ := hd
  have hD : D.Monic := Polynomial.monic_of_injective Subtype.val_injective hm
  exact ⟨F /ₘ D, Polynomial.map_divByMonic R.subtype hD, Polynomial.map_divByMonic φ hD⟩
theorem det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : Matrix ι ι 𝕜[X]} {N : Matrix ι ι 𝕝[X]}
    (h : ∀ i j, MapsPolynomial φ (M i j) (N i j)) :
    MapsPolynomial φ M.det N.det := by
  classical
  choose F hF hG using h
  refine ⟨Matrix.det (Matrix.of F), ?_, ?_⟩
  · change (Polynomial.mapRingHom R.subtype) (Matrix.det (Matrix.of F)) = M.det
    rw [RingHom.map_det]
    congr 1
    apply Matrix.ext
    intro i j
    exact hF i j
  · change (Polynomial.mapRingHom φ) (Matrix.det (Matrix.of F)) = N.det
    rw [RingHom.map_det]
    congr 1
    apply Matrix.ext
    intro i j
    exact hG i j

end MapsPolynomial

variable {ε : ℤ} {τ : 𝕜} {σ : 𝕝} {K : ℕ}

theorem maps_w (hτ : Maps φ τ σ) : Maps φ (wpar ε τ) (wpar ε σ) :=
  (Maps.intCast ε).mul (hτ.pow 2)

theorem maps_node (h : LocalizationData R ε τ K) (hτ : Maps φ τ σ) (a : ℕ) :
    Maps φ (node ε τ a) (node ε σ a) := by
  unfold node
  exact ((maps_w hτ).pow a).inv (h.node_mem a)

theorem maps_F (h : LocalizationData R ε τ K) (hτ : Maps φ τ σ) :
    MapsPolynomial φ (F ε τ K) (F ε σ K) := by
  apply MapsPolynomial.prod
  intro a _
  exact MapsPolynomial.X.sub (MapsPolynomial.C (maps_node h hτ a))

theorem maps_res (h : LocalizationData R ε τ K) (hτ : Maps φ τ σ) (k a : ℕ)
    (ha : a ∈ Icc 1 K) : Maps φ (res ε τ K k a) (res ε σ K k a) := by
  unfold res
  exact ((maps_node h hτ a).pow k).div
    ((maps_F h hτ).derivative.eval (maps_node h hτ a)) (h.inverse_derivative_mem a ha)

theorem maps_psi (h : LocalizationData R ε τ K) (hτ : Maps φ τ σ) (N : ℕ) (hN : N ∈ Icc 1 K) :
    Maps φ (psi ε τ N) (psi ε σ N) := by
  unfold psi
  apply (hτ.pow _).div ((Maps.one.sub ((maps_w hτ).pow N)).pow 3)
  rw [← inv_pow]
  exact R.pow_mem (h.inv_geom_mem N hN) 3

theorem maps_S (h : LocalizationData R ε τ K) (hτ : Maps φ τ σ) (a : ℕ) (ha : a ≤ K) :
    Maps φ (S ε τ a) (S ε σ a) := by
  apply Maps.sum
  intro b hb
  exact maps_psi h hτ b (mem_Icc.mpr ⟨(mem_Icc.mp hb).1, (mem_Icc.mp hb).2.trans ha⟩)

theorem maps_alpha (hτ : Maps φ τ σ) (k : ℕ) : Maps φ (alpha ε τ k) (alpha ε σ k) :=
  ((Maps.intCast ε).mul hτ).mul ((maps_w hτ).pow k)

theorem maps_nu (h : LocalizationData R ε τ K) (hτ : Maps φ τ σ) (j : ℕ) (hj : j ≤ K - 2) :
    Maps φ (nu ε τ j) (nu ε σ j) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [nu_zero, nu_zero]; exact Maps.zero
  unfold nu
  exact (((Maps.natCast j).mul ((Maps.natCast j).add Maps.one)).mul (maps_alpha hτ j)).div
    (Maps.one.sub (maps_alpha hτ j)) (h.inv_alpha_mem j (mem_Icc.mpr ⟨hj0, hj⟩))

theorem maps_quotient_moment (h : LocalizationData R ε τ K) (hτ : Maps φ τ σ)
    (k : ℕ) (hk : k ≤ 2 * K - 2) :
    Maps φ (Lpoly ε τ (X ^ k /ₘ F ε τ K)) (Lpoly ε σ (X ^ k /ₘ F ε σ K)) := by
  have hd (v : 𝕜) : (X ^ k /ₘ F ε v K).natDegree ≤ K - 2 := by
    have := natDegree_quotient_le (ε := ε) v K (X ^ k : 𝕜[X]) (n := k) (by rw [natDegree_X_pow])
    omega
  have hw : (X ^ k /ₘ F ε σ K).natDegree ≤ K - 2 := by
    have := natDegree_quotient_le (ε := ε) σ K (X ^ k : 𝕝[X]) (n := k) (by rw [natDegree_X_pow])
    omega
  rw [Lpoly_eq_sum_range τ _ (K + 1) (by have := hd τ; omega),
    Lpoly_eq_sum_range σ _ (K + 1) (by omega)]
  apply Maps.sum
  intro j _
  by_cases hjK : j ≤ K - 2
  · exact (((MapsPolynomial.X.pow k).divByMonic (maps_F h hτ) (F_monic τ K)).coeff j).mul
      (maps_nu h hτ j hjK)
  · rw [coeff_eq_zero_of_natDegree_lt (by have := hd τ; omega),
      coeff_eq_zero_of_natDegree_lt (by omega), zero_mul, zero_mul]
    exact Maps.zero

theorem maps_mConst (h : LocalizationData R ε τ K) (hτ : Maps φ τ σ)
    (k : ℕ) (hk : k ≤ 2 * K - 2) : Maps φ (mConst ε τ K k) (mConst ε σ K k) := by
  apply Maps.add (maps_quotient_moment h hτ k hk)
  apply (Maps.natCast 2).mul |> fun f => by simpa using f (Maps.sum _ fun a ha =>
    ((maps_res h hτ k a ha).mul (hτ.pow a)).mul (maps_S h hτ a (mem_Icc.mp ha).2))

theorem maps_mLin (h : LocalizationData R ε τ K) (hτ : Maps φ τ σ) (k : ℕ) :
    Maps φ (mLin ε τ K k) (mLin ε σ K k) := by
  apply Maps.neg
  simpa using (Maps.natCast 2).mul (Maps.sum _ fun a ha =>
    (maps_res h hτ k a ha).mul (hτ.pow a))

theorem maps_nrm (h : LocalizationData R ε τ K) (hτ : Maps φ τ σ) :
    Maps φ (nrm ε τ K) (nrm ε σ K) := by
  unfold nrm
  exact ((Maps.one.neg).pow K).mul (((maps_w hτ).pow _).inv
    (by rw [← inv_pow]; exact R.pow_mem h.inv_w_mem _))

theorem maps_Delta (h : LocalizationData R ε τ K) (hτ : Maps φ τ σ) :
    MapsPolynomial φ (Delta ε τ K) (Delta ε σ K) := by
  apply MapsPolynomial.det
  intro i j
  have e1 : ((Polynomial.X : 𝕜[X]) • (hankelLin ε τ K).map Polynomial.C +
      (hankelConst ε τ K).map Polynomial.C) i j =
      Polynomial.X * Polynomial.C (nrm ε τ K * mLin ε τ K (i.val + j.val)) +
        Polynomial.C (nrm ε τ K * mConst ε τ K (i.val + j.val)) := by
    simp [hankelLin, hankelConst]
  have e2 : ((Polynomial.X : 𝕝[X]) • (hankelLin ε σ K).map Polynomial.C +
      (hankelConst ε σ K).map Polynomial.C) i j =
      Polynomial.X * Polynomial.C (nrm ε σ K * mLin ε σ K (i.val + j.val)) +
        Polynomial.C (nrm ε σ K * mConst ε σ K (i.val + j.val)) := by
    simp [hankelLin, hankelConst]
  rw [e1, e2]
  exact (MapsPolynomial.X.mul (MapsPolynomial.C
    ((maps_nrm h hτ).mul (maps_mLin h hτ (i.val + j.val))))).add
    (MapsPolynomial.C ((maps_nrm h hτ).mul (maps_mConst h hτ (i.val + j.val)
      (by have := i.isLt; have := j.isLt; omega))))

/-- The determinant commutes with every specialization defined on its localization ring. -/
theorem specialize_Delta_coeff (h : LocalizationData R ε τ K) (φ : R →+* 𝕝) (i : ℕ) :
    φ ⟨(Delta ε τ K).coeff i, h.Delta_coeff_mem i⟩ =
      (Delta ε (φ ⟨τ, h.base_mem⟩) K).coeff i :=
  ((maps_Delta h (Maps.of_mem h.base_mem)).coeff i).value (h.Delta_coeff_mem i)

/-- `Delta` commutes with field homomorphisms. -/
theorem map_Delta (hε : ε = 1 ∨ ε = -1) (f : 𝕜 →+* 𝕝) (τ : 𝕜) (K : ℕ) :
    (Delta ε τ K).map f = Delta ε (f τ) K := by
  let h : LocalizationData (⊤ : Subring 𝕜) ε τ K :=
    ⟨hε, by trivial, by trivial, by intros; trivial, by intros; trivial⟩
  ext i
  simpa using specialize_Delta_coeff h (f.comp (⊤ : Subring 𝕜).subtype) i

end LucasU.Denom.Specialization
