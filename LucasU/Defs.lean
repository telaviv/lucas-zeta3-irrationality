import Mathlib

/-!
# Definitions for the irrationality of `∑ 1/U_n³` (Lucas sequences of quadratic units)

Written proof: `handoff/fibzeta/pell/PROOF_U.md` (parametrised version of `handoff/fibzeta/PROOF.md`).
This library generalises `lean_fibzeta` (`FibZeta`, the case `a = 1`, `E = 1`).

The algebraic construction is written over a field `𝕜` with a sign `ε : ℤ` (`ε = ±1`, the norm of the
unit) and a parameter `τ : 𝕜`.  With `w = ε τ²` and `ρ = ε τ`:

* `alpha ε τ k = ρ w^k`, `nu ε τ k = k(k+1) α_k/(1 − α_k)` (moments `L(s^k)`);
* `psi ε τ N = τ^{3N}/(1 − w^N)³`, `S ε τ a = ∑_{N ≤ a} ψ_N`;
* `node ε τ a = w^{−a}` (the poles of `1/D_K`), `F ε τ K = ∏ (s − x_a)` (monic),
  `D_K(s) = ∏ (1 − w^a s) = (−1)^K w^{A_K} F(s)`;
* `L_X(1/(s − x_a)) = −2 τ^a (X − S_a)` (since `w/ρ = τ` for both signs);
* `Delta ε τ K = det [L_X(s^{i+j}/D_K)]_{0 ≤ i,j < K} ∈ 𝕜[X]`.

For `ε = −1` every definition coincides with the `FibZeta` one.

The real side is stated for an arbitrary `t` (the analytic ingredients only need `0 < t ≤ φ⁻¹`); the
recurrence `U_{n+1} = a U_n + E U_{n−1}` enters only through `tU a E = 1/α` and the assembly.
-/

open Polynomial Finset

namespace LucasU

/-! ### The generic construction -/

section Generic

variable {𝕜 : Type*} [Field 𝕜]

/-- `w = ε τ²`. -/
def wpar (ε : ℤ) (τ : 𝕜) : 𝕜 := (ε : 𝕜) * τ ^ 2

/-- `α_k = ρ w^k = (ε τ)(ε τ²)^k`. -/
def alpha (ε : ℤ) (τ : 𝕜) (k : ℕ) : 𝕜 := ((ε : 𝕜) * τ) * wpar ε τ ^ k

/-- The polynomial moments `ν_k = L(s^k) = k(k+1) α_k/(1 − α_k)`; `ν_0 = 0`. -/
def nu (ε : ℤ) (τ : 𝕜) (k : ℕ) : 𝕜 := ((k : 𝕜) * ((k : 𝕜) + 1)) * alpha ε τ k / (1 - alpha ε τ k)

/-- `ψ_N = τ^{3N}/(1 − w^N)³`; at `τ = t = 1/α` this is `U_N^{−3}/(D√D)`. -/
def psi (ε : ℤ) (τ : 𝕜) (N : ℕ) : 𝕜 := τ ^ (3 * N) / (1 - wpar ε τ ^ N) ^ 3

/-- The partial sums `S_a = ∑_{N=1}^a ψ_N`. -/
def S (ε : ℤ) (τ : 𝕜) (a : ℕ) : 𝕜 := ∑ N ∈ Icc 1 a, psi ε τ N

/-- The pole `x_a = w^{−a}` of `1/D_K`. -/
def node (ε : ℤ) (τ : 𝕜) (a : ℕ) : 𝕜 := (wpar ε τ ^ a)⁻¹

/-- `F_K(s) = ∏_{a=1}^K (s − x_a)` (monic). -/
noncomputable def F (ε : ℤ) (τ : 𝕜) (K : ℕ) : 𝕜[X] := ∏ a ∈ Icc 1 K, (X - C (node ε τ a))

/-- The functional on polynomials: `L(∑ c_j s^j) = ∑ c_j ν_j`. -/
noncomputable def Lpoly (ε : ℤ) (τ : 𝕜) (f : 𝕜[X]) : 𝕜 := ∑ j ∈ f.support, f.coeff j * nu ε τ j

/-- The residue coefficient `x_a^k / F_K'(x_a)` of `s^k/F_K` at `x_a`. -/
noncomputable def res (ε : ℤ) (τ : 𝕜) (K k a : ℕ) : 𝕜 :=
  node ε τ a ^ k / (derivative (F ε τ K)).eval (node ε τ a)

/-- Constant term (in `X`) of `L_X(s^k/F_K)`. -/
noncomputable def mConst (ε : ℤ) (τ : 𝕜) (K k : ℕ) : 𝕜 :=
  Lpoly ε τ (X ^ k /ₘ F ε τ K) + 2 * ∑ a ∈ Icc 1 K, res ε τ K k a * τ ^ a * S ε τ a

/-- Coefficient of `X` in `L_X(s^k/F_K)`: `−2 ∑_a res_a τ^a`. -/
noncomputable def mLin (ε : ℤ) (τ : 𝕜) (K k : ℕ) : 𝕜 :=
  -(2 * ∑ a ∈ Icc 1 K, res ε τ K k a * τ ^ a)

/-- `A_K = K(K+1)/2`. -/
def AK (K : ℕ) : ℕ := K * (K + 1) / 2

/-- The normalisation `1/D_K = nrm · 1/F_K`, `nrm = (−1)^K w^{−A_K}`. -/
def nrm (ε : ℤ) (τ : 𝕜) (K : ℕ) : 𝕜 := (-1) ^ K * (wpar ε τ ^ AK K)⁻¹

/-- The `X`-coefficient matrix of `[L_X(s^{i+j}/D_K)]`. -/
noncomputable def hankelLin (ε : ℤ) (τ : 𝕜) (K : ℕ) : Matrix (Fin K) (Fin K) 𝕜 :=
  Matrix.of fun i j => nrm ε τ K * mLin ε τ K (i.val + j.val)

/-- The constant-coefficient matrix of `[L_X(s^{i+j}/D_K)]`. -/
noncomputable def hankelConst (ε : ℤ) (τ : 𝕜) (K : ℕ) : Matrix (Fin K) (Fin K) 𝕜 :=
  Matrix.of fun i j => nrm ε τ K * mConst ε τ K (i.val + j.val)

/-- `Δ_K(X) = det [L_X(s^{i+j}/D_K)]_{0 ≤ i,j < K} ∈ 𝕜[X]`. -/
noncomputable def Delta (ε : ℤ) (τ : 𝕜) (K : ℕ) : 𝕜[X] :=
  Matrix.det ((X : 𝕜[X]) • (hankelLin ε τ K).map C + (hankelConst ε τ K).map C)

end Generic

/-! ### The real side, for a general `t` -/

/-- `Ξ(t) = ∑_{N ≥ 1} ψ_N(t)`. -/
noncomputable def XiR (ε : ℤ) (t : ℝ) : ℝ := ∑' N : ℕ, psi ε t (N + 1)

/-- `θ(θ+1)h = s² h'' + 2 s h'` (`θ = s d/ds`). -/
noncomputable def thetaOp (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  s ^ 2 * deriv (deriv h) s + 2 * s * deriv h s

/-- The real functional `L(h) = ∑_{n ≥ 1} ρⁿ [θ(θ+1)h](wⁿ)`, `ρ = ε t`, `w = ε t²`. -/
noncomputable def Lfun (ε : ℤ) (t : ℝ) (h : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, ((ε : ℝ) * t) ^ (n + 1) * thetaOp h (wpar ε t ^ (n + 1))

/-- `D_K(s) = ∏_{a=1}^K (1 − w^a s)`. -/
noncomputable def DK (ε : ℤ) (t : ℝ) (K : ℕ) (s : ℝ) : ℝ :=
  ∏ a ∈ Icc 1 K, (1 - wpar ε t ^ a * s)

/-! ### Lucas sequences of quadratic units -/

/-- Admissible parameters: `E = 1, a ≥ 1` (unit of norm `−1`) or `E = −1, a ≥ 3` (norm `+1`). -/
def Admissible (a : ℕ) (E : ℤ) : Prop := (E = 1 ∧ 1 ≤ a) ∨ (E = -1 ∧ 3 ≤ a)

/-- `U_0 = 0`, `U_1 = 1`, `U_{n+2} = a U_{n+1} + E U_n`. -/
def Useq (a : ℕ) (E : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => a * Useq a E (n + 1) + E * Useq a E n

/-- The target `∑_{n ≥ 1} 1/U_n³`. -/
noncomputable def zetaU (a : ℕ) (E : ℤ) : ℝ := ∑' n : ℕ, 1 / ((Useq a E (n + 1) : ℤ) : ℝ) ^ 3

/-- The discriminant `D = a² + 4E`. -/
def discr (a : ℕ) (E : ℤ) : ℤ := (a : ℤ) ^ 2 + 4 * E

/-- The unit `α = (a + √D)/2 > 1`. -/
noncomputable def alphaR (a : ℕ) (E : ℤ) : ℝ := ((a : ℝ) + √((discr a E : ℤ) : ℝ)) / 2

/-- `t = 1/α`. -/
noncomputable def tU (a : ℕ) (E : ℤ) : ℝ := (alphaR a E)⁻¹

/-! ### Quantities of the real decay bound -/

/-- `a_j = ∑_{u=1}^{j} ⌈u/3⌉`. -/
def aj (j : ℕ) : ℕ := ∑ u ∈ Icc 1 j, (u + 2) / 3

/-- `b_K = 2 ∑_{j<K} a_j`; `|Δ_K(Ξ)| ≲ |w|^{b_K} = t^{2 b_K}`. -/
def bK (K : ℕ) : ℕ := 2 * ∑ j ∈ range K, aj j

/-! ### The cyclotomic exponents -/

/-- The cluster cost `c(m)`. -/
def cW (m : ℕ) : ℕ := ∑ j ∈ range (m - 1), (m + 2 - 2 * j)

/-- The cluster cost `c′(m)` (the cluster `r = e`). -/
def cW' (m : ℕ) : ℕ := ∑ j ∈ range m, (m + 2 - 2 * j)

/-- The size `m_r = #{a ∈ [1, K] : a ≡ r (mod e)}`. -/
def clusterSize (K e r : ℕ) : ℕ := ((Icc 1 K).filter (fun a => a % e = r % e)).card

/-- The chosen primitive `d`-th root of unity `exp(2πi/d)`. -/
noncomputable def zetaC (d : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / d)

/-- `e(d)`: the order of `w(ζ) = ε ζ²` for a primitive `d`-th root `ζ` (type (W)). -/
noncomputable def eW (ε : ℤ) (d : ℕ) : ℕ := orderOf ((ε : ℂ) * zetaC d ^ 2)

/-- Type (α): `α_k(ζ) = 1` for `ζ = zetaC d`. -/
def IsAlphaRoot (ε : ℤ) (d k : ℕ) : Prop := ((ε : ℂ) * zetaC d) * ((ε : ℂ) * zetaC d ^ 2) ^ k = 1

open Classical in
/-- The α-part of the local exponent: `max(0, K − 1 − k_min(d))` if some `1 ≤ k ≤ K − 2` has
`α_k(ζ) = 1`, else `0`. -/
noncomputable def nAlpha (ε : ℤ) (K d : ℕ) : ℕ :=
  if h : ∃ k, 1 ≤ k ∧ k ≤ K - 2 ∧ IsAlphaRoot ε d k then K - 1 - Nat.find h else 0

open Classical in
/-- The W-part of the local exponent: if `e = e(d) ≤ K`, `∑_{r=1}^{e−1} c(m_r) + c′(m_e)`, else `0`. -/
noncomputable def nW (ε : ℤ) (K d : ℕ) : ℕ :=
  if 1 ≤ eW ε d ∧ eW ε d ≤ K then
    (∑ r ∈ Icc 1 (eW ε d - 1), cW (clusterSize K (eW ε d) r)) + cW' (clusterSize K (eW ε d) (eW ε d))
  else 0

/-- The local exponent `b_{K,d}`. -/
noncomputable def nExp (ε : ℤ) (K d : ℕ) : ℕ := nW ε K d + nAlpha ε K d

/-- The clearing polynomial `C_K(τ) = ∏_{d=1}^{4K} Φ_d(τ)^{b_{K,d}} ∈ ℤ[τ]`. -/
noncomputable def CKpoly (ε : ℤ) (K : ℕ) : ℤ[X] := ∏ d ∈ Icc 1 (4 * K), cyclotomic d ℤ ^ nExp ε K d

end LucasU
