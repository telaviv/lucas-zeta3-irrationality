# LucasU/Conj — Proposition 4 (conjugate smallness)

Generalised from `lean_fibzeta/FibZeta/Conj` (τ = −φ, t = φ⁻¹) to the conjugate point τ = ε/t, ε = ±1,
0 < t ≤ φ⁻¹ (only `ε² = 1` and `0 < t < 1` are used).

Main theorems: `LucasU.Conj.conjBound (h : Good ε t) : ConjBound ε t` (`ConjBound.lean`) and
`LucasU.Conj.summable_psi (h : Good ε t) : Summable (fun N => psi ε t N)` (`Conjugate.lean`).
Axioms: `propext, Classical.choice, Quot.sound`. Mathlib `Lagrange` API only.

| File | Content | PROOF_U §4 / PROOF §4 step |
|---|---|---|
| `DivDiff.lean` | Unchanged copy: `E r K m = Σ_a r_a^m / F'(r_a)`, `E_base`, `E_succ`, `E_bound` (\|E\| ≤ (1−ρ)^{−K}), `coeff_divByMonic` | "Σ_a r_a^m/F′(r_a) = h_{m−K+1}(r)", partial fractions |
| `Conjugate.lean` | `wpar_conj` (w(ε/t) = w(t)⁻¹), nodes `rr ε t a = w^a` (`node_conj`, `F_conj`, `res_conj`), `psi_conj` (ψ_N(ε/t) = −ψ_N(t)), `summable_psi`, `S_add_Xi`, `two_conj_psi` (Γ(r_a) summands, same for both signs), `abs_nu_conj` (\|ν_j(ε/t)\| ≤ j(j+1)/(1−t), from \|α_j(ε/t)\| = t^{−1−2j}) | the σ-data list and Γ(r_a) |
| `Entry.lean` | `T ε t K k = mConst − Ξ·mLin` at ε/t; `T_eq`, `abs_Lpoly_le`, `partB_eq`, `abs_partB_le` | "T_k(−Ξ) = Σ h·σν + Σ γ_n h", \|T_k\| ≤ B_K |
| `ConjBound.lean` | `abs_T_le_pow` (\|T_k\| ≤ Dc(t)^K for k < 2K), `eval_Delta`, `abs_nrm_conj` (\|nrm\| = t^{K(K+1)}), `conjBound` | Hadamard step, \|w\|^{A_K K} = t^{K²(K+1)} |

Changes from FibZeta: the φ-specific bound |ν_j(−φ)| ≤ j(j+1)φ² became j(j+1)/(1−t); the constants
`BE`, `cB`, `Dc` are functions of t.

Numerical check of every identity used, for ε = ±1 and several t: `scripts/conj/check_conj.py` (mpmath).
