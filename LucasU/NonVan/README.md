# LucasU/NonVan — Proposition 5 (nonvanishing)

Main result (`LucasU/NonVan/Nonvanishing.lean`):

* `LucasU.NonVan.nonvanishing {ε : ℤ} {t : ℝ} (h : Good ε t) : Nonvanishing ε t`.

No added hypothesis. `EntryIdentity` is not used. Axioms: `propext, Classical.choice, Quot.sound`.

Generalised from `lean_fibzeta/FibZeta/NonVan/` (fixed `tR = φ⁻¹`, `w = −t²`, `ρ = −t`) to `w = ε t²`,
`ρ = ε t`. From `Good ε t` the proof uses only `0 < t`, `t < 1` (from `t ≤ φ⁻¹ < 1`) and `ε² = 1`
(`t_pos`, `t_lt_one`, `eps_sq`, `abs_eps` in `Cauchy.lean`). The identities that change are
`|w| = t²`, `|ρ| = t`, `ρⁿwⁿ = t^{3n}`, `w² = t⁴` (so the poles `w^{2j+2}` are positive for both signs).

## Map to PROOF §5 / PROOF_U §5

| PROOF §5 step | Lean |
|---|---|
| `Δ_n(Ξ) = 0` gives a kernel polynomial `Q_n ≠ 0`, `deg < n` | `Delta_eval` (Interp), `exists_orthogonal_polynomial` (Algebra) |
| `𝓕(z) = Σ ρⁿ 2wⁿz/(z−wⁿ)³`, analytic at ∞, `= Σ ν_k z^{−k−1}` | `cauchyF`, `cauchyF_inv_eq`, `meromorphicAt_cauchyF_inv` (Cauchy) |
| `E_n = 𝓕Q_n − T_n = O(1/z)` | `cauchyPart`, `tendsto_cauchyPart_error` (Interp) |
| `E_n(x_a) = 0`, `1 ≤ a ≤ n`, at `x_a = w^{−a}` | `cauchyF_node` (Cauchy), `Ln_cofactor_mul`, `cauchyPart_interpolates` (Interp) |
| cubic poles at `wⁿ`; `𝓕` not rational | `cauchyF_cubic_pole`, `meromorphicOn_cauchyF_pos`, `cauchyF_nonrational` (Pole) |
| normality: one reduced `T/Q`, too many zeros of `U_n` | `frequently_nonsingular_of_meromorphic_nonrational` (Algebra, unchanged) |

Files: `Algebra.lean` (normality argument, generic, unchanged apart from the namespace), `Cauchy.lean`,
`Pole.lean`, `Interp.lean`, `Nonvanishing.lean`. Numerical check: `scripts/nonvan/check.py` (node values
`𝓕(w^{−a}) = 2t^a(Ξ − S_a)`, `𝓕(1/u) = u Σ ν_k u^k`, and `Δ_K(Ξ) ≠ 0` for `K ≤ 5`, at `ε = ±1`,
`t ∈ {φ⁻¹, 0.4, 0.1}`).
