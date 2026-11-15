# LucasU/Analytic

Generalises `lean_fibzeta/FibZeta/Analytic` from `t = φ⁻¹`, `w = −t²`, `ρ = −t` to `w = εt²`, `ρ = εt`,
`ε = ±1`, any `0 < t ≤ φ⁻¹`. The hypothesis `Good ε t` is carried as an instance `[Fact (Good ε t)]`.

| Lean | file | written proof |
|---|---|---|
| `entryIdentity (h : Good ε t) : EntryIdentity ε t` | `All.lean` (via `Entry.hasL_fraction_DK`) | PROOF_U §1 Lemma 1 + partial fractions (PROOF §1) |
| `decayBound (h : Good ε t) : DecayBound ε t`, constant 4096 | `All.lean` (via `Decay.decayBound_of_fact`) | PROOF_U §2 Prop 2 (PROOF §2) |
| `hasL_pow`, `hasL_simplePole` | `Functional.lean` | Lemma 1(i), (ii); uses `ρw = ε²t³ = t³` |
| `Delta_eval_eq_det` | `Gram.lean` | Δ_K(Ξ) is the real Gram determinant |
| `det_tripleRootGram`, `abs_det_le_of_scaled_entries` | `Basis.lean` | triple-root basis B_j |
| `rationalWeight_euler_bounds` | `Weight.lean` | bounds on W = 1/D_K, θW, θ²W for \|q\| ≤ 1/2 |
| `tripleRoot_jets_common` | `Jets.lean` | jets of B_j at the nodes |

Where FibZeta used the golden ratio:
* `t < 1` (`t_lt_one`) replaces `tR < 1`;
* `t² ≤ 1/2` (`t_sq_le_half`, from `t φ ≤ 1` and `φ² = φ + 1`) replaces `tR² = 1 − tR ≤ 1/2`;
* `|w| = t²`, `|ρ| = t` (`abs_w`, `abs_rho`, from `ε² = 1`) replace `|−t²| = t²`, `|−t| = t`.
`Weight.lean`, `Jets.lean` and the algebraic part of `Basis.lean` do not depend on `t` and are unchanged.
