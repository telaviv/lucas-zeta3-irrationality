# LucasU/Cost — Proposition 3.6 (`CostBound ε t`)

`LucasU.Cost.costBound {ε : ℤ} {t : ℝ} (h : Good ε t) : CostBound ε t`, with
C = 6610008 · log t⁻¹ + 840. Axioms: `propext, Classical.choice, Quot.sound`.

Generalised from `lean_fibzeta/FibZeta/Cost` (the case ε = −1, t = φ⁻¹). Same elementary route: cubic constant
4393/3675 = 1.19537… ≤ 121/100 for **both** signs, because the two root counts it uses are sign-free.

| File | Contents | PROOF_U / PROOF step |
|---|---|---|
| `Cyclo.lean` | `log_norm_cyc_le`: log\|Φ_d(t)\| + log\|Φ_d(ε/t)\| ≤ φ(d) log t⁻¹ + 12, uniform in ε = ±1, 0 < t ≤ φ⁻¹ (Möbius inversion; G(n) = log(1−tⁿ) + log\|1−(εt)ⁿ\|, \|G(n)\| ≤ 6tⁿ as t ≤ 2/3) | Lemma 3.5 (PROOF_U §3.3: \|F(d)\| ≤ 2E₁(t) ≤ 12) |
| `Cluster.lean` | unchanged: cluster cost bounds, `Wc_bound` | Prop 3.6, W part |
| `RootCount.lean` | `sum_totient_eW_le`: Σ_{e(d)=e} φ(d) ≤ 2φ(e) (square roots of εω); `sum_totient_alpha_le`: Σ_{α_j(ζ_d)=1} φ(d) ≤ 2j+1 (roots of X^{2j+1} = ε^{j+1}); `card_eW_fiber_le`: ≤ 8 orders d per e; all with `hε : ε = 1 ∨ ε = -1` | §3.1, Lemma 3.1′ root types |
| `Sieve.lean` | unchanged: sieve at 2, 3, 5, 7, `T1_le`, `T2_le` | Prop 3.6 (totient averages) |
| `CostBound.lean` | `log_norm_CK_eq`, `sum_totient_nExp_le` (≤ 1.21K³ + 6610008K²), `sum_nExp_le` (≤ 70K²(1+log K)), `costBound` | Prop 3.6 |

For ε = +1 the true α-part is smaller (odd d, k_min = (d−1)/2; asymptotically 8/(3π²) vs 80/(27π²)), but the crude
bound Σ_j (K−1−j)(2j+1) ≤ K³/3 already suffices. Exact check of all counts for both signs:
`scripts/cost/check_cost_eps.py` (K ≤ 120: total/K³ = 1.0895 for ε = +1, 1.1191 for ε = −1).
