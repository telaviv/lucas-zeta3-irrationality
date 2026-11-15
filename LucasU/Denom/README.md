# LucasU/Denom — Proposition 3.4 (`Integrality ε`, both signs)

Main theorem: `LucasU.Denom.integrality {ε : ℤ} (hε : ε = 1 ∨ ε = -1) : Integrality ε`
(file `Integrality.lean`). `#print axioms`: `propext, Classical.choice, Quot.sound`.

Generalised file by file from `lean_fibzeta/FibZeta/Denom` (the case ε = −1): `-τ ^ 2` became
`wpar ε τ = ε τ²`, `-τ` became `ε τ`. The sign enters only through
`(ε : 𝕜)² = 1` (`eps_cast_sq`, `wpar_inv : (ε τ²)⁻¹ = ε (τ⁻¹)²`, `wpar_ne_zero`), threaded as
`hε` (and as the field `sign` of `LocalizationData R ε τ K`). The root types at a primitive `d`-th
root enter only through `orderOf (wpar ε ω) = eW ε d` and the α-root predicate, both transported
from `zetaC d` by `LucasU.Roots` (`orderOf_w_of_primitive`, `alpha_eq_one_iff_of_primitive`). The
local argument (Newton cluster basis, weights, rank correction with `k₀ = k_min(d)`) is
sign-independent, as in PROOF_U §3: no file uses the explicit value of `e(d)` or `k_min(d)`.

| File | Content | PROOF / PROOF_U |
|---|---|---|
| `Localization.lean` | sign lemmas; `LocalizationData R ε τ K` (inverses of `τ`, `1 − wⁿ` (n ≤ K), `1 − α_k` (1 ≤ k ≤ K−2)); `Delta_coeff_mem` | Lemma 3.1 |
| `Specialization.lean` | `Maps`, `maps_Delta`, `specialize_Delta_coeff`, `map_Delta` | §1 "Formal parameter" |
| `Local.lean` | local ring `regularAt ω ⊂ RatFunc 𝕜`, uniformizer `X − ω`, `localEval` | §3.1 "Local setting" |
| `Descent.lean` | integer monic fractions (`1 − wⁿ = −εⁿ(X²ⁿ − εⁿ)`, `1 − α_k = −ε^{k+1}(X^{2k+1} − ε^{k+1})`), Gauss and pole descent; `integrality_of_local_bounds : LocalBounds ε ℂ → Integrality ε` | Prop 3.4 |
| `Gram.lean` | `momentPolynomial = L_X(f/F)`, `properPart`, Gram congruence `det_normalizedGram` | Prop 3.2 (change of basis) |
| `LocalDet.lean` | weighted determinants, rank correction | Prop 3.2 (scaling; α bullet) |
| `Framework.lean` | `π ν_l` regular (fact (c)), `poly_part_split`, `local_bound_of_basis` | Prop 3.2 / Lemma 3.3 |
| `Nodes.lean` | node collisions simple (fact (a)), `π³ S_a` regular (fact (b)), `F'(x_a)` cleared, `proper_term_coeff_mem` | §3.1 facts (a),(b),(d) |
| `Monomial.lean` | `local_bound_monomial` (e > K) | Lemma 3.3 |
| `Clusters.lean` | classes, `clusterSize = clMult`, weights, `sum_weights = c(m)/c′(m)` | Prop 3.2 (iv) |
| `ClusterBasis.lean` | CRT linear independence | Prop 3.2 |
| `Newton.lean` | Newton cluster basis, unit change-of-basis determinant | Prop 3.2 |
| `NewtonLocal.lean` | `newton_term_mem`, `local_bound_cluster` | Prop 3.2 |
| `Integrality.lean` | choice of `k₀`, `nW = ∑ costs`, `localBounds hε`, `integrality hε` | Prop 3.4, PROOF_U Lemma 3.1′ |

Exact check of the frozen statement for small K, both signs: `scripts/denom/check_integrality.py`.

Adapted (with header attribution) from the uplift Lean (`qzeta_3-irrationality`, Apache-2.0), via
FibZeta: GenericMoments, GenericSpecialization, CyclotomicLocal, LocalEvaluation, IntegerFractions,
LocalPoleDescent, DenominatorDescent, GenericEvaluation, GenericGram, LocalDeterminants,
LocalGramBounds, PolynomialMomentRank, MovingClusterBasis, LocalClusterTransport, ClusterBasis.
