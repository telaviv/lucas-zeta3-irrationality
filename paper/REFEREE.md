# Referee report

**Paper:** "The reciprocal cube sums of Lucas sequences of quadratic units are irrational" (`paper/main.tex`, compiled
`paper/build/main.pdf`, 10 pp.). **Date:** 2026-11-15.

## Recommendation

**Minor revision.**

## Summary

The paper proves that Σ_{n≥1} U_n(P,Q)^{-3} is irrational for every admissible pair: Q = −1 with P ≥ 1, or Q = 1 with
P ≥ 3. This covers the Pell numbers and Σ F_{kn}^{-3} for every k. The method is the Hankel-determinant construction of
the author's Fibonacci paper [Kri26], now run with a sign Q and a general unit t = η^{-1} ∈ (0, φ^{-1}]. Four estimates
are combined:
- real decay of size −(2/9)K³ log η;
- conjugate smallness of size −K³ log η;
- a cyclotomic denominator cost ≤ c_*K³ log η, with c_* = 4393/3675 < 11/9;
- nonvanishing for infinitely many K.

I checked every lemma and proposition line by line, compared each deferral to [Kri26] against that paper's text, and
tested the key claims by computer (list at the end).

**I found no mathematical error in the proof of the theorem.**
- The local denominator bounds hold exactly for both signs: no violation for Q = 1, K ≤ 10, or for Q = −1, K ≤ 9.
- The root-type tables, the totient identity, the cluster inequality, c_*, the conjugate bound and the decay rate all
  check out.
- The deferrals to [Kri26] (Propositions 4.2, 4.6, 6.1) are legitimate. The cited proofs use only the properties
  claimed, and the present paper repeats them anyway.

There is one factual error, in a remark that the proof does not use. The finite-K numbers in the closing remark of §7
were computed with the true denominators, not with C_K(t) as the remark says. There is also one imprecise uniformity
claim (Proposition 4.6). The rest is exposition: notation clashes, a few compressed steps, and some literature wording.

The added content over [Kri26] is modest: a sign, a general unit, and the classification of the roots for Q = 1. Much
of the text is reused nearly verbatim from [Kri26]. The editor may want this disclosed, or the two papers merged (point
14). That is an editorial matter, not a correctness one.

## Numbered points

### Mathematics

1. **(minor; factual error) Closing remark of §7 (lines 493–498).**
   - *What the remark says.* "The left side above without the term 2K log(vD²), divided by K³ log η, is about −0.17 for
     the Pell numbers at K = 20–25 and about −0.21 for (3,1) at K = 20." The left side contains log|N C_K(t)|, with C_K
     as defined in Proposition 4.4, i.e. built from the proved bounds b_{K,d}.
   - *What I computed with that C_K.* I recomputed the left side (mpmath at 3000–5000 digits, stable between two
     precisions):

     | case | K | log\|N C_K\| | log\|Δ_K(Ξ)\| | log\|σΔ_K(−Ξ)\| | total |
     |---|---|---|---|---|---|
     | Pell | 20 | 1.1909 | −0.2611 | −1.0511 | **−0.121** |
     | Pell | 25 | 1.1781 | −0.2537 | −1.0407 | **−0.116** |
     | (3,1) | 20 | 1.1776 | −0.2658 | −1.0532 | **−0.141** |

     (All values are divided by K³ log η.)
   - *Where the paper's numbers come from.* The Δ and σΔ columns agree to four digits with the author's notes
     (`handoff/fibzeta/pell/AUDIT.md` §4, `PROOF_U.md` §8). But there the "budget" uses Nc = −log N(content ideal), the
     *true* denominators (Nc ≈ 1.13 for Pell at K = 20, 1.124 at K = 25). That is where −0.17/−0.18 and −0.21 come
     from.
   - *Fix.* Either say "with the true denominator (the norm of the content ideal of Δ_K) in place of C_K(t)", or quote
     −0.12 (Pell) and −0.14 ((3,1)).
   - *Consistency check.* The analogous number in [Kri26] (−0.12 for the Fibonacci numbers) does use C_K: I get −0.124
     at K = 12. As written, the two papers' remarks therefore measure different things.

2. **(minor) Proposition 4.6, uniformity claim (line 371).**
   - *The problem.* The proof gives log|N C_K(t)| ≤ log η·(c_*K³ + O(K²)) + 2𝓔₁·O(K² log K). The O(K²)·log η part is
     not bounded by a (P,Q)-independent O(K² log K) as η → ∞. So "with an implied constant independent of (P,Q)" is
     false as literally stated.
   - *Fix.* State the bound as (c_*K³ + O(K² log K)) log η with an absolute constant (use log η ≥ log φ). This is what
     the abstract's "measured in units of log η" means.
   - *Not affected.* Propositions 3.1 and 5.1 are genuinely uniform as stated.

3. **(minor) Proposition 4.6, unproved auxiliary claims.**
   - (a) "Σ_d b_{K,d} = O(K² log K)" is asserted without justification. [Kri26] gives a one-line argument. Add it,
     noting that for Q = 1 at most two d have e(d) = e (d = e for e odd, and d = 2e).
   - (b) The averaging lemma |Σ g f − β∫f| ≤ 2P₀(M+V) is stated without proof. [Kri26] gives a three-line proof.
     Since §1 says "the present paper is self-contained", restore it.
   - (c) The lemma is phrased with the specific function g₇ as its generic function. Use a neutral name (g, β, period
     p) and avoid P₀, which is already the partial-fraction numerator of §2.

4. **(minor) Introduction vs Proposition 4.6 on the α-count.**
   - Line 120–121 says "only the classification of the roots and the count of the α-roots change". The proof of
     Proposition 4.6 (line 397) uses an α-count that is identical for both signs: #{ζ : α_j(ζ) = 1} = 2j + 1. I
     verified this for j < 60, both signs.
   - Only the exact k_min changes, and that matters only for the sharp constant of Remark 4.7.
   - Reword the introduction.

5. **(minor) Lemma 4.3, proof (line 340).** It cites (a)–(d), but (a) is stated under the hypothesis e(d) ≤ K. Add the
   sentence from [Kri26]: since |b − a| < K < e, no factor 1 − w^{b−a} and no 1 − w^N (N ≤ K) vanishes at ζ.

6. **(minor) Proposition 4.2, compressed steps.** Compared with [Kri26] the following were dropped or left implicit.
   Each is correct, but should be restored:
   - (i) the definition of A^pol: it collects ϖ^{-1}(u_k − u_k(0))[s^k](·)₊ for k ∈ P_α and ν_k[s^k](·)₊ for
     k ∉ P_α;
   - (ii) the fact that ⌈κ⌉ + ⌊κ⌋ = 2κ because κ_j ∈ ½ℤ, which is needed for "total scaling 2Σκ_j";
   - (iii) the reason rank B′ = rank B: the scalings are invertible over the fraction field;
   - (iv) the terms "α-root" and "pure W-root", which are used without definition;
   - (v) P_α should be {1 ≤ k ≤ K−2 : α_k(ζ) = 1}. For Q = 1, d = 1 one has α₀(1) = 1, which is harmless because
     ν₀ ≡ 0, but as written k = 0 is included.

7. **(minor) Proposition 5.1, omitted formulas.**
   - The bound |γ_n| ≤ n(n+1)t^{2n+1}/(1−t³) is given without the formula γ_n = n(n+1)Σ_M t^{3M}w^{M(n−1)} that yields
     it.
   - The partial-fraction expansion of s^k/F^σ is used but not displayed.
   - Both are one line in [Kri26]; restore them. I re-derived both.

### Exposition and notation

8. **(minor) §6, notation clash.**
   - The auxiliary polynomials are called Q₁ and Q₂, the kernel polynomials Q_n, and the sign Q. "One reduced fraction
     T/Q₂" literally clashes with the kernel polynomial Q_n at n = 2, and Q₁ with Q_n at n = 1.
   - Rename, e.g. kernel polynomials R_n, generic polynomial R, reduced fraction T/R₀.
   - Also, V (line 468) reuses the name of the V_j of §3. Harmless.

9. **(typo/notation) Overloaded symbols.**
   - v is the valuation ord_ϖ in §4 and the denominator of u/v in §7. It is also used in the introduction (line 116)
     before it is defined.
   - P is the Lucas parameter, and also P₀ (numerator, period), P₁, P^pol and P_α.
   - ε is the 0/1 indicator of Proposition 4.2, the small ε of §6, and the Lean sign ε = Q in §8.
   - E is the Lean sign and E_n, E in §6.
   - L_k (Lucas numbers) sits next to L, L_X (functionals).
   - Suggested fixes: q for the denominator in §7; 𝟙_α or δ_α for the indicator; ℓ_k or write "the k-th Lucas
     number"; p for the period.

10. **(minor) Introduction, line 101.** "Has rational moments": the moments ν_k lie in ℚ(√D) and are rational functions
    of t. Say so. Similarly, "pure simple-pole tails of Ξ" is jargon: say "L(1/(1−w^a s)) = λ_a(Ξ − S_a)".

### Formal verification section (§8 in the compiled paper)

11. **(minor) Consistency with the Lean files.** I checked §8 against `LucasU/Defs.lean`, `Statements.lean`,
    `Final.lean`, `Corollaries.lean` and `scripts/axioms.txt`.

    *These agree with the paper:*
    - the statement of `irrational_zetaU`;
    - `Admissible` (E = 1, a ≥ 1, or E = −1, a ≥ 3), `Useq`, `zetaU` and `pell = Useq 2 1`;
    - the dictionary (a,E) = (P,−Q);
    - the roots of τ² + aEτ − E;
    - the forms of `DecayBound`, `ConjBound`, `CostBound` (121/100) and `Integrality` (one integer polynomial for all
      real τ ≠ 0 that are not roots of unity);
    - the standard-axioms output;
    - `CKpoly` = ∏_{d≤4K} Φ_d^{nW+nAlpha}, with nW/nAlpha matching b_{K,d} (cW uses truncated subtraction, which
      equals 2·max(0, (m+2)/2 − j));
    - the name check `check_lean_names.py`: 56 tokens, 0 problems.

    *Points to fix:*
    - (a) Lines 554–556 say the uniformity in (P,Q) of Proposition 3.1 is "not formalised". But the decay proof gives
      C = 4096 for every Good ε t (`Analytic/All.lean`: "independent of (ε, t)"). Say that the *statement* does not
      express uniformity, while the proof's constant is in fact uniform.
    - (b) `fib_mul_eq` is stated with `Useq (lucasNum k) ((−1)^(k+1))`, i.e. E = (−1)^{k+1} = −Q. Worth one clause,
      since the text writes U_n(L_k, (−1)^k).
    - (c) The repository URL is a TODO (line 505). It must be filled in before submission. A line count, as given in
      [Kri26], would be useful.

### Introduction and literature (flags for the separate reference check; I did not verify sources)

12. **(minor) Scope of the cited results.**
    - (a) [AJ89] is cited only for Σ F_n^{-1}. Its title ("certaines suites récurrentes") suggests it covers general
      recurrences. Since this paper is about general U_n(P,Q), state what [AJ89] proves for Lucas sequences. Consider
      also citing the later work on Σ 1/U_n for general Lucas sequences (e.g. Bundschuh–Väänänen; Prévost, J. Number
      Theory 1998), if the reference check confirms them.
    - (b) Check that [DNNS97], a 3-page Proc. Japan Acad. note, really states the result "for the generalised Fibonacci
      sequences with Q = −1", rather than for F_n and L_n only, with the generalisation appearing in a later paper by
      the same authors.
    - (c) For Q = 1 the even-power sums (e.g. Σ F_{2n}^{-2s}) are also values of quasi-modular forms. The introduction
      mentions only Q = −1. Mention both signs, since the paper treats both.

13. **(minor) Wording.**
    - (a) "The odd powers of the full sums are not of this kind (see [Wal10])" overstates. Nobody has proved that they
      are not quasi-modular values. Write "are not known to be of this kind". Also check that [Wal10] discusses the
      Fibonacci zeta function at all.
    - (b) [Kri26] is the author's own unrefereed 2026 preprint. Give an arXiv identifier, and say "preprint" where the
      priority claim "we know of no irrationality result … before [Kri26]" is made.
    - (c) In [QZ3] the author field "Solomon Admasu, F." looks garbled.

14. **(editorial) Overlap with [Kri26].**
    - Sections 2–7 reproduce [Kri26] nearly verbatim, with t replaced by a general unit and −1 by Q.
    - Many journals require text recycling to be disclosed. Some editors will prefer one combined paper.
    - If the paper stays separate, it would help to put in the introduction a short table of exactly what changes. The
      introduction already does this in prose ("three changes").
    - Optionally, also note:
      - the immediate extension to Σ 1/U_{kn}³ (U_{kn} = U_k·U′_n);
      - that the alternating sums Σ(−1)^{n−1}U_n(P,−1)^{-3} = Σ U_n(−P,−1)^{-3} are not covered by the normalisation
        η > 1.

## Checks run

All scripts are in `paper/referee_scratch/`.

| # | Claim | Script | Result |
|---|---|---|---|
| 1 | Root types e(d), k_min(d) for both signs (§4.1 table) | `check_elementary.py` | Exact exponent arithmetic, d < 400, both signs: 0 mismatches |
| 2 | Σ_{e(d)=e} φ(d) = 2φ(e); #{ζ : α_j(ζ) = 1} = 2j+1 for both signs | `check_elementary.py` | True for e < 150 and j < 60 |
| 3 | c(1) = 0, c′(1) = 3, c(m) = 4(m−1) for m ≤ 6, c(m) ≤ (m+3)²/4, 0 ≤ c′ − c ≤ 3, 0 ≤ δ(m) ≤ max(0,m−5)²/4 | `check_elementary.py` | m < 300: all true |
| 4 | Cluster inequality Σc(m_r) + c′(m_e) ≤ 4(K−e) + max(0,K−4e)²/(4e) + 3 | `check_elementary.py` | All K < 120, e ≤ K: true |
| 5 | 2Σ_{j<K} a_j = (K³+3K²−ι_K)/9 | `check_elementary.py` | K < 300: true |
| 6 | β₇ = 768/1225 = mean of g₇; ∫f_K = (11/8)K³ + O(K²); c_* = 4393/3675 = 1.195374; c_* − 11/9 = −0.026848; c_* < 121/100 < 11/9 | `check_elementary.py` | All exact |
| 7 | 𝓔₁ = 2.11360…, C₀ = 2.0770906…, 2t³/(1−t²)³ = 2 and 1/(1−t³) = φ²/2 at t = φ^{-1} | `check_elementary.py` | Confirmed |
| 8 | Remark 4.7 constants: 1.130790 (Q = −1), 1.100769 (Q = 1), margins 0.0914 and 0.1214; Q = 1 odd-d α part → 8/(3π²) | `check_elementary.py` | Confirmed (α part /K³ = 0.2695 at K = 600 vs 0.2702) |
| 8′ | I = ∫₀¹ xℓ(x)dx | `check_I.py` | I ∈ [0.683060, 0.683122] ⊂ stated interval |
| 9 | **Integrality and local bounds:** exact Δ_{K,τ}(X) over ℚ(τ), cyclotomic multiplicities vs b_{K,d}, and C_K·Δ ∈ ℤ[τ^{±1}] | `check_local_bounds.py` | Q = 1, K = 2..10, and Q = −1, K = 2..9: **no violation**. C_K·Δ has integer Laurent coefficients in every case. Equality in most d (e.g. 14/19 at K = 10, Q = 1) |
| 10 | Binet / (1.1): Σ U_n^{-3} = D√D Ξ for (P,Q) = (1,−1), (2,−1), (3,1), (4,−1), (7,1), (10,−1) | `check_analytic.py` | Agreement to 600 digits |
| 11 | Lemma 2.3 + partial fractions: L(s^k/D_K) by direct summation of θ(θ+1) at the nodes vs ν_k, λ_a(Ξ−S_a) | `check_analytic.py` | K = 3, same six pairs: error < 10^{-50} |
| 12 | Proposition 3.1: (log\|Δ_K(Ξ)\| − main term)/K² | `check_analytic.py` | K = 4..12, six pairs: bounded (between −0.72 and +0.27), consistent with an absolute O(K²) |
| 13 | Proposition 5.1 with the explicit M_K | `check_analytic.py` | Holds in all 30 cases |
| 14 | Closing remark of §7 | `check_finiteK.py` | See point 1. Totals with C_K: −0.121 / −0.116 (Pell, K = 20/25), −0.141 ((3,1), K = 20). Fibonacci K = 12: −0.124, matching [Kri26] |
| 15 | Lean consistency | `check_lean_names.py` (author's) + manual reading of Defs/Statements/Final/Corollaries/axioms | Consistent (point 11) |
| 16 | Build | — | No undefined references or citations. Kri26 cross-references (Props 4.2, 4.6, 6.1) match the labels in `lean_fibzeta/paper/build/main.aux`. Two harmless bibtex warnings (no pages for article-number entries) |

### Manual verifications, beyond the scripts

- **Lemma 2.1 (i)–(v).**
- **Moments.** The θ(θ+1)(1−cs)^{-1} computation.
- **Real decay.** Every inequality, with constants uniform for t ≤ φ^{-1}; the signs of the nodes play no role.
- **Lemma 4.1.**
- **Proposition 4.2.** The Newton basis, the residue valuations j + k − (m−1), the cases (A)/(B), the weights, and the
  rank argument.
- **Lemma 4.3 and Proposition 4.4.** Including t, σt ∈ ℤ[η]^× and the Gauss-lemma step.
- **Lemma 4.5.** Monotonicity in η.
- **Proposition 4.6.** Both parts.
- **Proposition 5.1.** The conjugate data at τ = Q/t, (−1)^{K²}w^{A_K K}, Γ(r_a) via t^{4a} = r_a², the h_m and γ_n
  bounds, monotonicity in t.
- **Proposition 6.1.** The full interpolation argument.
- **Final assembly.** Ξ = u(P − 2Qt)/(vD²), y_K ∈ ℤ[η], and the norm in ℤ without maximality.
