# Fidelity referee report: `LucasU` (2026-11-15)

Scope: whether the formal statements mean what they claim. Kernel checking was not redone, beyond one scratch file
(`scratch/fidelity/Check.lean`) that imports `LucasU.Final`, evaluates the definitions and re-prints the axioms.
Commit checked: `08c3fcf` (HEAD of `main`).

## Verdict: **PASS WITH FIXES**

`LucasU.irrational_zetaU` states exactly the claimed theorem. The corollaries state what their names say. The
assembly is a genuine derivation, and no hypothesis in it is vacuous. All the fixes below are about the paper's wording
or repository hygiene. None of them touches a Lean statement.

## Findings

**1. Top-level statement: exact (no issue).**
* `Useq a E`: U₀ = 0, U₁ = 1, U_{n+2} = a·U_{n+1} + E·U_n over ℤ, with a : ℕ cast to ℤ.
  - `#eval` gives Fibonacci for (1, 1), Pell 0,1,2,5,12,29,70,169 for (2, 1), F_{2n} for (3, −1) and F_{3n}/2 for (4, 1).
  - `Useq 1 1 n = Nat.fib n` was proved in scratch.
* `zetaU a E = ∑' n, 1/(U_{n+1})³`. The index starts at U₁, so U₀ = 0 is not in the sum, and the cast ℤ → ℝ is
  correct.
* A divergent `tsum` would be 0, which is rational, so the statement cannot hold for a degenerate reason. In any case
  `hasSum_zetaU` proves convergence, with the same axioms.
* No term is 1/0, since U_n ≥ 1 for n ≥ 1 under `Admissible`.
* `Admissible`: (E = 1 ∧ a ≥ 1) ∨ (E = −1 ∧ a ≥ 3). The degenerate cases (2, −1) (D = 0) and (0, 1) are rejected
  (checked in scratch).
* Sign convention: (a, E) = (P, −Q). `discr` = a² + 4E = P² − 4Q, and ε = −E = Q = N(α).
* Scope note (informational): a ranges over ℕ, so U_n(−P, Q) = (−1)^{n+1}U_n(P, Q) is not covered. That sequence
  gives an alternating sum. This matches the paper's normalisation η > 1, so it is not a defect.

**2. Corollaries: correct (no issue).**
* `pell = Useq 2 1`.
* `lucasNum` gives L₀..L₆ = 2, 1, 3, 4, 7, 11, 18 (`#eval`).
* `fib_mul_eq`: F_{kn} = F_k·U_n(L_k, (−1)^{k+1}). This is proved in general, and was also checked by `#eval` for
  k, n < 9.
* `admissible_fib_mul` covers k odd → E = 1 and k even → E = −1 with L_k ≥ 3.
* `irrational_fib_mul` (k ≥ 1) and `irrational_pell` have exactly the advertised statements.

**3. Frozen statements: faithful (no issue; one note).**
* `Defs.lean` and `Statements.lean` have not changed since the skeleton commit `6540870`.
* The definitions match PROOF_U §1 and the paper §2:
  - ν_k = k(k+1)α_k/(1 − α_k);
  - ψ_N = τ^{3N}/(1 − w^N)³;
  - L_X(1/(s − x_a)) = −2τ^a(X − S_a), which equals the paper's λ_a(X − S_a) on 1/(1 − w^a s) for every X;
  - `nrm` = (−1)^K w^{−A_K};
  - c(m) and c′(m) are written with truncated ℕ subtraction, which gives max(0, ·);
  - d ≤ 4K in `CKpoly`.
* `DecayBound`: t^{2b_K} = |w|^{2Σa_j}, which is the paper's exponent exactly.
* `ConjBound` is evaluated at τ = ε/t = σt and X = −Ξ.
* `Integrality`: one Laurent polynomial in τ for all real τ ≠ 0 that are not roots of unity. This is equivalent to
  C_KΔ ∈ ℤ[τ^{±1}][X].
* `CostBound`: constant 121/100, which exceeds c_* = 4393/3675 and κ_± < 1.131.
* `Nonvanishing`: Δ_K(Ξ) ≠ 0 for infinitely many K.
* Nothing is trivially satisfiable.
  - `Nonvanishing` rules out Δ ≡ 0, which would otherwise make Decay, Conj and Integrality trivial.
  - `CostBound` has a log|0| = 0 quirk, but it is harmless: C_K(t) ≠ 0 is proved (`aeval_CKpoly_ne_zero`), and the
    assembly derives P > 0 before it takes logs.
* Note: every analytic statement is ∃C with C depending on (ε, t), and the conjugate bound is in the form C^{K²}. These
  are weaker than the paper's uniform or explicit constants, but they are exactly what the assembly needs (see M2).

**4. Assembly: sound (no issue).**
* `irrational_zetaU_of` uses all five ingredients. The route is:
  - Ξ = u(t) and −Ξ = u(σt), with u(τ) = p(a + 2Eτ)/(bD²);
  - `Integrality` is applied at both points, with the same integer polynomial Q;
  - Q mod (τ² + aEτ − E) gives p + qτ, and its norm p² − aEpq − Eq² is an integer;
  - this norm is nonzero because √D ∉ ℚ (`discr_not_sq`, a correct square-sandwich argument);
  - the margin 11/9 − 121/100 = 11/900 comes from `bK_lower` (2b_K ≥ (2/9)(K³ − K)).
* This avoids any Galois-action formalisation, so it is cleaner than the paper's "σy_K".
* Binet (`Useq_binet`, `one_div_U_cube`) and t ≤ φ⁻¹ (`gold_le_alphaR`) are correct for both signs.

**5. `EntryIdentity` is not an assembly input (low).** It is used only inside `decayBound`. The paper's table lists it
on the same footing as the five ingredients (M3).

**6. Attribution headers (low).**
* Every QZeta3 ("uplift") line in a FibZeta file was carried into its LucasU counterpart. I checked all files: none
  was dropped.
* `NOTICE` records both kinds of reuse.
* However, three files lack the "Generalised from lean_fibzeta …" header that NOTICE and the paper promise:
  - `LucasU/Main.lean`: `bK_lower` and `eventually_log_sq_lt` are verbatim from `FibZeta/Main.lean`, and
    `norm_ne_zero` and the assembly are generalised from it;
  - `LucasU/Final.lean`;
  - `LucasU/Unit.lean`: `one_div_U_cube` comes from `one_div_fib_cube`.
* This is the same author's code, so there is no licence issue, but the claim "every adapted file says so" is false
  as written.

**7. Hygiene (low).**
* There is no `sorry`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque` or `admit` in
  `LucasU/`, `LucasU.lean` or `Axioms.lean`.
* The axioms were re-printed in scratch: [propext, Classical.choice, Quot.sound].
* `lake-manifest.json` is **untracked** in git. Commit it for reproducibility.
* `.lake/config` is not git-ignored.

**8. Trivia.**
* The docstring of `paper/check_lean_names.py` still says "from lean_fibzeta/". The script itself works: it checks 40
  tokens and finds 0 problems.
* There is no top-level README or TRUST file; only the area folders have READMEs.

## Paper (main.tex) versus Lean

Matches:
* Theorem name and signature.
* `Admissible`, `zetaU` and `Useq` as described, with (a, E) = (P, −Q).
* ε = Q = −E.
* The quadratic τ² + aEτ − E. Lemma 2.1(iii) gives τ² − PQτ + Q, which is the same polynomial.
* √D = P − 2Qt.
* The file names, and all 40 `\lean{}` names (checker).
* Lean and Mathlib v4.35.0.
* The axioms, and "no sorry/native_decide".
* The constant 121/100, and c_* < 121/100 < 11/9.
* The conjugate point ε/t.

Mismatches:
* **M1 (low).** The intro says the integrality statement is formalised "for an indeterminate parameter". The Lean
  statement is pointwise, for every real τ ≠ 0 that is not a root of unity, with one Laurent polynomial. It is
  equivalent, but it is not an indeterminate.
* **M2 (low).** Props 3.1 ("absolute implied constant"), 4.8 ("independent of (P, Q)") and 5.1 (explicit M_K) are
  stronger than the Lean statements, whose constants depend on (ε, t) and use the form C^{K²}. The §9 table pairs
  them without saying so. Add one sentence: uniformity is not formalised and is not needed.
* **M3 (low).** The table row "Lemma 2.2, entries → `EntryIdentity`" reads as an assembly ingredient. Say that it is
  used inside the proof of `decayBound`.
* **M4 (low).** Provenance says "every adapted file says so in its header". This is false for Main, Final and Unit with
  respect to lean_fibzeta (Finding 6). Fix the headers, or the wording.
* **M5 (trivial).** §9 says Statements.lean states the ingredients "for every ε = ±1 and every real t with
  0 < t ≤ φ⁻¹ (`Good`)". In fact `Integrality` is per ε, over all real non-roots of unity, and `Good` is a hypothesis of
  the proof theorems rather than part of the predicates.
* **M6 (suggestion).** Name `hasSum_zetaU` where §9 says "a separate lemma also shows that the series converges".
* **M7 (open).** `% TODO(owner): repository URL` is still pending.
