# lean_lucasu workers: shared rules (2026-11-15)

**Goal.** A Lean 4 + Mathlib (v4.35.0) proof of `LucasU.irrational_zetaU`: for every admissible (a, E), meaning
E = 1 with a ≥ 1, or E = −1 with a ≥ 3, the number Σ 1/U_n³ is irrational, where U_{n+1} = a U_n + E U_{n−1}. Only
standard axioms. The written proof is `C:\Users\Shawn Krisman\math\handoff\fibzeta\pell\PROOF_U.md`, a parametrised
version of `...\fibzeta\PROOF.md`; its referee report is `...\pell\REFEREE_U1.md`.

**This generalises a finished project.** `C:\Users\Shawn Krisman\math\lean_fibzeta` (`FibZeta`, ≈ 8500 lines, complete,
standard axioms) proves the Fibonacci case (a = 1, E = 1, i.e. ε = −1, t = 1/φ). Read its sources (read-only) at
`C:\Users\Shawn Krisman\math\lean_fibzeta\FibZeta\`; never edit anything in `lean_fibzeta`. **Your job is to generalise your area's proved FibZeta files from the fixed
`tR = φ⁻¹`, `w = −τ²`, `ρ = −τ` to a sign `ε ∈ {±1}` (`w = ε τ²`, `ρ = ε τ`) and a real `t` with `0 < t ≤ φ⁻¹`.**
Copy the files into your folder and edit them. Do not start from scratch.

## Architecture (fixed)
* **`LucasU/Defs.lean`.** All definitions, generic over a field with parameters `(ε : ℤ) (τ : 𝕜)`:
  - `wpar ε τ = ε τ²`, `alpha`, `nu`, `psi`, `S`, `node`, `F`, `Lpoly`, `res`, `mConst`, `mLin`, `nrm`, `hankelLin`,
    `hankelConst`, `Delta ε τ K`;
  - the real side as functions of `(ε, t)`: `XiR ε t`, `Lfun ε t`, `DK ε t K`;
  - `eW ε d`, `IsAlphaRoot ε d k`, `nAlpha`, `nW`, `nExp ε K d`, `CKpoly ε K`;
  - `Useq a E`, `zetaU a E`, `alphaR`, `tU`.
  For ε = −1 every definition coincides with FibZeta's (`(-τ^2)` became `wpar (-1) τ = ((-1 : ℤ) : 𝕜) * τ ^ 2`).
  `mConst` and `mLin` are unchanged, because w/ρ = τ for both signs. **Read it first. Never edit it.**
* **`LucasU/Statements.lean`.** The frozen ingredients. `Good ε t := (ε = 1 ∨ ε = −1) ∧ 0 < t ∧ t ≤ φ⁻¹`, then
  `DecayBound ε t`, `ConjBound ε t` (the conjugate point is `τ = ε/t`), `Integrality ε`, `CostBound ε t` (constant
  121/100, with `log t⁻¹` in place of `log φ`), `Nonvanishing ε t` and `EntryIdentity ε t`. **Never edit it.**
* **`LucasU/Roots.lean`.** Done. Root types depend only on the order, for both ε: `orderOf_w_of_primitive`,
  `alpha_eq_one_iff_of_primitive`.
* **`LucasU/Unit.lean`, `LucasU/Main.lean`.** Done, written by the coordinator. They contain the quadratic-unit algebra,
  Binet, `√D ∉ ℚ`, the norm argument, and `irrational_zetaU_of`, the assembly from the five ingredients at
  `ε = −E`, `t = tU a E`.

**Theorem each worker must prove**, with exactly this signature (put it in your folder's top file):

| worker | folder | theorem |
|---|---|---|
| analytic | `LucasU/Analytic/` | `theorem decayBound {ε : ℤ} {t : ℝ} (h : Good ε t) : DecayBound ε t` (and `entryIdentity (h : Good ε t) : EntryIdentity ε t`) |
| nonvan | `LucasU/NonVan/` | `theorem nonvanishing {ε : ℤ} {t : ℝ} (h : Good ε t) : Nonvanishing ε t` |
| conj | `LucasU/Conj/` | `theorem conjBound {ε : ℤ} {t : ℝ} (h : Good ε t) : ConjBound ε t` |
| denom | `LucasU/Denom/` | `theorem integrality {ε : ℤ} (hε : ε = 1 ∨ ε = -1) : Integrality ε` |
| cost | `LucasU/Cost/` | `theorem costBound {ε : ℤ} {t : ℝ} (h : Good ε t) : CostBound ε t` |

Namespace `LucasU.<Area>`. If a frozen statement is false or not provable as stated, **stop and report**; do not change it.

**Notes per area:**
* *analytic, nonvan, conj.* The FibZeta proofs used tR = φ⁻¹ numerically (for example tR < 0.62, 1 − tR² = tR). Replace
  each use by an inequality valid for all 0 < t ≤ φ⁻¹. Constants may depend on (ε, t), since the statements are
  `∃ C`. The nodes wⁿ alternate in sign for ε = −1 and are positive for ε = +1; the FibZeta arguments only used
  |wⁿ| = t^{2n}.
* *conj.* The conjugate point is `τ = ε/t`. The key identities are `psi ε (ε/t) N = −psi ε t N`,
  `wpar ε (ε/t) = (wpar ε t)⁻¹`, and α_k at ε/t equal to ε/α_k(t). They hold as identities of rational functions,
  for every t ≠ 0.
* *denom.* Purely formal in τ. ε = −1 is FibZeta's proof. For ε = +1 the root types are: e(d) = ord(ζ²), and α-roots
  only for odd d with k_min = (d−1)/2. The local arguments (Newton cluster basis, weights, rank) do not depend on the
  sign; see PROOF_U §3.
* *cost.* The bound must hold for both ε and all 0 < t ≤ φ⁻¹:
  - |log|Φ_d(t)| + log|Φ_d(ε/t)| − φ(d) log t⁻¹| ≤ 2E₁(t), with E₁ monotone in t;
  - the cubic constant 121/100 must cover both signs. FibZeta proved 4393/3675 for ε = −1. For ε = +1 the α-part
    is smaller: odd d only, k_min = (d−1)/2, constant 8/(3π²) against 80/(27π²).

## Reuse of the uplift Lean (Apache-2.0)
FibZeta already adapted `uplift-universal-inc/qzeta_3-irrationality` (clone at
`C:\Users\Shawn Krisman\math\handoff\fibzeta\ref\qzeta_3-irrationality\lean\`). **Keep every attribution header**
in files you copy from FibZeta. A file you adapt from FibZeta starts with
`Generalised from lean_fibzeta FibZeta/<Area>/<File>.lean (ε = ±1, general t).` and keeps its uplift line if it had one.

## Where you work
* Your own git worktree `C:\Users\Shawn Krisman\math\lean_lucasu_wt\<name>`, on branch `w-<name>`. Work only there;
  never touch `C:\Users\Shawn Krisman\math\lean_lucasu` (the main checkout) or another worker's worktree.
* `.lake/packages` in your worktree is a junction to `lean_chi2/.lake/packages` (Mathlib). Never delete it, never run
  `lake clean`, `lake update` or `lake exe cache get`, and never delete a worktree folder recursively.

## Building
* Single module: `LEAN_NUM_THREADS=4 lake build LucasU.<Area>.<File>`. For quick iteration use
  `lake env lean LucasU/<Area>/X.lean` once its imports are built. Mathlib is already built.
* Five workers share a 32 GB machine: run **one** Lean process at a time. Commands that may run longer than about
  2 min go in the background (`run_in_background`), and you wait for the notification. Never kill processes by name or
  guessed PID.
* Keep files small (≤ about 400 lines).

## Deliverable
* No `sorry`, `axiom`, `native_decide` or `implemented_by`. `decide +kernel` and `norm_num` are fine. Check
  `#print axioms` in a scratch file that you do not commit: the output must be only `propext, Classical.choice,
  Quot.sound`.
* Commit on your branch (`git add` only your files). The message ends with
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`. Never merge, rebase or push. Commit at every major
  milestone.
* Test new statements numerically (Python, exact arithmetic where a claim depends on it) before proving them. Put the
  scripts in `scripts/<area>/`.
* Leave a short `LucasU/<Area>/README.md` mapping your theorems to PROOF_U/PROOF steps.
* Final report (your last message): branch, commit hash, theorem names, files, any added hypothesis (there should be
  none), and build time.
