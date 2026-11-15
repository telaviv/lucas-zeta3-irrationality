# Reference check for `main.tex` / `refs.bib` (2026-11-15)

Scope: all 15 entries in `refs.bib`, every citing sentence in `main.tex` (lines 82–90, 97–100, 601–602, and the
`\cite{Kri26}` cross-references), and the referee's points 12–13 in `REFEREE.md`. `main.tex` and `refs.bib` were not
edited.

What "verified in" means below:
* **source**: I read the statement in the work itself (full text, a local copy, or the repository files).
* **abstract**: an arXiv or publisher abstract by the authors.
* **secondary**: a zbMATH review, or a citing paper or survey (named in each case).

zbMATH records were read through the zbMATH Open API (`api.zbmath.org`). The web URLs given (`zbmath.org/?q=an:…`) are
the same records. Bibliographic data were cross-checked against Crossref (`api.crossref.org/works/<DOI>`).

## 1. Summary table

| Key | Exists | Verification source | Details | Claim supported? |
|---|---|---|---|---|
| AJ89 | yes | zbMATH [Zbl 0682.10025](https://zbmath.org/?q=an:0682.10025): C. R. Acad. Sci. Paris Sér. I 308, no. 19, 539–541 (1989). Same citation in Meher–Sahoo, INTEGERS 24 (2024) #A85 (local `lit/Integers_y85.txt`, ref. [1]). | Correct (could add `number = {19}`). | **Partly.** True, but understated: the paper proves much more than Σ1/F_n (see (a)). Checked in the zbMATH review (secondary); no full text available (no Gallica or Numdam copy found). |
| DNNS97 | yes | DOI [10.3792/pjaa.73.140](https://doi.org/10.3792/pjaa.73.140) (Crossref: vol. 73, no. 7, pp. 140–142, 1997); zbMATH [Zbl 0902.11029](https://zbmath.org/?q=an:0902.11029) (review by P. Bundschuh); restated in ESS, RIMS Kôkyûroku 1665 (2009), §1 (local `lit/kokyuroku_1665-16.txt`). | Correct. Journal abbreviation better as "Proc. Japan Acad. Ser. A Math. Sci."; add `number = {7}`. | **Partly.** Correct for Q = −1, but the paper also covers Q = +1 (Σ U_n^{-2s} and Σ V_n^{-s}), which our text omits (see (b), (c)). Checked in the zbMATH review and the ESS survey (secondary); the Project Euclid full text would not load. |
| ESS07 | yes | DOI [10.4064/aa130-1-3](https://doi.org/10.4064/aa130-1-3); zbMATH [Zbl 1132.11036](https://zbmath.org/?q=an:1132.11036): Acta Arith. 130, no. 1, 37–60 (2007). | Correct. | **Yes, for Q = −1.** For algebraic α, \|α\| > 1, β = −1/α: Φ₂, Φ₄, Φ₆ are algebraically independent and every Φ_{2s} is a rational function of them. Checked in the zbMATH review and in the ESS RIMS 2007 abstract (local `lit/ESS_rims07_abstract.txt`, Thm 1). |
| ESS08 | yes | DOI [10.1007/s11139-007-9019-7](https://doi.org/10.1007/s11139-007-9019-7); zbMATH [Zbl 1233.11081](https://zbmath.org/?q=an:1233.11081): Ramanujan J. 17, no. 3, 429–446 (2008). | Correct. | **Yes** (odd-index sums Σ U_{2n−1}^{-p}, αβ = −1). Checked in the authors' own survey, Kôkyûroku 1665, Thms 3.1–3.3 (local file; secondary, same authors). |
| Kra21 | yes | [arXiv:2103.03969](https://arxiv.org/abs/2103.03969) (C. Krattenthaler, 5 Mar 2021). No journal reference on arXiv or on the author's page [mat.univie.ac.at/~kratt/artikel/uvarov.html](https://mat.univie.ac.at/~kratt/artikel/uvarov.html). | Correct (still a preprint). | **Yes.** It proves Hankel determinants of moments for densities related by a rational factor, with Uvarov's formula as a corollary. Checked in the abstract. |
| Nes96 | yes | DOI [10.1070/SM1996v187n09ABEH000158](https://doi.org/10.1070/SM1996v187n09ABEH000158); zbMATH [Zbl 0898.11031](https://zbmath.org/?q=an:0898.11031): Sb. Math. 187, no. 9, 1319–1348 (1996), translated from Mat. Sb. 187, no. 9, 65–96. | Correct (could add `number = {9}`). | **Yes.** At least three of q, P(q), Q(q), R(q) are algebraically independent. Checked in the zbMATH review. The use for Fibonacci-type sums is confirmed in Wal10 §3.4 and ESS Kôkyûroku 1665 §1 (local files, source). |
| Pre96 | yes | DOI [10.1016/0377-0427(95)00019-4](https://doi.org/10.1016/0377-0427(95)00019-4); zbMATH [Zbl 0855.11037](https://zbmath.org/?q=an:0855.11037): J. Comput. Appl. Math. 67, no. 2, 219–235 (1996). | Correct. | **Yes**, for the loose "in the line of" claim: Padé approximants to the remainder of ζ(s), which recover Apéry's approximations. Checked in the zbMATH review. |
| QZ3 | yes | Repository file [`lean/CITATION.cff`](https://github.com/uplift-universal-inc/qzeta_3-irrationality/blob/d12d56f/lean/CITATION.cff) (local clone `handoff/fibzeta/ref/qzeta_3-irrationality/lean/CITATION.cff`, commit d12d56f). | Title, version 0.1.0, date 2026-10-11 and Apache-2.0 are correct. The author is correct as an initial, but the full given name is better (see (f)). | **Yes.** It is the Lean development inside UPL, Apache-2.0. Checked in the source (repository files). |
| UPL | yes | Repository [uplift-universal-inc/qzeta_3-irrationality](https://github.com/uplift-universal-inc/qzeta_3-irrationality): public (GitHub API), created 2026-10-12; commit d12d56f exists (API 200). `CITATION.cff`: author "uplift-universal-inc", version "0.3.0-two-proofs", released 2026-10-12. | Correct. | **Yes.** The README states the result for Σ n²/(pⁿ−1), every integer p ≥ 2, and lists "External expert review / publication: Not yet established". `docs/ATTRIBUTION.md` discloses substantial AI assistance. Checked in the source. |
| Uva69 | yes | DOI [10.1016/0041-5553(69)90124-4](https://doi.org/10.1016/0041-5553(69)90124-4) (Crossref): USSR Comput. Math. Math. Phys. 9, no. 6, 25–36 (1969). Original: Zh. Vychisl. Mat. Mat. Fiz. 9 (1969), 1253–1262 (zbMATH [Zbl 0191.36702](https://zbmath.org/?q=an:0191.36702)). | **Title wrong in one word.** The official title is "…systems of polynomials orthogonal with respect to…" (no "that are"). | **Yes** (rationally modified orthogonality measures). Checked only from the title and from Kra21's abstract (secondary). |
| Wal10 | yes | RIMS Kôkyûroku 1710 (2010), 166–179: [PDF](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1710-18.pdf) (local `lit/kokyuroku_1710-18.pdf`; the header reads "1710 2010 166-179"). | Correct. | **No, as currently cited.** §3.4 (pp. 172–173) defines ζ_F(s) and states ESS's theorem that ζ_F(2), ζ_F(4), ζ_F(6) are algebraically independent, as a consequence of Nesterenko's theorem. It says **nothing** about odd values. So it cannot support "The odd powers … are not of this kind". Checked in the source. See (d). |
| Zud16 | yes | DOI [10.1007/s40993-016-0042-x](https://doi.org/10.1007/s40993-016-0042-x); [arXiv:1601.02688](https://arxiv.org/abs/1601.02688); zbMATH 1415.11099: Res. Number Theory 2 (2016), Paper No. 15, 10 pp. | Correct. | **Yes.** It proves irrationality of ℓ_p(x,z) using Hankel determinants built on Padé approximations. Checked in the abstract. |
| Zud17 | yes | DOI [10.1007/s00365-016-9333-7](https://doi.org/10.1007/s00365-016-9333-7); [arXiv:1507.05697](https://arxiv.org/abs/1507.05697); zbMATH 1367.11062: Constr. Approx. 45, no. 2, 301–310 (2017). | Correct. | **Yes** (a determinantal extension of the irrationality criterion, with Hankel and Vandermonde determinants). Checked in the abstract and the zbMATH review. |
| Kri26 | **not publicly available** | arXiv API title search (exact title, and "reciprocal cubes" AND "Fibonacci"): no hits. Web search on the exact title: no hits. Zenodo and HAL title search: 0 hits. GitHub `telaviv/fibonacci-zeta3-irrationality`: **HTTP 404 without authentication**. The authenticated API shows the repository exists but is **private** (created 2026-11-15). | Title matches `lean_fibzeta/paper/main.tex`. It has no identifier, and the Lean URL is not public. | The deferrals to Props 4.2, 4.6 and 6.1 were checked by the referee against `lean_fibzeta/paper` (REFEREE.md, row 16). Not re-checked here. |
| XW13 | yes | DOI [10.1186/1687-1847-2013-184](https://doi.org/10.1186/1687-1847-2013-184); zbMATH 1390.11043. Full text (open access) read. | Authors correct: **Zhefeng Xu and Tingting Wang** (Northwest University, Xi'an). Adv. Difference Equ. **2013**, Paper No. 184, 10 pp. Add `volume = {2013}` to silence the bibtex warning. | **Yes.** The main theorem evaluates ⌊(Σ_{k≥n} 1/P_k³)^{−1}⌋ explicitly in terms of P_n, P_{n−1}, separately for n even and n odd. Checked in the source. |

All 15 bib entries are cited, and every `\cite` key has an entry (see (h)).

## 2. Corrected / improved BibTeX

Only entries that change are listed. `ESS12` is new, needed for the Q = 1 sentence (see (c)). `Pre98` is optional (see (a)).

```bibtex
@article{AJ89,
  author  = {Andr{\'e}-Jeannin, R.},
  title   = {Irrationalit{\'e} de la somme des inverses de certaines suites r{\'e}currentes},
  journal = {C. R. Acad. Sci. Paris S{\'e}r. I Math.},
  volume  = {308},
  number  = {19},
  year    = {1989},
  pages   = {539--541},
}

@article{DNNS97,
  author  = {Duverney, D. and Nishioka, {\relax Ke}. and Nishioka, {\relax Ku}. and Shiokawa, I.},
  title   = {Transcendence of {R}ogers--{R}amanujan continued fraction and reciprocal sums of {F}ibonacci numbers},
  journal = {Proc. Japan Acad. Ser. A Math. Sci.},
  volume  = {73},
  number  = {7},
  year    = {1997},
  pages   = {140--142},
  doi     = {10.3792/pjaa.73.140},
}

@article{ESS12,
  author  = {Elsner, C. and Shimomura, S. and Shiokawa, I.},
  title   = {Algebraic relations for reciprocal sums of even terms in {F}ibonacci numbers},
  journal = {J. Math. Sci. (N.Y.)},
  volume  = {180},
  number  = {5},
  year    = {2012},
  pages   = {650--671},
  note    = {translated from Fundam. Prikl. Mat. \textbf{16} (2010), no.~5, 173--200},
  doi     = {10.1007/s10958-012-0663-0},
}

@article{Uva69,
  author  = {Uvarov, V. B.},
  title   = {The connection between systems of polynomials orthogonal with respect to different distribution
             functions},
  journal = {U.S.S.R. Comput. Math. Math. Phys.},
  volume  = {9},
  number  = {6},
  year    = {1969},
  pages   = {25--36},
  note    = {translated from Zh. Vychisl. Mat. Mat. Fiz. \textbf{9} (1969), 1253--1262},
}

@misc{QZ3,
  author  = {{Solomon Admasu}, Fikreab},
  title   = {{QZeta3}: {L}ean 4 formalisation of the irrationality of $\zeta_{1/p}(3)$ (moving-denominator {H}ankel
             argument)},
  note    = {version 0.1.0, 2026-10-11, Apache License 2.0; directory \texttt{lean/} of \cite{UPL}},
}

@article{XW13,
  author  = {Xu, Z. and Wang, T.},
  title   = {The infinite sum of the cubes of reciprocal {P}ell numbers},
  journal = {Adv. Difference Equ.},
  volume  = {2013},
  year    = {2013},
  note    = {Paper No. 184, 10 pp.},
  doi     = {10.1186/1687-1847-2013-184},
}

% Kri26: give the arXiv identifier once posted, and make the Lean repository public before submission
% (it currently returns 404 to the public). Until then:
@misc{Kri26,
  author  = {Krisman, S.},
  title   = {The sum of the reciprocal cubes of the {F}ibonacci numbers is irrational},
  note    = {preprint, 2026, arXiv:XXXX.XXXXX; Lean formalisation at
             \url{https://github.com/telaviv/fibonacci-zeta3-irrationality}},
}

% optional, if the AJ89 sentence also mentions the Pade-approximant generalisation
@article{Pre98,
  author  = {Pr{\'e}vost, M.},
  title   = {On the irrationality of $\sum\frac{t^n}{A\alpha^n+B\beta^n}$},
  journal = {J. Number Theory},
  volume  = {73},
  number  = {2},
  year    = {1998},
  pages   = {139--161},
  doi     = {10.1006/jnth.1998.2304},
}
```

The `doi` field is ignored by `amsplain`; it is harmless. Kra21, Nes96, Pre96, Wal10, Zud16, Zud17, ESS07, ESS08
and UPL need no change. You could add `number` fields (Nes96: 9; Pre96: 2; Zud17: 2; ESS07: 1; ESS08: 3).

## 3. Proposed replacement wording

### 3.1 Lines 82–90 (history paragraph)

Current problems:
* AJ89 is understated.
* DNNS97 is given only for Q = −1.
* The Q = 1 case is missing.
* Wal10 is cited for a claim it does not make.
* "are not of this kind" overstates.
* "before [Kri26]" does not say that Kri26 is a preprint.

Proposed text, which needs `ESS12` added to `refs.bib`:

> The case $(P,Q)=(1,-1)$, $\sum_nF_n^{-3}\notin\QQ$, is the main result of the preprint \cite{Kri26}; we refer there
> for the history of the Fibonacci zeta function. Briefly: Andr\'e-Jeannin proved that $\sum_nU_n^{-1}$ is irrational
> for every Lucas sequence with $Q=\pm1$ and $D>0$, in particular $\sum_nF_n^{-1}\notin\QQ$ \cite{AJ89}. For both
> signs of $Q$, Duverney, Ke.~Nishioka, Ku.~Nishioka and Shiokawa proved that the even powers $\sum_nU_n^{-2s}$
> ($s\ge1$) are transcendental, and for $Q=-1$ also the odd-index sums $\sum_nU_{2n-1}^{-s}$ \cite{DNNS97}. Elsner,
> Shimomura and Shiokawa determined the algebraic relations among such numbers \cite{ESS07,ESS08,ESS12}. These sums
> are values of quasi-modular forms at algebraic points, to which Nesterenko's theorem \cite{Nes96} applies (see
> \cite[\S3.4]{Wal10} for the Fibonacci zeta function). The odd powers $\sum_nU_n^{-(2s+1)}$ of the full sums are not
> known to be of this kind. For the Pell numbers, Xu and Wang \cite{XW13} evaluated the integer part of
> $\bigl(\sum_{k\ge n}\cP_k^{-3}\bigr)^{-1}$; we know of no irrationality result for any full sum $\sum_nU_n^{-3}$
> before the preprint \cite{Kri26}.

Notes on the wording:
* "for every Lucas sequence with Q = ±1 and D > 0" comes from the zbMATH review of AJ89 (see (a)). If you want to
  claim only what can be checked against the printed note, write "for a class of binary recurrences that includes
  every $U_n(P,\pm1)$".
* The Wal10 citation now supports only what Wal10 says: ζ_F at even integers, via Nesterenko.
* "Not known to be of this kind" is the referee's wording. No source states it outright. It is a statement of
  absence, consistent with Wal10 §3.4, the ESS survey (Kôkyûroku 1665) and Meher–Sahoo 2024 intro, all of which
  list only even-power or odd-index results.
* Optional: after \cite{AJ89} add "(see also Prévost \cite{Pre98} for $\sum t^n/(A\alpha^n+B\beta^n)$)".

### 3.2 Lines 97–100 (method lineage)

Supported as written. One optional precision: "an unrefereed research draft" could become "an unrefereed,
AI-assisted research draft", which matches the UPL note and the repository's `docs/ATTRIBUTION.md`. No change is
needed.

### 3.3 Lines 601–602 (provenance)

Supported. The adapted files in `LucasU/` carry headers of the form "Adapted from
uplift-universal-inc/qzeta_3-irrationality, lean/QZeta3/… (Apache-2.0, Lean formalisation by F. Solomon Admasu)".
I spot-checked `LucasU/Analytic/{Basis,Decay,Entry,Functional}.lean`. The NOTICE/LICENSE content was not audited
here.

## 4. Answers to the referee's questions

### (a) What does [AJ89] prove?

Source: zbMATH [Zbl 0682.10025](https://zbmath.org/?q=an:0682.10025). This is secondary, but the review states the
theorem explicitly. I found no open full text of the C. R. note.

Statement, as given in the review:
* Setup: r ∈ ℤ∖{0}, s = ±1, r² − 4s > 0, and α, β the roots of X² − rX + s. Let (w_n) be any integer sequence with
  w_n = r w_{n−1} − s w_{n−2} and w_n ≠ 0 for n ≥ 1. Write w_n = c₁αⁿ + c₂βⁿ with c₁c₂ ≠ 0.
* Conclusion: for every x ∈ ℤ with |x| < |α| and |c₁c₂| x² < |α|, the sum Σ_{n≥1} xⁿ/w_n is irrational.
* Method: Apéry-type approximations p_{n,n}/q_{n,n}.

What this means for us:
* Take w_n = U_n(P,Q) with Q = s = ±1 (the paper uses the same recurrence convention, U_{n+1} = PU_n − QU_{n−1}).
  Then c₁c₂ = −1/D, and with x = 1 the conditions hold because 1/D < η.
* So AJ89 already gives **Σ 1/U_n(P,Q) ∉ ℚ for every admissible (P,Q) of this paper**, not just for the Fibonacci
  numbers. It also gives Σ 1/V_n for the companion Lucas sequences (c₁ = c₂ = 1, x = 1 < α).
* The title's "certaines suites récurrentes" refers to exactly this class.
* Replacement sentence: see §3.1. Prévost, J. Number Theory 73 (1998) 139–161 (zbMATH 0920.11044, DOI
  10.1006/jnth.1998.2304) extends the Padé approach to Σ tⁿ/(Aαⁿ + Bβⁿ) over ℚ and imaginary quadratic fields. It is
  optional.

### (b) Does [DNNS97] treat generalised sequences?

**Yes, and both signs.** Source: zbMATH [Zbl 0902.11029](https://zbmath.org/?q=an:0902.11029), review by P. Bundschuh
(secondary). The review states:
* Setup: α, β algebraic with |α| > 1 > |β|, U_n = (αⁿ − βⁿ)/(α − β), V_n = αⁿ + βⁿ.
* If β = α^{−1}: Σ U_n^{−2s} and Σ V_n^{−s} are transcendental for every s ≥ 1.
* If β = −α^{−1}: the same holds for Σ U_n^{−2s}, Σ V_n^{−2s} and Σ U_{2n−1}^{−s}.
* The Fibonacci and Lucas cases are stated as corollaries.

This is confirmed for αβ = −1 by the authors' coworkers' survey: ESS, RIMS Kôkyûroku 1665 (2009), §1 (local
`lit/kokyuroku_1665-16.txt`). It credits DNNS [2] (= DNNS97) with the transcendence of Σ U_n^{−2s}, Σ V_n^{−2s},
Σ U_{2n−1}^{−s} and Σ V_{2n}^{−s} for s = 1, 2, 3, …, and mentions the Pell numbers explicitly as the case
β = 1 − √2.

The Fibonacci special cases (Σ F_n^{−2s}, Σ 1/F_{2n−1}) go back to the same authors' 1996 notes: Proc. Japan Acad.
72 (1996) 202–203, zbMATH 0884.11030, and the Eger proceedings 1998, zbMATH 0938.11039. That is the earlier paper the
referee had in mind. DNNS97 is the right citation for the generalised statement.

Not verified in the source itself: the Project Euclid full text would not load. The paper's sentence is correct for
Q = −1 but omits Q = +1.

### (c) Q = 1

**Known, and covered by the same two references, plus ESS's "even terms" paper for the relations.**
* Transcendence: DNNS97, case β = α^{−1}. For U_n(P,1) take α = η, β = η^{−1}. This gives transcendence of
  Σ U_n(P,1)^{−2s} for all s ≥ 1, for example Σ F_{2n}^{−2s}, since F_{2n} = U_n(3,1). Same source as (b) (secondary).
* Algebraic relations: Elsner–Shimomura–Shiokawa, "Algebraic relations for reciprocal sums of even terms in Fibonacci
  numbers", J. Math. Sci. (N.Y.) 180 (2012) 650–671, translated from Fundam. Prikl. Mat. 16:5 (2010) 173–200 (zbMATH
  1345.11011, DOI 10.1007/s10958-012-0663-0). Its Theorem 4.1, as stated in Kôkyûroku 1665 §4 (local file, same
  authors): for algebraic α, β with αβ = −1, the numbers h₂, h₄, h₆, where h_{2s} = (α − β)^{−2s} Σ U_{2n}^{−2s}, are
  algebraically independent, and every h_{2s} is a rational function of them.
* Why this covers all Q = 1 sequences [Proof sketch, my reduction, not stated in the source]: with A = α², we have
  h_{2s} = Σ (Aⁿ − A^{−n})^{−2s}. Taking α = √η (algebraic) gives Σ U_n(P,1)^{−2s} = (η − η^{−1})^{2s} h_{2s}. So the
  result applies to every U_n(P,1).

Proposed single sentence for both signs:

> For both signs of $Q$ the even powers $\sum_nU_n^{-2s}$ ($s\ge1$) are transcendental \cite{DNNS97}, and their
> algebraic relations are known \cite{ESS07,ESS12}.

### (d) Does [Wal10] discuss the Fibonacci zeta function and its odd values?

It discusses the Fibonacci zeta function, but **not its odd values**. Verified in the source (local
`lit/kokyuroku_1710-18.pdf`):
* §1 lists "those of Fibonacci" among zeta functions.
* §3.4 "Algebraic independence" (pp. 172–173), after Nesterenko's Theorem 12 and Corollaries 13–15, says that
  "another consequence" of Nesterenko's theorem concerns ζ_F(s) = Σ F_n^{−s}. Theorem 16 there is ESS (2006): ζ_F(2),
  ζ_F(4), ζ_F(6) are algebraically independent.
* Nothing is said about ζ_F at odd integers, ζ_F(1), or quasi-modularity.

So the current sentence "The odd powers of the full sums are not of this kind (see [Wal10])" is not supported.
Supported wording:

> These sums are values of quasi-modular forms at algebraic points, to which Nesterenko's theorem \cite{Nes96} applies
> (see \cite[\S3.4]{Wal10} for the Fibonacci zeta function). The odd powers $\sum_nU_n^{-(2s+1)}$ of the full sums are
> not known to be of this kind.

That is, Wal10 moves to the Nesterenko sentence and the odd-power sentence carries no citation. Our own reduction is
recorded in `handoff/fibzeta/LIT.md` §2 [Heuristic]: Σ F_n^{−3} involves the non-modular odd part of ζ_q(3) at
q = φ^{−2}. That is evidence only, and nothing in the literature proves non-quasi-modularity.

### (e) [XW13]

Verified in the source (open-access PDF, DOI [10.1186/1687-1847-2013-184](https://doi.org/10.1186/1687-1847-2013-184)).

Bibliographic details:
* Authors: Zhefeng Xu and Tingting Wang (Department of Mathematics, Northwest University, Xi'an).
* Title: "The infinite sum of the cubes of reciprocal Pell numbers".
* Journal: Advances in Difference Equations 2013, Paper No. 184, 10 pp. The volume is 2013; there are no page
  numbers.
* The bib entry is right on authors and title; only the volume field is missing.

What it proves:
* The abstract says it evaluates "the integral part of the reciprocal of the sum Σ_{k≥n} 1/P_k³ explicitly in terms of
  the Pell numbers themselves".
* The Theorem gives ⌊(Σ_{k≥n} P_k^{−3})^{−1}⌋ as an explicit polynomial in P_n, P_{n−1}, with separate formulas for n
  even and n odd.
* So "determined the integer part of their reciprocals" is accurate.

Is Zhang–Wang a better citation? No. W. Zhang and T. Wang, Appl. Math. Comput. 218 (2012) 6164–6167 (Σ 1/P_k), and
J. Weinan Teach. Univ. 26 (2011) 39–42 (Σ 1/P_k²), cited as XW13's refs [7], [8], treat the first and second powers.
XW13 answers the cube question raised at the end of their paper, so XW13 is the right citation for cubes. Citing
Zhang–Wang 2012 alongside it is optional. The Fibonacci prototype is Ohtsuka–Nakamura, Fibonacci Quart. 46/47
(2008/09) 153–159.

### (f) [QZ3] author

The repository's own file `lean/CITATION.cff` (commit d12d56f) reads:

```
authors:
  - family-names: "Solomon Admasu"
    given-names: "Fikreab"
license: Apache-2.0
date-released: "2026-10-11"
version: "0.1.0"
```

So "F. Solomon Admasu" is **not garbled**. It is the CFF's own split: given name Fikreab, family names "Solomon
Admasu", presumably the Ethiopian patronymic form. Use the full form `author = {{Solomon Admasu}, Fikreab}`, which
amsplain prints as "Fikreab Solomon Admasu". That removes the "looks garbled" impression.

The top-level repository (UPL) uses only the pen name "uplift-universal-inc" (root `CITATION.cff`; `docs/ATTRIBUTION.md`
says the pen name is "owner-approved" and that "Human author names are not inferred from anonymous or pseudonymous
accounts"). `docs/PUBLISHING.md` names the GitHub account `fikreab-s` as the publisher.

So: QZ3 → Fikreab Solomon Admasu, per `lean/CITATION.cff`; UPL → uplift-universal-inc, per the root `CITATION.cff`.
Both entries as they stand are consistent with the repository.

### (g) [Kri26]

**Not found anywhere public.** Searched by title only:
* arXiv API, exact-title search and ti:"reciprocal cubes" AND ti:Fibonacci: 0 results.
* Web search on the exact title: no matching document.
* Zenodo API and HAL API title searches: 0 results.

Lean URL:
* `https://github.com/telaviv/fibonacci-zeta3-irrationality` returns **404** to an unauthenticated request (both the
  web page and `api.github.com`).
* The authenticated GitHub API shows that the repository **exists but is private** (`"private": true`, created
  2026-11-15T07:10Z).

Action:
* Make the repository public, or drop the URL, before the paper is distributed.
* Add the arXiv number once Kri26 is posted.
* Keep "preprint" in the entry, and say "the preprint [Kri26]" where the priority claim is made (§3.1).

### (h) Cite keys

`main.tex` cites exactly AJ89, DNNS97, ESS07, ESS08, Kra21, Kri26 (11×), Nes96, Pre96, QZ3 (2×), UPL (2×), Uva69,
Wal10, XW13, Zud16, Zud17. These are the 15 keys of `refs.bib`, one to one. `Fau` appears in neither file (the only
grep hit for "fau" is `pdfauthor`).

If the §3.1 rewrite is adopted, add `ESS12` to `refs.bib` (and `Pre98` if used). UPL is also cited from inside the
QZ3 note, which is fine because UPL is cited in the text.

## 5. Problems found (short list)

1. **Wal10 is misused.** It covers only even ζ_F values; it says nothing about odd powers. Move the citation, and use
   "not known to be".
2. **DNNS97 is understated.** It covers Q = +1 as well as Q = −1. The paper treats both signs but cites only Q = −1.
3. **The Q = 1 relations are uncited.** Add ESS, J. Math. Sci. 180 (2012), the "even terms" paper.
4. **AJ89 is understated.** It proves Σ 1/U_n irrational for all Q = ±1 Lucas sequences, not only for Fibonacci.
5. **Uva69 title.** Drop "that are".
6. **XW13.** Details correct; add `volume = {2013}`. The claim is verified in full text.
7. **QZ3.** "F. Solomon Admasu" matches `lean/CITATION.cff`; spell out "Fikreab".
8. **Kri26.** Not public: no arXiv, and the Lean repository is private (404). Fix before submission, and call it a
   preprint in the priority sentence.

## 6. Update (2026-11-15)

The Lean repository cited in [Kri26], https://github.com/telaviv/fibonacci-zeta3-irrationality, is now public: an
unauthenticated request returns HTTP 200, and the API reports visibility "public". The paper itself still has no public
preprint identifier, so the entry keeps "preprint, 2026".
