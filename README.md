# Exact semiprimes in almost all intervals of length (log x)^2.092

This repository contains a Lean 4 formalization of the paper
*Exact semiprimes in almost all intervals of length (log x)^2.092*
(`paper/exact_semiprimes_exponent_2092.tex`, compiled PDF alongside).

Matomäki and Teräväinen (*Almost primes in almost all short intervals II*,
Trans. AMS 2023, Theorem 1.1) proved that almost every interval
`(x, x + (log x)^2.1]` contains a product of exactly two primes.  The paper
replaces `2.1` by every `c > 3688/1763 = 2.09188…`, in particular by `2.092`.

| Argument | Large-value input | Admissible exponent |
|---|---|---|
| Matomäki–Teräväinen, Theorem 1.1 | Jutila, threshold `49/206` | `c = 2.1` |
| Matomäki–Teräväinen, optimized | Jutila, threshold `49/206` | `c > 197/94 = 2.09574…` |
| one threshold for both Type II factors | Guth–Maynard, `17/70` | `c > 67/32 = 2.09375` |
| **this project** | **Guth–Maynard, threshold depending on the length** | **`c > 3688/1763 = 2.09188…`** |

## Main theorems

```lean
theorem ExactSemiprimes.mainTheorem_exponent_2092
    (inputs : ExternalInputs) (ext : ParameterExtensionInputs) :
    Results.CleanTheoremStatement          -- Theorem 1.2: exponent 2.092

theorem ExactSemiprimes.mainTheorem_parameter
    (inputs : ExternalInputs) (ext : ParameterExtensionInputs) :
    Results.ParameterTheoremStatement      -- Theorem 1.3: every c > 3688/1763
```

Theorem 1.2 says: there are `c₀, δ > 0` such that for all but
`O(X/(log X)^δ)` integers `x ≤ X`, the interval `(x, x + (log x)^2.092]`
contains at least `c₀ (log x)^1.092` products `pq` with
`(log x)^1.091 < p ≤ (log x)^1.092`.

**Cited theorems + labelled parameter extensions + Mathlib + symbol
manipulation = the new result.**  `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound`; there is no `sorry`, no project
`axiom`, and no inhabitant of either hypothesis bundle.

## Assumptions

The two main theorems take two hypothesis bundles as explicit arguments.
`ExactSemiprimes/Audit.lean` walks the proof term and lists the fields that
are actually used.

**Cited published theorems** (`ExternalInputs`,
`ExactSemiprimes/Assumptions.lean`).  The bundle has 21 fields, each a
published theorem transcribed in its printed parameter range.  The proof
uses these 13:

| Lean field | Source |
|---|---|
| `guthMaynardMainLargeValues` | Guth–Maynard, *New large value estimates for Dirichlet polynomials*, Ann. of Math. 203 (2026), Theorem 1.1 |
| `guthMaynardLongPolynomial` | Guth–Maynard, ibid., Proposition 12.1 (the bound for `T^(5/6) ≤ N ≤ T`) |
| `matomakiTeravainenLemmaThreeFour` | Matomäki–Teräväinen, *Almost primes in almost all short intervals II*, Trans. AMS 376 (2023) [MT23], Lemma 3.4 = Heath-Brown's sparse mean value theorem (Acta Arith. 184 (2018), Theorem 4(iii)) |
| `hildebrandTenenbaumCorollaryOneThree` | Hildebrand–Tenenbaum, J. Théor. Nombres Bordeaux 5 (1993), Corollary 1.3 and (1.14): `log Ψ(x,(log x)^a)/log x → 1 - 1/a` |
| `lucaTothTheoremOne` | Luca–Tóth, J. Integer Seq. 20 (2017), Theorem 1 (moments of the divisor function) |
| `iwaniecKowalskiTheoremNineOne` | Iwaniec–Kowalski, *Analytic Number Theory* (2004), Theorem 9.1 (mean value theorem, as [MT23, Lemma 3.2]) |
| `iwaniecKowalskiTheoremNineFour` | Iwaniec–Kowalski, Theorem 9.4 (discrete mean value theorem) |
| `iwaniecKowalskiTheoremNineSix` | Iwaniec–Kowalski, Theorem 9.6 (Halász–Montgomery inequality) |
| `matomakiTeravainenPropositionTwoTwo` | [MT23], Proposition 2.2 and (2.9)–(2.11) (Harman-sieve decomposition into Type I, I/II, II sums) |
| `matomakiTeravainenTheoremTwoOnePartOne` | [MT23], Theorem 2.1(i) (the minorant is below the prime indicator) |
| `matomakiTeravainenEquationTwoFour` | [MT23], equation (2.4) (pointwise bound for the minorant) |
| `matomakiTeravainenLemmaThreeThree` | [MT23], Lemma 3.3 (improved mean value theorem) |
| `matomakiTeravainenEquationFiveSix` | [MT23], equation (5.6) (Vinogradov–Korobov decay of the structured Type II factor) |

The other eight fields (Mertens, Watt, Deshouillers–Iwaniec, Harman's
Lemma 1.5, Iwaniec–Kowalski Theorem 6.7, and the `c = 2.1` cases of
[MT23, Lemma 3.1, Theorem 2.1(ii), Section 5]) are carried but not used.

**Labelled parameter extensions** (`ParameterExtensionInputs`,
`ExactSemiprimes/Extensions.lean`).  These five statements are **not**
verbatim published results: each is a published lemma printed only at
`c = 2.1` (or `a ∈ [1.0999, 1.1]`), restated uniformly in the parameters
because its printed proof does not use their numerical values.  All five are
used.

| Field | Extends | Range needed here |
|---|---|---|
| E1 `generalParsevalReduction` | Matomäki–Radziwiłł, Ann. of Math. 183 (2016), Lemma 14; Teräväinen, Math. Proc. Camb. Phil. Soc. 161 (2016), Lemma 1; [MT23, Lemma 3.1] | general cutoff `T₀`, coefficients bounded by `K` |
| E2 `uniformLongIntervalMinorant` | [MT23, Theorem 2.1(ii)] | `1 ≤ a ≤ 11/10` |
| E3 `uniformRoughPairSieve` | [MT23, Section 5, rough-pair sieve bound] | `1 ≤ a ≤ c - 1`, `c ≤ 2.1` |
| E4 `uniformTypeIComponent` | [MT23, Section 5.1] (Type I sums, via Deshouillers–Iwaniec) | `1925/1763 ≤ a ≤ 11/10` |
| E5 `uniformTypeIOneHalfComponent` | [MT23, Section 5.2] (Type I/II sums, via Watt) | `1925/1763 ≤ a ≤ 11/10` |

For E4 and E5 the only `a`-dependent step is the power check
`(1 - 1/a)/4 ≥ 81/3850 > 1/100`.  None of the extensions concerns the
Type II sums, where the improvement happens.

**Guth–Maynard transcription.**  The two Guth–Maynard fields were checked
term by term against arXiv:2405.20552v2 (7 April 2026), Theorem 1.1 and
Proposition 12.1; theorem numbers follow that version.  The only differences
are that the Lean fields hold for all `T ≥ 1` rather than all large `T`
(equivalent after enlarging the constant) and that Proposition 12.1 indexes
`n ∼ N` while the Lean sum includes `n = N` (every coefficient sequence the
proof uses vanishes there).  Details are in `ASSUMPTIONS.md`, section
*Normalization of the Guth–Maynard inputs*.

The new mathematics is proved, not assumed: the length-dependent
Guth–Maynard density estimate (`Hybrid/RefinedDensity.lean`), the Type II
estimate with threshold `17/70`, the sparse Heath-Brown branches, the
three-case treatment of the medium large-value bins that gives
`a > 1925/1763` (`Final/TypeIIDensityBins.lean`,
`Final/TypeIIComponent.lean`), and the whole passage to Theorems 1.2 and 1.3.

`ASSUMPTIONS.md` lists every hypothesis with its source and the power checks
behind each extension; `FORMALIZATION_STATUS.md` describes the route of the
proof; `MODULE_MAP.md` maps the paper to the Lean files.

## Building

The project is pinned to Lean 4.34.0 and Mathlib v4.34.0.

```text
lake exe cache get                          # download compiled Mathlib
lake build                                  # build the project
lake env lean ExactSemiprimes/Audit.lean    # axioms and hypotheses actually used
```

## Layout

- `Definitions.lean`: shared definitions and module metadata.
- `Assumptions.lean`: the cited published inputs (`ExternalInputs`).
- `Extensions.lean`: the five labelled parameter extensions
  (`ParameterExtensionInputs`).
- `MainTheorem.lean`: the two end-to-end theorems; `Audit.lean`: the trust
  audit.
- `Hybrid/`: coefficient normalization and the Guth–Maynard density
  estimates (Lemma 4.3), including the length-dependent thresholds.
- `TypeII/`: the Type II estimate with threshold `17/70` (Proposition 5.1).
- `Sparse/`: the sparse polynomial and the two Heath-Brown branches
  (Section 6).
- `Completion/`: the Perron/variance reduction and the passage to exact
  semiprimes.
- `Final/`: the assembly uniform in the prime blocks — the medium bins,
  the Type II components, the complement of `𝒰`, high frequencies, the
  Dirichlet-polynomial target and variance (Proposition 7.1), and
  Section 7.2.
- `Results/`: the parameter theorem, the rational arithmetic for `2.092`,
  and the clean theorem.
- `paper/`: the TeX source and PDF of the paper.

`Results/PreviousStateOfArt.lean` records the Matomäki–Teräväinen theorem
for comparison only; it is not a premise of the new theorem.

## Formalization policy

- Every published analytic input is an explicit field of `ExternalInputs`
  and names an exact theorem, proposition, lemma or displayed equation.
- An extension of a published statement beyond its printed parameter range
  is never attributed to the source: the five that are assumed are the
  separate, labelled fields of `ParameterExtensionInputs`, each naming the
  source whose proof it extends.
- Normalizations, combinations of cited results and paper-specific
  adaptations are proved in Lean.
- The main theorems take both bundles as explicit hypotheses, so their
  conditional nature is visible in their types; no axiom is involved.

## Provenance

The paper is a research draft and has not been refereed.  An earlier draft
generated with ChatGPT (OpenAI) obtained `c > 67/32` with a single threshold
`17/70`; the length-dependent refinement to `c > 3688/1763`, this write-up
and the Lean formalization were produced with Claude (Anthropic).
