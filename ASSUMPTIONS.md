# Assumptions used by the Lean proof

## Summary: what the main theorem assumes

The end-to-end results are

```lean
theorem ExactSemiprimes.mainTheorem_exponent_2092
    (inputs : ExternalInputs) (ext : ParameterExtensionInputs) :
    Results.CleanTheoremStatement          -- paper Theorem 1.2 (exponent 2.092)

theorem ExactSemiprimes.mainTheorem_parameter
    (inputs : ExternalInputs) (ext : ParameterExtensionInputs) :
    Results.ParameterTheoremStatement      -- paper Theorem 1.3 (every c > 3688/1763)
```

in `ExactSemiprimes/MainTheorem.lean`.  `#print axioms` reports only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`; the project has no
`sorry`, no `axiom`, and no inhabitant of either hypothesis bundle.  So the
formal content is exactly

> **cited theorems (`ExternalInputs`) + labelled parameter extensions
> (`ParameterExtensionInputs`) + Mathlib + symbol manipulation
> = the new result.**

There are two hypothesis bundles, kept strictly apart:

1. `ExternalInputs` (`ExactSemiprimes/Assumptions.lean`, 21 fields): published
   theorems, each transcribed with its printed hypotheses and in its printed
   parameter range.  See *Cited input inventory* below.
2. `ParameterExtensionInputs` (`ExactSemiprimes/Extensions.lean`, 5 fields):
   uniform-in-parameter versions of five published Matomäki--Radziwiłł /
   Teräväinen / Matomäki--Teräväinen statements that are printed only at
   `c = 2.1` and `a ∈ [1.0999, 1.1]` (or with a fixed cutoff), whose printed
   proofs do not use those numerical values.  **These are not verbatim
   published statements**; they are explicitly labelled assumptions.  See
   *Labelled parameter extensions* below.

None of the five extensions concerns the new large-value input.  The Type II
components, which carry the improvement from `2.1` to `3688/1763`, are proved
in Lean from the verbatim inputs (Guth--Maynard, Heath-Brown's sparse mean
value theorem, Hildebrand--Tenenbaum, MT23 equation (5.6), Iwaniec--Kowalski,
Luca--Tóth).

### Inputs actually used

`ExactSemiprimes/Audit.lean` walks the proof term of
`mainTheorem_exponent_2092` and lists the fields it uses (run
`lake env lean ExactSemiprimes/Audit.lean`).  The result is:

| Bundle | Fields used by the main theorem |
|---|---|
| `ExternalInputs` (13 of 21) | `guthMaynardMainLargeValues`, `guthMaynardLongPolynomial`, `matomakiTeravainenLemmaThreeFour` (Heath-Brown), `hildebrandTenenbaumCorollaryOneThree`, `lucaTothTheoremOne`, `iwaniecKowalskiTheoremNineOne`, `iwaniecKowalskiTheoremNineFour`, `iwaniecKowalskiTheoremNineSix`, `matomakiTeravainenEquationTwoFour`, `matomakiTeravainenEquationFiveSix`, `matomakiTeravainenLemmaThreeThree`, `matomakiTeravainenPropositionTwoTwo`, `matomakiTeravainenTheoremTwoOnePartOne` |
| `ParameterExtensionInputs` (5 of 5) | `generalParsevalReduction` (E1), `uniformLongIntervalMinorant` (E2), `uniformRoughPairSieve` (E3), `uniformTypeIComponent` (E4), `uniformTypeIOneHalfComponent` (E5) |

The other eight `ExternalInputs` fields (`mertensSecondTheorem`,
`matomakiTeravainenLemmaThreeOne`, `matomakiTeravainenTheoremTwoOnePartTwo`,
`matomakiTeravainenSectionFiveRoughSieve`, `wattEquationFourSeven`,
`deshouillersIwaniecEquationFourteen`, `harmanLemmaOneFive`,
`iwaniecKowalskiTheoremSixSeven`) are carried as hypotheses but never used by
the final proof.  Three of them are the printed `c = 2.1` special cases of
E1--E3 (Lemma 3.1, Theorem 2.1(ii), the Section 5 sieve display); the other
five (Mertens, Watt, Deshouillers--Iwaniec, Harman, IK Theorem 6.7) are
ingredients of the printed proofs of E2--E5 and of MT23 (5.6), and were used
by alternative routes that the final proof does not need (see
`FORMALIZATION_STATUS.md`).

## Citation and trust policy

The main theorem is conditional only on identifiable results from the
published analytic-number-theory literature and on the five labelled
extensions.  Every field in `ExactSemiprimes/Assumptions.lean` names a
specific theorem, proposition, lemma, corollary, or displayed estimate.

There are four important distinctions:

1. A verbatim source result can be imported with its exact published
   hypotheses.
2. A change of normalization or line of integration that is not already part
   of the cited source statement is not silently attributed to that source;
   it is an internal Lean lemma.
3. A consequence obtained by combining two published results is not itself
   made an assumption.
4. Elementary and measure-theoretic steps expected from Mathlib are not
   included in the external assumption bundle.

The cited trust boundary `ExternalInputs` contains **21 fully typed cited
inputs and 0 opaque proposition slots**.  The separate, labelled bundle
`ParameterExtensionInputs` is described in its own section below.

Every field has a complete quantified Lean proposition type.
For the Guth--Maynard results, coefficient bounds, closed support,
one-spacing, height and amplitude hypotheses, arbitrary `T^ε` loss, constants,
and all three conclusion terms are explicit.  The Hildebrand--Tenenbaum input
is the direct fixed-`a` logarithmic-limit consequence of the cited corollary
(`log Ψ(x,(log x)^a)/log x → 1-1/a`), rather than a verbatim transcription
of the corollary itself.  Mertens' theorem is a `Tendsto`
statement for the reciprocal-prime sum.  Luca--Tóth Theorem 1 is recorded
for every integer moment `r ≥ 2`, with its positive main-term constant,
degree `2^r-1`, one-logarithm-smaller error, and an explicit eventual
threshold.  Matomäki--Teräväinen's sparse
mean-value lemma includes its general estimate and its improved alternative
with the third term deleted.  The Perron-reduction lemma includes the exact
four-term minorant from equation (2.3), its Dirichlet-polynomial hypothesis,
and the resulting variance (2.6), only in the parameter range printed in
MT23.  These are direct proof fields of `ExternalInputs`.

Proposition 2.2 is transcribed at its printed values
`z₀=exp(log X/(log log X)^3)`, `z=X^(2/11)`, and
`δ_A=(log X)^(-10A)`.  Its admissible `Y` interval, finite family-size
bound, exact decomposition identity, support and square-sum bound (2.10),
all three structural alternatives, and the ordered-prime-tuple coefficient
(2.11) are explicit.  For fixed `ε,A`, the family-size constant, remainder
constant, and divisor-bound witnesses `Bcoeff,Acoeff` are all chosen before
`X,Y`.  Thus one pair of coefficient witnesses applies uniformly to every
function in the family and every admissible principal scale.

Lemma 3.3 is recorded on the imaginary axis and on the printed symmetric
interval `[-T,T]`, with its diagonal and shifted-correlation terms intact.
Its absolute implied constant is quantified before `N,T` and the coefficient
sequence.  The source derives it from Iwaniec--Kowalski [IK04, Lemma 7.1]
with `Y=10T` and `x_m=(2π)⁻¹ log m`; Lean imports the resulting MT23 lemma,
not an unstated normalized version of the Iwaniec--Kowalski result.

Theorem 2.1(i) is recorded in the theorem's full fixed setup and is pointwise
for every integer `n∈[2X^(1/2),3X]`.  It imports neither the long-interval
lower bound in part (ii) nor the variance estimate in part (iii).

Theorem 2.1(ii) is recorded as the exact single-block long-interval lower
bound, with its constant `200`, uniformly for the printed `a`-window and
every real `x∈(X,2X]` once `X` is sufficiently large.  The later block-summed
equation (2.7) is not folded into this assumption.

Lemma 3.5(i),(ii) is recorded at the precise normalization printed in MT23,
which MT23 obtains from Watt [Watt95, equation (4.7)] and
Deshouillers--Iwaniec [DI82, equation (14)] after the reductions described
in its proof.  The four scale variables, the short zeta segment, the dyadic
coefficient polynomial, the integration interval, both rational-power
expressions, and the two different coefficient norms are explicit.

Lemma 3.2 is recorded on the zero line over `[-T,T]`.  Its printed
`(2T+O(N))∑|a_n|²` equality is represented by an absolute-error
inequality with one uniform absolute constant.

Iwaniec--Kowalski Theorem 9.4 is recorded for arbitrary complex coefficients
on `1≤n≤N` and an arbitrary finite one-spaced set in `[0,T]`, with
`N,T≥1`.  Its absolute implied constant and the complete discrete
mean-square bound `(∑|a_n|²)(T+N)*log(2N)` are explicit.  This is the
discrete theorem cited in the powered-polynomial step of [MT23, Proposition
5.1]; it is kept distinct from the continuous Theorem 9.1 input.  The local
product-fiber expansion, line-one normalization, coefficient energy, and
divisor-subpower specialization are proved in
`TypeII/PoweredMeanValue.lean`.

Iwaniec--Kowalski Theorem 9.6 (labelled “Montgomery” in the source) is
recorded for an arbitrary finite one-spaced set in `[0,T]`, arbitrary complex
coefficients supported on `1≤n≤N`, and `N,T≥1`.  Its absolute implied
constant and the complete bound
`(∑|a_n|²)(N+R*T^(1/2))*log(2T)` are explicit.  Applying it to the
dyadic polynomial `M₂(1+it)` requires the local normalization
`a_n=β_n/n` on `M₂<n≤2M₂`; that normalization, its exact energy bound,
and the resulting Type-II product estimate are proved locally in
`TypeII/HalaszMontgomery.lean`, rather than folded into this assumption.

Luca--Tóth Theorem 1 is kept at its source-faithful **integer-moment**
level.  The local proof in `TypeII/WeightedExtremeRange.lean` chooses
`r = max 2 ⌈2B⌉`, uses `1 ≤ d(n)` to dominate the real power `d(n)^(2B)`
by `d(n)^r`, restricts the moment sum to the dyadic interval `(M,2M]`, and
divides by the line-one factor `n²`.  This yields the required bound
`∑_{M<n≤2M}|a_n/n|² ≤ D (log T)^Q/M` for divisor-bounded coefficients.
Thus neither a real-moment theorem nor the final dyadic-energy consequence
is placed in the external trust boundary.

The Type-II bridge modules add no external input.
`TypeII/OuterLengthGeometry.lean` derives a uniformly bounded powering order,
the literal natural powered supports, the strong complementary-length
interval (and its weaker hybrid-range consequence), and eventual bin-width
bounds from elementary inequalities and the already typed hypotheses.
`TypeII/OuterParameterReserve.lean` performs the shifted-threshold and saving
reserve bookkeeping; `TypeII/MediumLogBinBridge.lean`,
`TypeII/MediumRegimeAssembly.lean`, `TypeII/ExtremeSmallAssembly.lean`, and
`TypeII/ExtremeRegimeAssembly.lean` instantiate and sum previously proved
local estimates.  Finally, `Hybrid/IntegralDiscretization.lean` proves the
unit-cell/parity conversion from the discrete one-spaced sums to the local
integral.  `TypeII/FullTypeIIEstimate.lean` then combines all three regimes,
absorbs their fixed and logarithmic losses, and applies that integral bridge
to prove the fully quantified Proposition 5.1 estimate.  Consequently none
of these modules enlarges the trust boundary.

Harman Lemma 1.5 is encoded for the exact prime set `P≤p<2P`, with
`V≥e`, `P≥2`, `V≤|t|<2V`, both printed error terms, and its implied constant
chosen after the fixed real part `σ`.  `StructuredPrimeFactors`,
`HarmanScaleArithmetic`, `HarmanNumericPaperScale`, and
`HarmanDyadicEventual` derive the uniform paper-scale full-dyadic decay from
this field.  The literal theorem does not directly imply the uniform
short-segment estimate of MT23 equation (5.6) (that would need a smooth
Fourier/Perron projector to `(Q,(1+δ)Q]`), so the main theorem uses the
cited equation (5.6) instead and does not use this field.

Iwaniec--Kowalski Theorem 6.7 is encoded for a fixed injective admissible
integer tuple.  The residue count, Euler product, simultaneous-prime counting
function, leading factor `2^k k!`, and logarithmic relative error are explicit,
and the constants are chosen after the tuple.  MT23 invokes a sieve argument
“similar to” this theorem for a rough-number pair correlation.  The fixed
prime-tuple theorem does not directly furnish that different consequence,
which the main theorem takes from the labelled extension E3 instead; this
field is not used.

All twenty-one statements are direct fields of `ExternalInputs`.  There is no
global axiom asserting that an `ExternalInputs` value exists.

## Cited input inventory

| Lean field | Exact published source | Status and role |
|---|---|---|
| **guthMaynardMainLargeValues** | Guth--Maynard [GM26], Theorem 1.1 | Fully quantified Lean statement; used below polynomial length T^(5/6) |
| **guthMaynardLongPolynomial** | Guth--Maynard [GM26], Proposition 12.1, specifically its displayed “In particular” conclusion | Fully quantified Lean statement; three-term consequence for T^(5/6) ≤ N ≤ T |
| **matomakiTeravainenLemmaThreeFour** | Matomäki--Teräväinen [MT23], Lemma 3.4, whose underlying input is Heath-Brown [HB18], Theorem 4(iii) | Fully quantified source-scoped Lean statement: `T ≥ M ≥ 1`, `ℳ ⊆ [M,T]`, `N ≥ 2`, coefficient domains and bounds, the symmetric `Re(s)=1` integral, every power of `M,N,T,|ℳ|`, `max_{n∼N}|aₙ|²`, the `η`-dependent constant, and both alternatives in the final deletion clause are explicit |
| **hildebrandTenenbaumCorollaryOneThree** | Hildebrand--Tenenbaum [HT93], Corollary 1.3 and equation (1.14); primary saddle-point source [HT86], Theorems 1--2 | Fully quantified direct fixed-a consequence for Ψ(x,(log x)^a)=x^(1-1/a+o(1)); verbatim source transcription and local derivation remain to be split |
| **matomakiTeravainenLemmaThreeOne** | Matomäki--Teräväinen [MT23], Lemma 3.1; cf. Teräväinen [Ter16], Lemma 1 | Fully quantified source-scoped Lean implication with the exact minorant (2.3), `c=21/10`, `a∈[c-1-10⁻⁴,c-1]`, `T₀=X^(1/1000)`, `h₁=X^(99/100)`, uniform constants replacing both `≪` symbols, and no claim in the desired wider parameter range |
| **matomakiTeravainenEquationTwoFour** | Matomäki--Teräväinen [MT23], equation (2.4) | Exact pointwise domination of the four-term minorant by `4(log(3X)/log(X^(2/11)))^3 rho(n,X^(2/11))` on `[2X^(1/2),3X]`, with the source's sufficiently-small positive `epsilon` made explicit; the factor is proved locally to be at most `5324` |
| **matomakiTeravainenTheoremTwoOnePartOne** | Matomäki--Teräväinen [MT23], Theorem 2.1(i), with equations (2.1)--(2.4), especially definition (2.3) | Fully quantified source-scoped Lean statement: the printed small-`ε` setup, `X≥3`, `c=2.1`, `h`, `h₁`, the complete `a,P₁` range, exact four-term minorant, closed `n` range, and pointwise prime-indicator inequality are explicit; parts (ii) and (iii) are not included |
| **matomakiTeravainenTheoremTwoOnePartTwo** | Matomäki--Teräväinen [MT23], Theorem 2.1(ii), proved in Section 2.1 | Fully quantified source-scoped Lean statement: the printed small-`ε` setup, a sufficiently-large-`X` threshold uniform over the exact `a,P₁` window, `h₁=X^(99/100)`, every real `x∈(X,2X]`, the exact single-block minorant sum, and the lower bound with constant `200` are explicit; equation (2.7) is not assumed |
| **matomakiTeravainenPropositionTwoTwo** | Matomäki--Teräväinen [MT23], Proposition 2.2, equations (2.9)--(2.11) | Fully quantified source-scoped Lean statement: the exact `z₀,z,δ_A,Y` ranges, family cardinality, decomposition identity, remainder support and square-sum estimate, all Type-I/Type-I/II/Type-II scale constraints, and the structured ordered-prime-tuple formula (2.11) are explicit; the uniform divisor-bound witnesses are quantified before `X,Y` and shared across the decomposition family |
| **wattEquationFourSeven** | Watt [Watt95], equation (4.7), in the normalization proved in [MT23], Lemma 3.5(i) | Fully quantified source-scoped Lean statement: `A,N,N',T≥1`, `N<N'≤2N`, arbitrary complex dyadic coefficients, the exact `[T/2,T]` twisted fourth moment, both displayed scale terms, `max_{m∼A}|a_m|²`, and a constant depending only on `ε` are explicit |
| **deshouillersIwaniecEquationFourteen** | Deshouillers--Iwaniec [DI82], equation (14), in the normalization proved in [MT23], Lemma 3.5(ii) | Fully quantified source-scoped Lean statement with the same ranges and integral as part (i), the additional term `A^(5/4)T^(3/4)`, the averaged norm `A⁻¹∑_{m∼A}|a_m|²`, and a constant depending only on `ε` explicit |
| **harmanLemmaOneFive** | Harman [Harman07], Lemma 1.5, p. 14 | Fully quantified source statement for `p∼P`, meaning `P≤p<2P`: `V≥e`, `P≥2`, `V≤|t|<2V`, arbitrary fixed `σ`, and both printed Vinogradov--Korobov terms are explicit; the implied constant may depend on `σ`; this does not directly supply MT23's short-prime-segment equation (5.6) |
| **matomakiTeravainenLemmaThreeThree** | Matomäki--Teräväinen [MT23], Lemma 3.3, deduced there from Iwaniec--Kowalski [IK04], Lemma 7.1 | Fully quantified source-scoped Lean statement: `N,T≥1`, the full polynomial `∑_{n≤N}aₙn⁻ˢ`, the symmetric imaginary-axis integral, the diagonal term, every nonzero integer shift `|k|≤N/T`, the shifted correlation, and one absolute implied constant are explicit |
| **matomakiTeravainenSectionFiveRoughSieve** | Matomäki--Teräväinen [MT23], Section 5, displayed estimate on p. 16 immediately after Lemma 3.3 | Exact diagonal-plus-shifted-correlation rough-pair estimate in the printed `c=2.1`, `a∈[c-1-10⁻⁴,c-1]`, and `X/h≤T≤X` range; the paper calls the upper-bound sieve argument similar to IK04 Theorem 6.7, so no wider range is silently attributed to IK04 |
| **matomakiTeravainenEquationFiveSix** | Matomäki--Teräväinen [MT23], equation (5.6), derived there via Harman [Harman07], Lemma 1.5 | Exact Vinogradov--Korobov decay for the structured coefficient sequence from equation (2.11), including all short-prime scales, the full moving support and height range, and a fixed implied constant |
| **iwaniecKowalskiTheoremSixSeven** | Iwaniec--Kowalski [IK04], Theorem 6.7, Section 6.8, p. 167, equations (6.96)--(6.97) | Fully quantified source statement for a fixed injective admissible tuple: the local residue counts, convergent Euler product, simultaneous-prime count, factor `2^k k!`, and tuple-dependent error constant and threshold are explicit; it does not directly imply MT23's rough-pair sieve consequence |
| **iwaniecKowalskiTheoremNineOne** | Iwaniec--Kowalski [IK04], Theorem 9.1, in the exact source-scoped normalization [MT23], Lemma 3.2 | Fully quantified Lean statement: `N,T≥1`, arbitrary complex coefficients in `A(s)=∑_{n≤N}a_n n^(-s)`, the symmetric zero-line integral, the main term `2T∑|a_n|²`, and a uniform absolute error bounded by `CN∑|a_n|²` are explicit |
| **iwaniecKowalskiTheoremNineFour** | Iwaniec--Kowalski [IK04], Theorem 9.4, p. 233 | Fully quantified source statement: `N,T≥1`, arbitrary complex coefficients on `1≤n≤N`, a finite one-spaced set in `[0,T]`, the exact discrete mean square on the zero line, `(T+N)*log(2N)`, the coefficient square-sum, and one uniform absolute constant are explicit; the powered-polynomial normalization used in [MT23, Proposition 5.1] is proved locally in `TypeII/PoweredMeanValue.lean` |
| **iwaniecKowalskiTheoremNineSix** | Iwaniec--Kowalski [IK04], Theorem 9.6, p. 234 | Fully quantified source statement: `N,T≥1`, arbitrary complex coefficients on `1≤n≤N`, a finite one-spaced set in `[0,T]`, its cardinality `R`, the exact discrete mean square on the zero line, the coefficient square-sum, `(N+R*T^(1/2))*log(2T)`, and one uniform absolute constant are explicit; the local `a_n=β_n/n` specialization used in [MT23, Proposition 5.1] is proved in `TypeII/HalaszMontgomery.lean` |
| **mertensSecondTheorem** | Mertens [Mer74], the result now called Mertens' second theorem, ∑_{p≤x} 1/p - log log x → B₁ | Fully quantified Lean `Tendsto` statement; not used by the main theorem |
| **lucaTothTheoremOne** | Luca--Tóth [LT17], Theorem 1, specialized to `f(n)=d(n)^r` | Source-faithful integer-moment asymptotic `∑_{n≤x}d(n)^r=xC_r(log x)^(2^r-1)+O_r(x(log x)^(2^r-2))` for every integer `r≥2`; `TypeII/WeightedExtremeRange.lean` locally chooses `r=max 2 ⌈2B⌉` and derives the real-`B` dyadic coefficient-energy bound |

## Labelled parameter extensions (`ParameterExtensionInputs`)

Each field below is a uniform-in-parameter version of a published lemma.
The printed lemma is stated at the single exponent `c = 2.1` and for
`a ∈ [c-1-10⁻⁴, c-1]` (where `P₁ = (log X)^a` is the small prime and
`h = (log X)^c` the interval length), or with a fixed logarithmic cutoff;
the new paper needs `3688/1763 < c ≤ 2.1` and `a` in a window inside
`(1925/1763, 11/10]`.  In every case the printed proof uses the numerical
value of `a` or `c` only through the power checks displayed in the last
column; the paper (proof of Proposition 7.1) re-does those checks for the
wider range.

| Field | Lean statement | Published source being extended | What changes / the power check |
|---|---|---|---|
| **generalParsevalReduction** (E1) | `GeneralParsevalReductionStatement`: for real weights `w`, a prime block `(P,2P]` and the product polynomial `A(s) = (∑_{P<p≤2P} p^(-s))(∑_{X/(2P)<n≤4X/P} w(n) n^(-s))` with coefficients `≤ K`, and `1 ≤ h ≤ h₂ ≤ X/T₀³`, `T₀ ≤ X/h`: `(1/X)∫_X^{2X} |S_h/h - S_{h₂}/h₂|² ≤ C (K²/T₀ + ∫_{T₀}^{X/h}|A|² + max_{T ≥ X/h} (X/(Th)) ∫_T^{2T}|A|²)` with an absolute `C` | [MR16, Lemma 14]; the general-`T₀` form [Ter16, Lemma 1]; used as [MT23, Lemma 3.1] | MR16 prints `|a_m| ≤ 1`, a fixed cutoff `T₀`, and coefficients on `[X,4X]`; the proof (Perron's formula, the low-frequency cancellation from `|t| h₂/X ≤ T₀⁻²`, Plancherel for the high frequencies) is unchanged for arbitrary `T₀` and support `n ≍ X`, and homogeneity gives `K²`.  Used with `T₀ = X^(1/1000)`, `h = (log X)^c/2`, `h₂ = X^(99/100)`, `K = 5324` (the bound `K ≤ 5324` is proved in Lean from MT23 (2.4) and the uniqueness of the small prime factor). See also the audit of Ter16 below. |
| **uniformLongIntervalMinorant** (E2) | `UniformLongIntervalMinorantStatement`: `h₁/(200 log P₁ log X) ≤ ∑_{P₁<p≤2P₁} ∑_{x/p<m≤(x+h₁)/p} ρ⁻(m)` for `h₁ = X^(99/100)`, all `x ∈ (X,2X]`, uniformly for `1 ≤ a ≤ 11/10` | [MT23, Theorem 2.1(ii)], proved in [MT23, Section 2.1] | Printed for `a ∈ [1.0999, 1.1]`.  The proof (Buchstab decomposition of ρ⁻ on a long interval and Mertens for `∑_{p∼P₁} 1/p`) only uses `P₁ → ∞` as a fixed power of `log X`. |
| **uniformRoughPairSieve** (E3) | `UniformSectionFiveRoughSieveStatement`: the diagonal-plus-shifted-correlation bound `T∑|b_n|² + T·Corr ≪ T P₁/(X log X) + 1/(log X)²` for the `X^(2/11)`-rough coefficient sequence, uniformly for `1 ≤ a ≤ c-1`, `c ≤ 2.1`, `X/(log X)^c ≤ T ≤ X` | [MT23, Section 5, display on p. 16 after Lemma 3.3]; an upper-bound sieve as in [IK04, Theorem 6.7] | Printed at `c = 2.1`, `a ∈ [1.0999,1.1]`.  The sieve bound for rough pairs `(n, n+k)` does not depend on `a, c`. |
| **uniformTypeIComponent** (E4) | `UniformTypeIComponentStatement`: for every Type I convolution of [MT23, Proposition 2.2(i)] at `Y = X/P₁`, `∫_𝒰 |P₁(1+it) F(1+it)|² dt ≪ exp(-(log log X)^6)` uniformly for `(log X)^(1925/1763) ≤ P₁ ≤ (log X)^(11/10)` | [MT23, Section 5.1], using the Deshouillers--Iwaniec twisted fourth moment [MT23, Lemma 3.5(ii)] = [DI82, (14)] | The printed argument leaves `P₁ L^(-(1-1/a)/2) X^(O(ε)) ≪ X^(-(1-1/a)/20+O(ε))`; the paper (proof of Proposition 7.1) checks `(1-1/a)/4 ≥ 81/3850 > 1/100` for `a ≥ 1925/1763`. |
| **uniformTypeIOneHalfComponent** (E5) | `UniformTypeIOneHalfComponentStatement`: the same bound for the Type I/II convolutions of [MT23, Proposition 2.2(ii)] | [MT23, Section 5.2], using Watt's twisted fourth moment [MT23, Lemma 3.5(i)] = [Watt95, (4.7)] | The printed argument leaves `P₁ X^(-ε(1-1/a)/4+ε/100+O(ε²))`; same check `(1-1/a)/4 ≥ 81/3850 > 1/100` for `a ≥ 1925/1763`. |

Here `𝒰 = {t ∈ [X^(1/1000), X] : |P₁(1+it)| ≥ P₁^(-ε/10)}` is the
large-prime set of [MT23, Section 5] (`largePrimeValueSet`), and
`ρ⁻ = matomakiTeravainenMinorant X ε` is the four-term Harman minorant
[MT23, (2.3)].

What is *not* extended: Proposition 2.2 (the decomposition), Lemma 3.3,
equation (2.4), equation (5.6), Theorem 2.1(i), and Heath-Brown's sparse
mean value theorem are used exactly as printed; their statements do not
involve `a` or `c` beyond what is transcribed.  The Type II components,
the complement of `𝒰`, the passage `T ≥ X` (mean value theorem plus the
coefficient bound `5324`), the Dirichlet-polynomial target of Proposition 7.1,
the variance bound, and all of Section 7.2 are proved in Lean
(`ExactSemiprimes/Final/`).


## Scope caveat for the Matomäki--Teräväinen inputs

The published form of [MT23, Lemma 3.1] is stated with c = 2.1 and
a in [c-1-10^(-4), c-1].  Likewise, [MT23, Theorem 2.1(ii)] is printed
inside that parameter setup.  The broader uniform parameter range needed in
the new paper is therefore **not** part of either external assumption.

The wider ranges are supplied by the labelled extensions E1 (Perron/Parseval
reduction), E2 (long-interval bound) and E3 (rough-pair sieve) above, which
are kept out of `ExternalInputs` so that no published theorem is mis-cited.
`Completion/LongIntervalMinorant.lean` and `Completion/DyadicPrimeBlocks.lean`
contain the complete application in the exact printed window; the main
theorem uses E2.

### Audit of the general Parseval/Perron citation

[MT23, Lemma 3.1] refers to [Ter16, Lemma 1], which in turn says that it is
a version of [MR16, Lemma 14] with an unspecified lower cutoff `T₀`.
The mathematical Parseval argument is general and does not intrinsically
fix the logarithmic exponents `a,c`.  Nevertheless, the literal printed
statement of [Ter16, Lemma 1] cannot safely be copied into the external trust
boundary:

- it defines `S_h(x)` with a factor `1/h` and then divides `S_h` by `h`
  once more in the displayed conclusion;
- it allows arbitrary complex `a_n` but has the coefficient-independent
  low-frequency term `1/T₀`, which is incompatible with scaling;
- it defines `F(s)` using only `n∼X`, although its short sums for
  `x∈[X,2X]` can involve coefficients above `2X`.

[MR16, Lemma 14] has the coherent bounded-coefficient normalization and
uses the support `[X,4X]`, but fixes its logarithmic cutoff and long interval;
it does not by itself supply the `T₀=X^(1/1000)`, `h₁=X^(99/100)` variant
needed here.  Consequently no new `ExternalInputs` field has been added for
a silently corrected or support-broadened theorem.

The local modules `Completion/GeneralPerronReduction.lean` and
`Completion/PerronCumulativeBounds.lean` instead record exactly what follows
from the printed statements.  They prove the full finite convolution identity for the
actual product polynomial and its literal product-image support, and they
prove that the cumulative `(DPtarget)` bound yields both the middle integral
and every normalized dyadic-tail integral, with exact constants `1` and `2`.
The remaining analytic interface is named
`PerronParsevalAtScaleStatement`; it includes the convolution-coefficient
bound `K` and the homogeneous low-frequency loss `K²/T₀`.  The coefficient
part is proved locally: projection of a fixed-product fibre to its prime
coordinate is injective, equation (2.4) gives `|ρ⁻(n)|≤5324`, and hence
`K≤10648(log X)^a`; this holds uniformly for `1≤a≤11/10`.  Lean also proves
that `K²/X^(1/1000)≤(log X)^(-2-ε)` eventually for every fixed `a,ε`.
Thus the only analytic content of this interface is the Parseval inequality
for the literal product-image support.  It is supplied by the labelled
extension E1 (`generalParsevalReduction`), stated with real
coefficients bounded by `K`, the homogeneous loss `K²/T₀`, and the literal
product polynomial, which avoids the three defects of [Ter16, Lemma 1]
listed above.  The main theorem applies it with `T₀ = X^(1/1000)`,
`K = 5324` (proved in `Final/PerronTail.lean`), `h = (log X)^c/2`, and
`h₂ = X^(99/100)`.

### Normalization of Theorem 2.1(i)

The source first fixes `ε>0` sufficiently small, `X≥3`, `c=2.1`,
`h=(log X)^c`, `h₁=X^(99/100)`, and
`a∈[c-1-1/10000,c-1]`, and then sets `P₁=(log X)^a`.  Lean retains
that complete surrounding setup even though `h,h₁,a,P₁` do not enter the
inequality in part (i).  As elsewhere, the unnumbered smallness condition on
`ε` is represented by an existential positive threshold, not by a claim for
all positive `ε`.

The minorant is literally the four-term function already transcribed from
equation (2.3), with `z=X^(2/11)`.  The source's `1_ℙ(n)` is the real-valued
indicator `if n.Prime then 1 else 0`, and membership in
`[2X^(1/2),3X]` is expressed by the two inclusive real inequalities after
coercing `n : ℕ` to `ℝ`.

Part (i) has no exceptional-set qualification: it holds for every integer in
that range.  The direct field deliberately contains neither part (ii), which
is a uniform long-interval lower bound for every `x∈(X,2X]`, nor part (iii),
which is the variance estimate from equation (2.6).

### Normalization of Theorem 2.1(ii)

The smallness of `ε` is again represented by an existential positive
threshold.  The phrase “once `X` is large enough” becomes a real cutoff
`X₀≥3`, chosen after the fixed `ε` but before `X` and `a`.  Thus the cutoff
is uniform over the compact printed interval
`a∈[c-1-1/10000,c-1]`, as required by the source's subsequent summation over
different `P₁` blocks.  It is not promoted to uniformity in any wider
parameter range.

The internal function `matomakiTeravainenPrimeProductSum` is exactly
`∑_{p₁∼P₁}∑_{x/p₁<n≤(x+h₁)/p₁}ρ⁻(n)`, hence exactly the printed
condition `x<p₁n≤x+h₁`.  The endpoints `X<x≤2X`, the exponent
`h₁=X^(99/100)`, and the denominator
`200 log P₁ log X` are unchanged.  The variable `x` is real, just as in the
source, and the assertion holds for every such `x`; there is no exceptional
set in part (ii).

Equation (2.7) is a later consequence obtained by summing several choices of
`P₁` and introducing a constant `γ`.  It is deliberately not part of the
external field, nor are part (i), part (iii), or any extension beyond
`c=2.1` and the printed `a`-window.

### Normalization of Lemma 3.5(i),(ii)

The Lean fields import exactly the source-scoped versions printed in
[MT23, Lemma 3.5], rather than silently asserting that the original papers'
equations already use MT23's notation.  MT23 states `A,N,N',T≥1`,
`N<N'≤2N`,

```text
N(s) = ∑_{N<n≤N'} n^(-s),       A(s) = ∑_{m∼A} a_m m^(-s),
```

for arbitrary complex coefficients.  Lean encodes the first range by
`natOpenClosedInterval N N'` and the second by `dyadicInterval A`, whose
convention is exactly `A<m≤2A`.  Both conclusions bound

```text
∫_[T/2,T] |N(1+it)|^4 |A(1+it)|^2 dt.
```

For every `ε>0`, one positive constant `C(ε)` is chosen before all four
scales and the coefficient sequence.  This is the fully quantified meaning
of MT23's unadorned `≪ T^ε`; in particular the constant cannot vary with
`A,N,N',T`, or `a`.  Part (i) has right side

```text
C(ε) T^ε ((T + A² T^(1/2))/(N² A) + (T + A)/(T⁴ A))
  max_{m∼A}|a_m|².
```

Part (ii) has right side

```text
C(ε) T^ε
  ((T + A² T^(1/2) + A^(5/4) T^(3/4))/(N² A)
    + (T + A)/(T⁴ A))
  (1/A) ∑_{m∼A}|a_m|².
```

The real integrals are Lebesgue set integrals over `Set.Icc (T/2) T`;
endpoint conventions do not alter their values.  MT23's proof treats
`N≤T` using an approximate functional equation, partial summation, and
[Watt95, (4.7)] or [DI82, (14)], and treats `N>T` using its displayed
equation (3.2) and the standard mean-value theorem.  The Lean assumption is
therefore attributed to MT23's complete normalized lemma while retaining
the two original estimates' precise locators.

### Normalization of Lemma 3.1

The phrase “`ε>0` small enough but fixed” in [MT23, Lemma 3.1] has no
printed numerical cutoff.  Lean therefore records an existential positive
threshold `εₘₐₓ` and assumes the implication only for
`0<ε≤εₘₐₓ`.  It does **not** quantify over every positive `ε`.
Likewise, `c` is definitionally `21/10`, while `a` remains in the printed
interval `[c-1-1/10000,c-1]`.  In particular, the external field cannot be
applied directly to the wider `a,c` range; that range is covered by E1.

The source refers to the already constructed `ρ⁻`.  To avoid turning the
lemma into an unjustified assertion for arbitrary weights, Lean transcribes
the four factorization sums in [MT23, equation (2.3)] with
`z=X^(2/11)`.  The source convention that every `q` is prime is explicit,
and `ρ(n,z)=1_(n,P(z))=1` is represented as the assertion that no prime
below `z` divides the positive integer `n`.

The hypothesis and conclusion each contain `≪`.  These are expanded into a
positive input constant `Cdp` and a positive output constant `Cvar`.
`Cvar` may depend on the fixed `ε`, `a`, and `Cdp`, but neither constant may
vary with `X` or the height `T`.  Source real integrals are represented by
Lebesgue set integrals on `Set.Ioc`; the difference at finitely many endpoints
is null.  These choices expose, rather than enlarge, the source's usual
fixed-parameter interpretation.

### Normalization of Proposition 2.2

The statement “`ε>0` fixed and small enough” is treated in the same way as
for Lemma 3.1: there is an existential positive threshold and the proposition
is assumed only for `0<ε≤εmax`.  For each fixed `ε` and `A≥5`, `Cfamily`,
`Cremainder`, `Bcoeff`, and `Acoeff` are chosen before `X,Y`.
Consequently neither the analytic constants nor the coefficient exponent or
coefficient constant may vary with the principal scale or with the selected
family member.

The source's `n∼N` convention remains `(N,2N]`, while each short
`δ_A`-adic interval remains `(N,(1+δ_A)N]`.  The Type-II tuple indexed in
the paper by `1,…,R` is represented by `Fin R`; its coefficient is literally
the cardinality of ordered prime tuples satisfying
`Q_j<q_j≤Q_j(1+δ_A)` and `q₁⋯q_R=m`.  This preserves ordering and
multiplicity rather than replacing (2.11) by a support-only condition.

Since the printed family consists of functions `f : ℕ → ℂ`, Lean embeds
the real minorant into `ℂ` in the decomposition identity and takes the
complex norm in (2.10).  The remainder support makes the finite sum over
`(Y/4,8Y]` exactly the source's unrestricted `∑_n |c_n|²`.

### Normalization of Lemma 3.2

The direct field `iwaniecKowalskiTheoremNineOne` has the exact
source-scoped form printed as [MT23, Lemma 3.2], which MT23 cites to
[IK04, Theorem 9.1].  For real `N,T≥1` and arbitrary complex coefficients,
Lean uses

```text
A(s) = ∑_{0<n≤N} a_n n^(-s),
S    = ∑_{0<n≤N} |a_n|²,
I    = ∫_[-T,T] |A(it)|² dt.
```

The source writes `I=(2T+O(N))S`.  Rather than treating `O(N)` as an
uninterpreted symbol, Lean quantifies one positive absolute constant `C`
before `N,T,a` and assumes the equivalent explicit estimate

```text
|I - 2 T S| ≤ C N S.
```

Thus the error constant is independent of the polynomial length, integration
height, and coefficient sequence.  The integral is represented by a
Lebesgue set integral over `Set.Icc (-T) T` and the polynomial is evaluated
at `(t:ℂ)·I`, exactly the source's zero-line normalization; changing the two
endpoint conventions is measure-theoretically immaterial.

### Normalization of Lemma 3.3

The source writes a finite vector `(a_n)_{n≤N}` and then uses `a_{n+k}` for
positive and negative integer shifts.  Lean makes the standard implicit
convention explicit by extending that vector by zero outside the integer
interval `[1,N]`.  Consequently its finite shift set
`{-⌊N/T⌋,…,-1,1,…,⌊N/T⌋}` is exactly the printed condition
`0<|k|≤N/T`, without assigning a value to a coefficient with a nonpositive
index.

The source's real integral is represented by a Lebesgue set integral over
`Set.Icc (-T) T`, and `A(it)` is evaluated at `(t:ℂ)·I`; this is a direct
formal encoding rather than a change of line or interval.  The unadorned
`≪` becomes one positive absolute constant chosen before `N,T,a`.  No
coefficient boundedness or support sparsity hypothesis is added.

MT23's one-line proof cites [IK04, Lemma 7.1] with `Y=10T` and
`x_m=(2π)⁻¹log m`.  The external field is deliberately the exact resulting
MT23 lemma.  A future formalization of the book lemma and its substitution
could discharge this field internally, but the current trust boundary does
not assert that [IK04, Lemma 7.1] already has the MT23 normalization.

## Normalization of the sparse mean-value lemma

The typed assumption is exactly the source-scoped form in [MT23, Lemma 3.4],
not a silent attribution of that form to [HB18, Theorem 4(iii)].  Heath-Brown
works on the zero line and integrates over `[0,T]`.  Matomäki--Teräväinen
pass to the line `Re(s)=1` by replacing the sparse coefficients by
`εₘ M/m` and the dyadic coefficients by `aₙ N/n`; they use symmetry to
replace `[0,T]` by `[-T,T]`, split a real signed coefficient into positive
and negative parts, and invoke Heath-Brown with `η/2`.  Those published
normalization steps are therefore inside the cited MT23 lemma and are not
new Lean assumptions.

Lean represents the source integral over `[-T,T]` as a Lebesgue set integral
over `Set.Icc (-T) T`; changing endpoint conventions has no effect.  The
source quantity `max_{n∼N}|aₙ|` is represented by the finite `NNReal`
supremum over `dyadicInterval N`, whose convention is `N < n ≤ 2N`.
The hypothesis `N ≥ 2` ensures that this range is nonempty.  The general
bound and the improved bound are packaged using one positive constant
`C(η)`.  This does not strengthen the two `≪_η` assertions: one may take
the maximum of their two implied constants.

## Composite consequences that are not assumptions

The following deductions are proved in Lean, not assumed: the upgrade of the
fixed-`a` Hildebrand--Tenenbaum consequence to a bound uniform over a window
of `a` (`Final/SparseUniform.lean`); the length-dependent Guth--Maynard
density estimate (Lemma 4.3, `Hybrid/RefinedDensity.lean`); the complete
sparse (Section 6) and Type II (Proposition 5.1) arguments; the three-case
treatment of the medium bins (`Final/TypeIIDensityBins.lean`); the Type II
component bound on `𝒰` uniformly in the block (`Final/TypeIIComponent.lean`);
the complement-of-`𝒰` bound from [MT23, Lemma 3.3], equation (2.4) and E3
(`Final/ComplementU.lean`); the high-frequency range `T ≥ X` from the mean
value theorem [IK04, Theorem 9.1] and the coefficient bound `5324`
(`Final/PerronTail.lean`); the assembly of the decomposition of
[MT23, Proposition 2.2] into the Dirichlet-polynomial target of
Proposition 7.1 (`Final/DirichletTarget.lean`); the variance bound of
Proposition 7.1 (`Final/BlockVariance.lean`); and Section 7.2
(`Final/Counting.lean`, `Final/Assembly.lean`).

The Type-I and Type-I/II estimates from [DI82] and [Watt95], the rough-pair
sieve adaptation of [IK04, Theorem 6.7], and the extensions of cited
statements beyond their printed ranges are exactly the labelled extensions
E1--E5.  The smooth short-segment projector from Harman's Lemma 1.5 to
[MT23, (5.6)] and the upper-tail control in `Sparse/Propagation.lean` belong
to alternative routes; the main theorem uses the cited equation (5.6)
directly and needs neither.

There is no assumption called elementarySieveMeanSquare,
matomakiTeravainenStructuredCoefficients, or
vinogradovKorobovStructuredFactor.

## Mathlib and local proof obligations

The following are not external analytic assumptions; they are proved from
Mathlib or locally:

- Cauchy--Schwarz and finite-sum inequalities;
- Chebyshev/Markov exceptional-set bounds, including the exact loss of two
  logarithmic powers in the paper's substitution;
- the needed factorial estimate (proved by `k!≤k^k`, so Stirling is not
  required for this step) and elementary logarithmic asymptotics;
- exact rational inequalities such as `3688/1763 < 2.092` and
  `1.0919 - 1925/1763 = 197/17630000`;
- maximal one-spaced covering and the discrete-to-measure passage;
- the subpower bound for a fixed power of the divisor function;
- dyadic block construction, counting, endpoint summation, and
  real-to-integer exceptional-set conversion.

## New results that must not be assumed

The genuinely new mathematics of the paper is proved in Lean, not assumed:

- the length-dependent Guth--Maynard density estimate (Lemma 4.3,
  `Hybrid/RefinedDensity.lean`) and the Type II estimate with threshold
  `σ* = 17/70 - O(ε)` (Proposition 5.1, `TypeII/`, `Hybrid/`);
- the sparse Heath-Brown branches (Section 6, `Sparse/`);
- the three-case treatment of the medium bins and the budget
  `a > 1925/1763` (Section 6, `Final/TypeIIDensityBins.lean`);
- the Type II component bound uniformly over the blocks
  (`Final/TypeIIComponent.lean`);
- Proposition 7.1 for every `3688/1763 < c ≤ 2.1`
  (`Final/DirichletTarget.lean`, `Final/BlockVariance.lean`), given E1;
- Section 7.2 and Theorems 1.2/1.3 (`Final/Assembly.lean`,
  `Results/ParameterTheorem.lean`, `Results/CleanTheorem.lean`).

The published Matomäki--Teräväinen final exponent-2.1 conclusion and its
variance statement, Theorem 2.1(iii), are not premises of the new result.
The comparison `3688/1763 < 67/32 < 2.1` is checked in
`Results/ExplicitExponentArithmetic.lean`.

## Bibliography

**[DI82]** J.-M. Deshouillers and H. Iwaniec, “Power mean values of
the Riemann zeta-function,” *Mathematika* **29** (1982), no. 2,
202--212. Equation (14).
https://doi.org/10.1112/S0025579300012298

**[GM26]** Larry Guth and James Maynard, “New large value estimates
for Dirichlet polynomials,” *Annals of Mathematics* (2) **203** (2026),
no. 2, 623--675. Theorem 1.1 and Proposition 12.1.
https://doi.org/10.4007/annals.2026.203.2.6
Preprint: https://arxiv.org/abs/2405.20552

**[Harman07]** Glyn Harman, *Prime-Detecting Sieves*, London
Mathematical Society Monographs Series, vol. 33, Princeton University
Press, Princeton, 2007. Lemma 1.5, p. 14. ISBN 978-0-691-12437-7.

**[HB18]** D. R. Heath-Brown, “The Differences Between Consecutive
Smooth Numbers,” *Acta Arithmetica* **184** (2018), no. 3, 267--285.
Theorem 4(iii). https://doi.org/10.4064/aa170913-11-7
Preprint: https://arxiv.org/abs/1808.02947

**[HT86]** Adolf Hildebrand and Gérald Tenenbaum, “On integers free of
large prime factors,” *Transactions of the American Mathematical
Society* **296** (1986), no. 1, 265--290. Theorems 1--2.
https://doi.org/10.1090/S0002-9947-1986-0837811-1

**[HT93]** Adolf Hildebrand and Gérald Tenenbaum, “Integers without
large prime factors,” *Journal de Théorie des Nombres de Bordeaux*
**5** (1993), no. 2, 411--484. Corollary 1.3 and equation (1.14).
https://doi.org/10.5802/jtnb.101

**[IK04]** Henryk Iwaniec and Emmanuel Kowalski, *Analytic Number
Theory*, American Mathematical Society Colloquium Publications,
vol. 53, American Mathematical Society, Providence, RI, 2004.
Lemmas/Theorems 7.1, 6.7, 9.1, 9.4 (p. 233), and 9.6 (p. 234).
https://doi.org/10.1090/coll/053

**[LT17]** Florian Luca and László Tóth, “The rth Moment of the
Divisor Function: An Elementary Approach,” *Journal of Integer
Sequences* **20** (2017), Article 17.7.4. Theorem 1.
https://cs.uwaterloo.ca/journals/JIS/VOL20/Luca/luca42.pdf
Preprint: https://arxiv.org/abs/1703.08785

**[Mer74]** Franz Mertens, “Ein Beitrag zur analytischen
Zahlentheorie,” *Journal für die reine und angewandte Mathematik*
**78** (1874), 46--62.
https://doi.org/10.1515/crll.1874.78.46

**[MR16]** Kaisa Matomäki and Maksym Radziwiłł, “Multiplicative
functions in short intervals,” *Annals of Mathematics* **183** (2016),
no. 3, 1015--1056. Lemma 14.
https://doi.org/10.4007/annals.2016.183.3.6

**[MT23]** Kaisa Matomäki and Joni Teräväinen, “Almost primes in
almost all short intervals II,” *Transactions of the American
Mathematical Society* **376** (2023), no. 8, 5433--5459. Theorem 2.1,
Proposition 2.2, Lemmas 3.1--3.5, and equation (5.6).
https://doi.org/10.1090/tran/8869
Preprint: https://arxiv.org/abs/2207.05038

**[Ter16]** Joni Teräväinen, “Almost primes in almost all short
intervals,” *Mathematical Proceedings of the Cambridge Philosophical
Society* **161** (2016), no. 2, 247--281. Lemma 1.
https://doi.org/10.1017/S0305004116000232
Preprint: https://arxiv.org/abs/1510.06005

**[Watt95]** Nigel Watt, “Kloosterman sums and a mean value for
Dirichlet polynomials,” *Journal of Number Theory* **53** (1995),
no. 1, 179--210. Equation (4.7).
https://doi.org/10.1006/jnth.1995.1086
