import ExactSemiprimes.Completion.GeneralPerronReduction
import ExactSemiprimes.Sparse.GlobalComponentCancellation

/-!
# Labelled parameter extensions of published results

`Assumptions.lean` contains verbatim transcriptions of published theorems.
Several of the Matomäki--Teräväinen inputs are printed only at the single
interval exponent `c = 2.1` and in the narrow window `a ∈ [1.0999, 1.1]`.
The new paper needs the *same* statements for a wider range of the
logarithmic exponents `a` (the size of the small prime `P₁ = (log X)^a`) and
`c` (the interval length `h = (log X)^c`).  The published proofs never use the
numerical values of `a, c` beyond the displayed power checks.

The fields of `ParameterExtensionInputs` below record exactly those
extensions.  **They are not verbatim published statements.**  Each one is a
uniform-in-parameters version of a published lemma whose printed proof
applies unchanged; they are explicitly labelled assumptions.  Every field names the source whose proof is
being extended.  See `ASSUMPTIONS.md`, section "Parameter extensions".

* `generalParsevalReduction` — the Parseval/Perron lemma
  [MR16, Lemma 14] in the general form of [Ter16, Lemma 1] (arbitrary lower
  cutoff `T₀`, real coefficients bounded by `K`), as used in
  [MT23, Lemma 3.1].
* `uniformLongIntervalMinorant` — [MT23, Theorem 2.1(ii)] uniformly for
  `1 ≤ a ≤ 11/10`.
* `uniformRoughPairSieve` — the displayed rough-pair estimate of
  [MT23, Section 5, p. 16] uniformly for `1 ≤ a ≤ c - 1`, `c ≤ 2.1`.
* `uniformTypeIComponent` — the Type I bound [MT23, Section 5.1] for
  every `a ∈ [1925/1763, 11/10]`; the paper checks the only `a`-dependent
  exponent: `(1-1/a)/4 ≥ 81/3850 > 1/50`.
* `uniformTypeIOneHalfComponent` — the Type I/II bound [MT23, Section 5.2]
  for every `a ∈ [1925/1763, 11/10]`.

None of these concerns the new large-value input: the Type II components,
which carry the improvement from `2.1` to `3688/1763`, are proved in Lean from
the verbatim inputs (Guth--Maynard, Heath-Brown, Hildebrand--Tenenbaum,
MT23 equation (5.6), ...).
-/

namespace ExactSemiprimes

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The large-prime set `𝒰` of [MT23, Section 5] and of the paper,
Section 3: heights `t ∈ [X^(1/1000), X]` at which the prime polynomial
`P₁(1+it) = ∑_{P<p≤2P} p^(-1-it)` is at least `P^(-ε/10)`. -/
def largePrimeValueSet (X P ε : ℝ) : Set ℝ :=
  Set.Icc (X ^ (1 / 1000 : ℝ)) X ∩
    {t : ℝ | P ^ (-ε / 10) ≤ ‖primeDirichletPolynomial P (onePlusIT t)‖}

/-- The quantity `exp(-(log log X)^6)` on the right of [MT23, (5.1)] and the
component target in Section 3 of the paper. -/
def loglogSixSaving (X : ℝ) : ℝ :=
  Real.exp (-((Real.log (Real.log X)) ^ (6 : ℕ)))

/-! ## (E1) The general Parseval / Perron reduction -/

/-- **Extension (E1).**  [MR16, Lemma 14] in the generality of
[Ter16, Lemma 1] and [MT23, Lemma 3.1].

For real coefficients `w`, a prime block `(P,2P]` and the product polynomial
`A(s) = (∑_{P<p≤2P} p^(-s)) (∑_{X/(2P)<n≤4X/P} w(n) n^(-s))` whose
coefficients are bounded by `K`, and for `1 ≤ h ≤ h₂ ≤ X/T₀³`,

`(1/X) ∫_X^{2X} |S_h(x)/h - S_{h₂}(x)/h₂|² dx ≪ K²/T₀ + ∫_{T₀}^{X/h} |A(1+it)|² dt
   + max_{T ≥ X/h} (X/(T h)) ∫_T^{2T} |A(1+it)|² dt`,

with an absolute implied constant.  The maximum is written with explicit
upper bounds `Bmiddle, Btail`.  MR16 prints the case `|a_m| ≤ 1`,
`T₀ = (log X)^(1/15)`, `h₂ = X/(log X)^(1/5)`; the proof (Perron's formula,
low frequencies via `|t| h₂/X ≤ 1/T₀²`, high frequencies via a Plancherel
bound) is the same for general `T₀`, and homogeneity gives the factor `K²`. -/
def GeneralParsevalReductionStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (w : ℕ → ℝ) (X P h hlong T₀ K : ℝ),
      3 ≤ X → 1 ≤ P → 1 ≤ T₀ → 1 ≤ h → h ≤ hlong →
      hlong ≤ X / T₀ ^ (3 : ℕ) → T₀ ≤ X / h → 0 ≤ K →
      (∀ m ∈ Completion.perronProductSupport X P,
        ‖Completion.perronProductCoefficient w X P m‖ ≤ K) →
      ∀ Bmiddle Btail : ℝ,
        (∫ t in Set.Ioc T₀ (X / h),
            ‖Completion.perronProduct w X P t‖ ^ (2 : ℕ)) ≤ Bmiddle →
        (∀ T : ℝ, X / h ≤ T →
          X / (T * h) *
            (∫ t in Set.Ioc T (2 * T),
              ‖Completion.perronProduct w X P t‖ ^ (2 : ℕ)) ≤ Btail) →
        matomakiTeravainenShortLongVariance w X P h hlong ≤
          C * (K ^ (2 : ℕ) / T₀ + Bmiddle + Btail)

/-! ## (E2) The long-interval lower bound, uniformly in `a` -/

/-- **Extension (E2).**  [MT23, Theorem 2.1(ii)] uniformly for
`1 ≤ a ≤ 11/10`.  The printed statement is the same with
`a ∈ [1.0999, 1.1]`; its proof (Buchstab decomposition of the minorant
on the long interval `h₁ = X^(99/100)` and Mertens' theorem for
`∑_{p∼P₁} 1/p`) uses only that `P₁` is a fixed power of `log X`. -/
def UniformLongIntervalMinorantStatement : Prop :=
  ∃ εₘₐₓ : ℝ, 0 < εₘₐₓ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∃ X₀ : ℝ, 3 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          let h₁ : ℝ := X ^ (99 / 100 : ℝ)
          ∀ a : ℝ, 1 ≤ a → a ≤ 11 / 10 →
            let P₁ : ℝ := (Real.log X) ^ a
            ∀ x : ℝ, X < x → x ≤ 2 * X →
              h₁ / (200 * Real.log P₁ * Real.log X) ≤
                matomakiTeravainenPrimeProductSum
                  (matomakiTeravainenMinorant X ε) P₁ x h₁

/-! ## (E3) The rough-pair sieve bound, uniformly in `a, c` -/

/-- **Extension (E3).**  The displayed estimate of [MT23, Section 5, p. 16]
(an upper-bound sieve for pairs of `X^(2/11)`-rough numbers, cf.
[IK04, Theorem 6.7]) uniformly for `1 ≤ a ≤ c - 1` and `c ≤ 2.1`.  The
printed version has `c = 2.1`, `a ∈ [1.0999, 1.1]`. -/
def UniformSectionFiveRoughSieveStatement : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧
    ∀ X a c T : ℝ, X₀ ≤ X →
      1 ≤ a → a ≤ c - 1 → c ≤ 21 / 10 →
      X / (Real.log X) ^ c ≤ T → T ≤ X →
      let P₁ : ℝ := (Real.log X) ^ a
      let N : ℝ := 4 * X / P₁
      let b := matomakiTeravainenSectionFiveRoughCoefficient X P₁
      T * (∑ n ∈ natOpenClosedInterval 0 N, ‖b n‖ ^ (2 : ℕ)) +
          T * matomakiTeravainenShiftedCorrelation b N T ≤
        C * (T * P₁ / (X * Real.log X) + 1 / (Real.log X) ^ (2 : ℕ))

/-! ## (E4) Type I components -/

/-- **Extension (E4).**  The Type I estimate [MT23, Section 5.1]: for a
Type I convolution from [MT23, Proposition 2.2(i)] at `Y = X/P₁`,
`∫_𝒰 |P₁(1+it) F(1+it)|² dt ≪ exp(-(log log X)^6)`, uniformly for
`P₁ ∈ [(log X)^(1925/1763), (log X)^(11/10)]`.  The printed argument (insertion
of a power of `P₁` of length `T^(1/10)`, Cauchy--Schwarz, the
Deshouillers--Iwaniec twisted fourth moment [MT23, Lemma 3.5(ii)]) leaves
`P₁ L^(-(1-1/a)/2) X^(O(ε)) ≪ X^(-(1-1/a)/20+O(ε))`; the paper's
Section 7.1 checks this is a power saving for `a ≥ 1925/1763`. -/
def UniformTypeIComponentStatement : Prop :=
  ∃ εₘₐₓ : ℝ, 0 < εₘₐₓ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∀ A : ℝ, 5 ≤ A →
        ∀ Bcoeff Acoeff : ℝ, 0 ≤ Bcoeff → 1 ≤ Acoeff →
          ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧
            ∀ X P : ℝ, X₀ ≤ X →
              (Real.log X) ^ (1925 / 1763 : ℝ) ≤ P →
              P ≤ (Real.log X) ^ (11 / 10 : ℝ) →
              ∀ (M₁ M₂ : ℝ) (α : ℕ → ℂ),
                0 < M₁ → 0 < M₂ →
                IsDivisorBoundedByConstant Bcoeff Acoeff α →
                M₁ ≤ X ^ (1 / 2 + ε) →
                X / P / 2 < M₁ * M₂ → M₁ * M₂ ≤ 4 * (X / P) →
                (∫ t in largePrimeValueSet X P ε,
                    ‖primeDirichletPolynomial P (onePlusIT t)‖ ^ (2 : ℕ) *
                      ‖dirichletPolynomial
                          (matomakiTeravainenTypeIValue
                            ((Real.log X) ^ (-10 * A)) M₁ M₂ α)
                          (Sparse.typeIProductSupport
                            ((Real.log X) ^ (-10 * A)) M₁ M₂)
                          (onePlusIT t)‖ ^ (2 : ℕ)) ≤
                  C * loglogSixSaving X

/-! ## (E5) Type I/II components -/

/-- **Extension (E5).**  The Type I/II estimate [MT23, Section 5.2] for a
convolution from [MT23, Proposition 2.2(ii)] at `Y = X/P₁`, uniformly for
`P₁ ∈ [(log X)^(1925/1763), (log X)^(11/10)]`.  The printed argument
(insertion of a power of `P₁` of length `T^(ε/2)`, Watt's twisted fourth
moment [MT23, Lemma 3.5(i)]) leaves
`P₁ X^(-ε(1-1/a)/4+ε/100+O(ε²))`; the paper checks
`(1-1/a)/4 ≥ 81/3850 > 1/100` for `a ≥ 1925/1763`. -/
def UniformTypeIOneHalfComponentStatement : Prop :=
  ∃ εₘₐₓ : ℝ, 0 < εₘₐₓ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∀ A : ℝ, 5 ≤ A →
        ∀ Bcoeff Acoeff : ℝ, 0 ≤ Bcoeff → 1 ≤ Acoeff →
          ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧
            ∀ X P : ℝ, X₀ ≤ X →
              (Real.log X) ^ (1925 / 1763 : ℝ) ≤ P →
              P ≤ (Real.log X) ^ (11 / 10 : ℝ) →
              ∀ (M₁ M₂ M₃ : ℝ) (α β : ℕ → ℂ),
                0 < M₁ → 0 < M₂ → 0 < M₃ →
                IsDivisorBoundedByConstant Bcoeff Acoeff α →
                IsDivisorBoundedByConstant Bcoeff Acoeff β →
                M₁ ^ (2 : ℕ) * M₂ ≤ X ^ (1 - ε) →
                M₂ ≤ X ^ (1 / 4 - ε) →
                X / P / 2 < M₁ * M₂ * M₃ → M₁ * M₂ * M₃ ≤ 4 * (X / P) →
                (∫ t in largePrimeValueSet X P ε,
                    ‖primeDirichletPolynomial P (onePlusIT t)‖ ^ (2 : ℕ) *
                      ‖dirichletPolynomial
                          (matomakiTeravainenTypeIOneHalfValue
                            ((Real.log X) ^ (-10 * A)) M₁ M₂ M₃ α β)
                          (Sparse.typeIOneHalfProductSupport
                            ((Real.log X) ^ (-10 * A)) M₁ M₂ M₃)
                          (onePlusIT t)‖ ^ (2 : ℕ)) ≤
                  C * loglogSixSaving X

/-- The labelled parameter extensions.  As with `ExternalInputs`, no global
inhabitant is postulated: every theorem using them takes an explicit
hypothesis of this type. -/
structure ParameterExtensionInputs : Prop where
  generalParsevalReduction : GeneralParsevalReductionStatement
  uniformLongIntervalMinorant : UniformLongIntervalMinorantStatement
  uniformRoughPairSieve : UniformSectionFiveRoughSieveStatement
  uniformTypeIComponent : UniformTypeIComponentStatement
  uniformTypeIOneHalfComponent : UniformTypeIOneHalfComponentStatement

def extensionsModule : ProofModule :=
  { name := "Extensions"
    paperLocation := "Section 7 (unchanged portions of [MT23], wider parameters)"
    purpose :=
      "Record, as explicitly labelled assumptions, the uniform-in-(a,c) versions of the MT23 Perron reduction, long-interval bound, rough-pair sieve, and Type I and Type I/II component bounds."
    dependsOn := ["Assumptions", "Completion.GeneralPerronReduction"]
    status := .externalAssumption }

end

end ExactSemiprimes
