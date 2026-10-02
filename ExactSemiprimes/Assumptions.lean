import ExactSemiprimes.Definitions

/-!
# Cited external assumptions

The formalization is proving the new argument conditionally on exact
statements imported from the published literature.  Every field below names a
specific theorem, proposition, lemma, corollary, or displayed estimate.
Paper-specific adaptations and combinations remain internal proof obligations.

All source inputs have faithful quantified Lean statements.  The
Vinogradov--Korobov estimate used at [MT23, equation (5.6)] is recorded in
its paper-specific structured-coefficient form: it is not inferred from a
weaker full-dyadic prime-polynomial estimate.  Iwaniec--Kowalski's fixed
prime-tuple upper-bound sieve does not by itself imply the paper-specific
rough-pair estimate for which [MT23] cites a related argument; that
adaptation remains an internal proof obligation.
There is no global axiom asserting that the assumption bundle is inhabited:
every eventual result must receive an explicit `ExternalInputs` hypothesis.

Elementary deductions intended to be proved from Mathlib--including
Cauchy--Schwarz, Chebyshev/Markov, Stirling, elementary rational arithmetic,
and local sampling arguments--are intentionally absent from this file.
-/

namespace ExactSemiprimes

/-! ## Guth--Maynard inputs -/

/-- [GM26, Theorem 1.1], with the paper's `T^{o(1)}` written out as
`∀ ε > 0, ∃ C > 0`.  The coefficient support is the source's closed
interval `[N,2N]`, not the half-open dyadic range `(N,2N]`. -/
def GuthMaynardMainLargeValuesStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (T V : ℝ) (N : ℕ) (b : ℕ → ℂ) (R : Finset ℝ),
      1 ≤ T → 1 ≤ N → 0 < V →
      (∀ n ∈ closedDyadicInterval N, ‖b n‖ ≤ 1) →
      (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
      IsOneSpaced (↑R : Set ℝ) →
      (∀ t ∈ R, V ≤ ‖oscillatoryDirichletSum b N t‖) →
      (R.card : ℝ) ≤ C * T ^ ε *
        (((N : ℝ) ^ (2 : ℕ)) / V ^ (2 : ℕ) +
          (N : ℝ) ^ (18 / 5 : ℝ) / V ^ (4 : ℕ) +
          T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ (4 : ℕ))

/-- The displayed “in particular” consequence of [GM26,
Proposition 12.1].  The relation `R ≲ B` is again expanded into an
arbitrary factor `T^ε` with a corresponding constant. -/
def GuthMaynardLongPolynomialStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (T V ρ : ℝ) (N : ℕ) (b : ℕ → ℂ) (R : Finset ℝ),
      1 ≤ T → 1 ≤ N → 0 < V →
      T ^ (5 / 6 : ℝ) ≤ (N : ℝ) → (N : ℝ) ≤ T →
      7 / 10 ≤ ρ → V = (N : ℝ) ^ ρ →
      (∀ n ∈ closedDyadicInterval N, ‖b n‖ ≤ 1) →
      (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
      IsOneSpaced (↑R : Set ℝ) →
      (∀ t ∈ R, V ≤ ‖oscillatoryDirichletSum b N t‖) →
      (R.card : ℝ) ≤ C * T ^ ε *
        ((N : ℝ) ^ (2 - 2 * ρ) +
          T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * ρ) +
          T ^ ((30 * ρ - 21) / 5) *
            (N : ℝ) ^ ((46 - 60 * ρ) / 5))

/-! ## Classical prime-sum input -/

/-- [Mer74], Mertens' second theorem, expressed along natural cutoffs. -/
def MertensSecondTheoremStatement : Prop :=
  ∃ meisselMertensConstant : ℝ,
    Filter.Tendsto
      (fun X : ℕ ↦ reciprocalPrimeSum X - Real.log (Real.log (X : ℝ)))
      Filter.atTop (nhds meisselMertensConstant)

/-! ## Fixed moments of the divisor function -/

/-- [Luca--Tóth 2017, Theorem 1], specialized to
`f(n) = tau(n)^r`.  For every fixed integer `r ≥ 2`, the `r`-th moment of
the divisor function has a positive main term of logarithmic degree
`2^r-1`, with an error one logarithmic degree smaller.

The source's `O_r` is expanded into a positive constant and a starting
point chosen after `r`.  The finite interval `natOpenClosedInterval 0 x`
is exactly the set of positive integers `n ≤ x`.  This source statement is
used only to derive, locally, the polylogarithmic coefficient energy needed
in the Halasz--Montgomery part of Proposition 5.1. -/
def LucaTothTheoremOneStatement : Prop :=
  ∀ r : ℕ, 2 ≤ r →
    ∃ Cᵣ E x₀ : ℝ,
      0 < Cᵣ ∧ 0 < E ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        |(∑ n ∈ natOpenClosedInterval 0 x,
              (divisorCount n : ℝ) ^ r) -
            x * Cᵣ * (Real.log x) ^ (2 ^ r - 1)| ≤
          E * x * (Real.log x) ^ (2 ^ r - 2)

/-! ## Smooth-number input -/

/-- A direct fixed-`a` consequence of [HT93, Corollary 1.3 and equation
(1.14)], specialized to `y=(log x)^a`.  Taking logarithms makes the
`x^(1-1/a+o(1))` assertion a literal limit.  This is fully quantified; it is
the standard consequence of the source corollary rather than a verbatim
transcription of it. -/
def HildebrandTenenbaumCorollaryOneThreeStatement : Prop :=
  ∀ a : ℝ, 1 < a →
    Filter.Tendsto
      (fun X : ℕ ↦
        Real.log (logPowerSmoothNumberCount a X : ℝ) /
          Real.log (X : ℝ))
      Filter.atTop (nhds (1 - 1 / a))

/-! ## Heath--Brown sparse mean-value input -/

/-- The finite maximum `max_{n ∼ N} |aₙ|` in [MT23, Lemma 3.4].  The
`NNReal` supremum gives value zero on an empty range; the source hypothesis
`N ≥ 2` makes the relevant dyadic range nonempty. -/
noncomputable def dyadicRealCoefficientSup (a : ℕ → ℝ) (N : ℝ) : ℝ :=
  ↑((dyadicInterval N).sup fun n ↦ Real.toNNReal |a n|)

/-- [MT23, Lemma 3.4], Heath--Brown's sparse mean-value estimate, including
the final clause that deletes the `|ℳ|^(7/4) T^(3/4)` term.  The theorem is
stated on the source's line `Re(s)=1`, over `[-T,T]`, for a finite set of
integers `ℳ ⊆ [M,T]`, complex coefficients `εₘ` of modulus at most one,
and real coefficients `aₙ` on `n ∼ N`.

The notation `≪_η` is expanded as a positive constant depending only on
`η`, quantified before every other parameter.  The underlying result is
[HB18, Theorem 4(iii)]; the changes from its zero-line normalization to this
source-scoped statement are carried out in the published proof of [MT23,
Lemma 3.4]. -/
def MatomakiTeravainenLemmaThreeFourStatement : Prop :=
  ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 < C ∧
    ∀ (T M N : ℝ) (ℳ : Finset ℕ) (ε : ℕ → ℂ) (a : ℕ → ℝ),
      1 ≤ M → M ≤ T → 2 ≤ N →
      (∀ m ∈ ℳ, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ T) →
      (∀ m ∈ ℳ, ‖ε m‖ ≤ 1) →
      let I : ℝ := ∫ t in Set.Icc (-T) T,
        ‖dirichletPolynomial ε ℳ (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖dyadicDirichletPolynomial (fun n ↦ (a n : ℂ)) N
            (onePlusIT t)‖ ^ (2 : ℕ)
      let R : ℝ := (ℳ.card : ℝ)
      let A₀ : ℝ := dyadicRealCoefficientSup a N
      I ≤ C *
          ((R / M) ^ (2 : ℕ) +
            (N * T) ^ η *
              (R * T / (M ^ (2 : ℕ) * N) +
                R ^ (7 / 4 : ℝ) * T ^ (3 / 4 : ℝ) /
                  (M ^ (2 : ℕ) * N))) *
          A₀ ^ (2 : ℕ) ∧
        (N ≥ T ^ (2 / 3 : ℝ) ∨ R ≤ T ^ (1 / 3 : ℝ) →
          I ≤ C *
            ((R / M) ^ (2 : ℕ) +
              (N * T) ^ η * (R * T / (M ^ (2 : ℕ) * N))) *
            A₀ ^ (2 : ℕ))

/-! ## Matomäki--Teräväinen's printed Perron reduction -/

/-- The source's roughness indicator `ρ(n,z)=1_(n,P(z))=1`.  It is written
without constructing the large finite product `P(z)`: a positive integer is
counted precisely when no prime below `z` divides it. -/
noncomputable def matomakiTeravainenRoughIndicator (n : ℕ) (z : ℝ) : ℝ := by
  classical
  exact if ∀ p : ℕ, p.Prime → (p : ℝ) < z → ¬p ∣ n then 1 else 0

/-- The exact four-term Harman minorant `ρ⁻` from [MT23, equation (2.3)],
with `z=X^(2/11)`.  As throughout the source, every variable named `q` is
prime.  For positive `n`, each complementary factor `m` is uniquely `n/q`,
`n/(q₁q₂)`, or `n/(q₁q₂q₃)`, so the finite divisor sums below are
the displayed factorization sums in (2.3). -/
noncomputable def matomakiTeravainenMinorant
    (X ε : ℝ) (n : ℕ) : ℝ := by
  classical
  let z : ℝ := X ^ (2 / 11 : ℝ)
  let rough : ℕ → ℝ := fun m ↦ matomakiTeravainenRoughIndicator m z
  let qs := Finset.range (n + 1)
  exact rough n -
      (∑ q ∈ qs,
        if q.Prime ∧ z ≤ (q : ℝ) ∧
            (q : ℝ) < 2 * X ^ (1 / 2 : ℝ) ∧ q ∣ n then
          rough (n / q)
        else 0)
    + (∑ q₁ ∈ qs, ∑ q₂ ∈ qs,
        if q₁.Prime ∧ q₂.Prime ∧
            z ≤ (q₂ : ℝ) ∧ (q₂ : ℝ) < (q₁ : ℝ) ∧
            (q₁ : ℝ) < X ^ (1 / 4 - 2 * ε) ∧
            (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) < X ^ (1 - 2 * ε) ∧
            q₁ * q₂ ∣ n then
          rough (n / (q₁ * q₂))
        else 0)
    - (∑ q₁ ∈ qs, ∑ q₂ ∈ qs, ∑ q₃ ∈ qs,
        if q₁.Prime ∧ q₂.Prime ∧ q₃.Prime ∧
            z ≤ (q₃ : ℝ) ∧ (q₃ : ℝ) < (q₂ : ℝ) ∧
            (q₂ : ℝ) < (q₁ : ℝ) ∧
            (q₁ : ℝ) < X ^ (1 / 4 - 2 * ε) ∧
            (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) < X ^ (1 - 2 * ε) ∧
            q₁ * q₂ * q₃ ∣ n then
          rough (n / (q₁ * q₂ * q₃))
        else 0)

/-- [MT23, equation (2.4)], the pointwise domination of the four-term
Harman minorant by the indicator of integers with no prime factor below
`z=X^(2/11)`.  The source first fixes a sufficiently small positive
`epsilon`; this is represented by an explicit positive threshold.  The
constant in the displayed inequality and the full interval on which the
minorant is constructed are retained verbatim. -/
def MatomakiTeravainenEquationTwoFourStatement : Prop :=
  ∃ εₘₐₓ : ℝ, 0 < εₘₐₓ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∀ X : ℝ, 3 ≤ X →
        ∀ n : ℕ,
          2 * X ^ (1 / 2 : ℝ) ≤ (n : ℝ) → (n : ℝ) ≤ 3 * X →
            |matomakiTeravainenMinorant X ε n| ≤
              4 * (Real.log (3 * X) /
                Real.log (X ^ (2 / 11 : ℝ))) ^ (3 : ℕ) *
                matomakiTeravainenRoughIndicator n
                  (X ^ (2 / 11 : ℝ))

/-- The weighted `p₁ n` sum in [MT23, Theorem 2.1 and Lemma 3.1]. -/
noncomputable def matomakiTeravainenPrimeProductSum
    (weight : ℕ → ℝ) (P x h : ℝ) : ℝ :=
  ∑ p ∈ dyadicPrimes P,
    ∑ n ∈ shortInterval (x / (p : ℝ)) (h / (p : ℝ)), weight n

/-- The left side of [MT23, equation (2.6)], including its outer `1/X`. -/
noncomputable def matomakiTeravainenShortLongVariance
    (weight : ℕ → ℝ) (X P h h₁ : ℝ) : ℝ :=
  (1 / X) * ∫ x in Set.Ioc X (2 * X),
    |matomakiTeravainenPrimeProductSum weight P x h / h -
      matomakiTeravainenPrimeProductSum weight P x h₁ / h₁| ^ (2 : ℕ)

/-- The mean square in the hypothesis of [MT23, Lemma 3.1]. -/
noncomputable def matomakiTeravainenPerronIntegral
    (weight : ℕ → ℝ) (X P T₀ T : ℝ) : ℝ :=
  ∫ t in Set.Ioc T₀ T,
    ‖primeDirichletPolynomial P (onePlusIT t) *
      dirichletPolynomial (fun n ↦ (weight n : ℂ))
        (natOpenClosedInterval (X / (2 * P)) (4 * X / P))
        (onePlusIT t)‖ ^ (2 : ℕ)

/-- [MT23, Lemma 3.1], “Reduction to Dirichlet polynomials”, in its printed
scope.  In particular `c` is exactly `2.1`, and the exponent `a` is restricted
to `[c-1-10⁻⁴,c-1]`; this statement makes no claim in the wider parameter
range sought by the new paper.

“`ε>0` small enough but fixed” is rendered as the existence of a positive
threshold `εₘₐₓ`.  The two `≪` constants are made explicit: a uniform
constant `Cdp` in the Dirichlet-polynomial hypothesis yields a uniform
constant `Cvar` in (2.6), allowed to depend on the fixed `ε`, `a`, and `Cdp`
but not on `X` or `T`.  The weight is the particular minorant from equation
(2.3), rather than an arbitrary family of coefficients. -/
def MatomakiTeravainenLemmaThreeOneStatement : Prop :=
  ∃ εₘₐₓ : ℝ, 0 < εₘₐₓ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∀ a : ℝ,
        (21 / 10 : ℝ) - 1 - 1 / 10000 ≤ a →
        a ≤ (21 / 10 : ℝ) - 1 →
        ∀ Cdp : ℝ, 0 < Cdp →
          ∃ Cvar : ℝ, 0 < Cvar ∧
            ∀ X : ℝ, 3 ≤ X →
              let c : ℝ := 21 / 10
              let h : ℝ := (Real.log X) ^ c
              let h₁ : ℝ := X ^ (99 / 100 : ℝ)
              let P₁ : ℝ := (Real.log X) ^ a
              let T₀ : ℝ := X ^ (1 / 1000 : ℝ)
              (∀ T : ℝ, X / h ≤ T →
                matomakiTeravainenPerronIntegral
                    (matomakiTeravainenMinorant X ε) X P₁ T₀ T ≤
                  Cdp * (T / (X / h)) / (Real.log X) ^ (2 + ε)) →
              matomakiTeravainenShortLongVariance
                  (matomakiTeravainenMinorant X ε) X P₁ h h₁ ≤
                Cvar / (Real.log X) ^ (2 + ε)

/-! ## Matomäki--Teräväinen's decomposition of the minorant -/

/-- The Type-I convolution in [MT23, Proposition 2.2(i)].  The two finite
ranges merely enumerate the positive factorizations `n=m₁m₂`; the scale
conditions are exactly `m₁∼M₁` and `M₂<m₂≤(1+δ)M₂`. -/
noncomputable def matomakiTeravainenTypeIValue
    (δ M₁ M₂ : ℝ) (α : ℕ → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ m₁ ∈ Finset.range (n + 1), ∑ m₂ ∈ Finset.range (n + 1),
    if m₁ * m₂ = n ∧ InDyadicRange M₁ m₁ ∧
        M₂ < (m₂ : ℝ) ∧ (m₂ : ℝ) ≤ (1 + δ) * M₂ then
      α m₁
    else 0

/-- The Type-I/II convolution in [MT23, Proposition 2.2(ii)]. -/
noncomputable def matomakiTeravainenTypeIOneHalfValue
    (δ M₁ M₂ M₃ : ℝ) (α β : ℕ → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ m₁ ∈ Finset.range (n + 1), ∑ m₂ ∈ Finset.range (n + 1),
    ∑ m₃ ∈ Finset.range (n + 1),
      if m₁ * m₂ * m₃ = n ∧ InDyadicRange M₁ m₁ ∧
          InDyadicRange M₂ m₂ ∧ M₃ < (m₃ : ℝ) ∧
          (m₃ : ℝ) ≤ (1 + δ) * M₃ then
        α m₁ * β m₂
      else 0

/-- The number of ordered prime tuples in [MT23, equation (2.11)].
The source indexes the tuple by `1,…,R`; `Fin R` is the identical zero-based
finite index set.  Searching in `Fin (m+1)` loses no tuple whose product is
the positive integer `m`. -/
noncomputable def matomakiTeravainenStructuredTypeIICoefficient
    (δ : ℝ) (R : ℕ) (Q : Fin R → ℝ) (m : ℕ) : ℂ := by
  classical
  exact (((Finset.univ : Finset (Fin R → Fin (m + 1))).filter fun q ↦
    (∀ j : Fin R,
      (q j : ℕ).Prime ∧ Q j < (q j : ℝ) ∧
        (q j : ℝ) ≤ Q j * (1 + δ)) ∧
      (∏ j : Fin R, (q j : ℕ)) = m).card : ℂ)

/-- The Type-II convolution in [MT23, Proposition 2.2(iii)]. -/
noncomputable def matomakiTeravainenTypeIIValue
    (δ M₁ M₂ : ℝ) (R : ℕ) (α β : ℕ → ℂ) (n : ℕ) : ℂ := by
  classical
  exact ∑ m₁ ∈ Finset.range (n + 1), ∑ m₂ ∈ Finset.range (n + 1),
    if m₁ * m₂ = n ∧ M₁ < (m₁ : ℝ) ∧
        (m₁ : ℝ) ≤ (1 + δ) ^ R * M₁ ∧ InDyadicRange M₂ m₂ then
      α m₁ * β m₂
    else 0

/-- The first alternative in [MT23, Proposition 2.2]. -/
def MatomakiTeravainenTypeICase
    (X Y ε δ Bcoeff Acoeff : ℝ) (f : ℕ → ℂ) : Prop :=
  ∃ (M₁ M₂ : ℝ) (α : ℕ → ℂ),
    0 < M₁ ∧ 0 < M₂ ∧
      IsDivisorBoundedByConstant Bcoeff Acoeff α ∧
      M₁ ≤ X ^ (1 / 2 + ε) ∧
      Y / 2 < M₁ * M₂ ∧ M₁ * M₂ ≤ 4 * Y ∧
      ∀ n : ℕ, f n = matomakiTeravainenTypeIValue δ M₁ M₂ α n

/-- The second alternative in [MT23, Proposition 2.2]. -/
def MatomakiTeravainenTypeIOneHalfCase
    (X Y ε δ Bcoeff Acoeff : ℝ) (f : ℕ → ℂ) : Prop :=
  ∃ (M₁ M₂ M₃ : ℝ) (α β : ℕ → ℂ),
    0 < M₁ ∧ 0 < M₂ ∧ 0 < M₃ ∧
      IsDivisorBoundedByConstant Bcoeff Acoeff α ∧
      IsDivisorBoundedByConstant Bcoeff Acoeff β ∧
      M₁ ^ (2 : ℕ) * M₂ ≤ X ^ (1 - ε) ∧
      M₂ ≤ X ^ (1 / 4 - ε) ∧
      Y / 2 < M₁ * M₂ * M₃ ∧ M₁ * M₂ * M₃ ≤ 4 * Y ∧
      ∀ n : ℕ,
        f n = matomakiTeravainenTypeIOneHalfValue δ M₁ M₂ M₃ α β n

/-- The third alternative in [MT23, Proposition 2.2], including the exact
structured coefficient (2.11). -/
def MatomakiTeravainenTypeIICase
    (X Y ε δ z₀ z Bcoeff Acoeff : ℝ) (f : ℕ → ℂ) : Prop :=
  ∃ (R : ℕ) (M₁ M₂ : ℝ) (α β : ℕ → ℂ) (Q : Fin R → ℝ),
    1 ≤ R ∧ R ≤ ⌊Real.log z / Real.log z₀⌋₊ ∧
      0 < M₁ ∧ 0 < M₂ ∧
      IsDivisorBoundedByConstant Bcoeff Acoeff α ∧
      IsDivisorBoundedByConstant Bcoeff Acoeff β ∧
      X ^ (ε / 2) ≤ M₁ ∧ M₁ ≤ z ∧
      Y / 2 < M₁ * M₂ ∧ M₁ * M₂ ≤ 4 * Y ∧
      (∀ j : Fin R, z₀ ≤ Q j ∧ Q j < z) ∧
      (∏ j : Fin R, Q j) = M₁ ∧
      (∀ m : ℕ, α m = matomakiTeravainenStructuredTypeIICoefficient δ R Q m) ∧
      ∀ n : ℕ, f n = matomakiTeravainenTypeIIValue δ M₁ M₂ R α β n

/-- [MT23, Proposition 2.2], “Decomposition of the minorant”, in the
source's printed scope.  Thus `z₀`, `z`, and `δ_A` have exactly their values
from the proposition; `Y ∈ (X^(1-ε/100),X/2]`; the remainder is supported
on `(Y/4,8Y]` and satisfies (2.10); and every family member has one of the
three displayed Type-I, Type-I/II, or Type-II representations.

The phrases `ε>0 fixed and small enough`, `O(exp((log log X)^5))`,
`divisor-bounded`, and `≪_A` are expanded into a positive `ε` threshold,
uniform coefficient witnesses, and positive constants chosen after the
fixed parameters `ε,A` but before `X,Y`.  This is the source's
fixed-parameter meaning and makes the decomposition usable in a theorem
whose power-saving exponent must be uniform in the principal scale.
The source has real-valued terms embedded in `ℂ`; this harmless codomain
choice is already the codomain printed for the functions `f`. -/
def MatomakiTeravainenPropositionTwoTwoStatement : Prop := by
  classical
  exact ∃ εₘₐₓ : ℝ, 0 < εₘₐₓ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∀ A : ℝ, 5 ≤ A →
        ∃ Cfamily Cremainder Bcoeff Acoeff : ℝ,
          0 < Cfamily ∧ 0 < Cremainder ∧
          0 ≤ Bcoeff ∧ 1 ≤ Acoeff ∧
            ∀ X : ℝ, 3 ≤ X →
              let z₀ : ℝ := Real.exp (Real.log X / (Real.log (Real.log X)) ^ (3 : ℕ))
              let z : ℝ := X ^ (2 / 11 : ℝ)
              let δ : ℝ := (Real.log X) ^ (-10 * A)
              ∀ Y : ℝ, X ^ (1 - ε / 100) < Y → Y ≤ X / 2 →
                ∃ (F : Finset (ℕ → ℂ)) (c : ℕ → ℂ),
                  (F.card : ℝ) ≤
                      Cfamily * Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ)) ∧
                    (∀ n : ℕ,
                      (if n ∈ natOpenClosedInterval (Y / 2) (4 * Y) then
                          (matomakiTeravainenMinorant X ε n : ℂ)
                        else 0) =
                        (∑ f ∈ F, f n) + c n) ∧
                    (∀ n : ℕ, c n ≠ 0 → Y / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * Y) ∧
                    (∑ n ∈ natOpenClosedInterval (Y / 4) (8 * Y), ‖c n‖ ^ (2 : ℕ)) ≤
                      Cremainder * Y / (Real.log X) ^ A ∧
                    ∀ f ∈ F,
                      MatomakiTeravainenTypeICase
                        X Y ε δ Bcoeff Acoeff f ∨
                      MatomakiTeravainenTypeIOneHalfCase
                        X Y ε δ Bcoeff Acoeff f ∨
                      MatomakiTeravainenTypeIICase
                        X Y ε δ z₀ z Bcoeff Acoeff f

/-! ## Matomäki--Teräväinen's mean-value theorems -/

/-- The Dirichlet polynomial `A(s)=∑_{n≤N} aₙn⁻ˢ` in
[MT23, Lemmas 3.2--3.3]. -/
noncomputable def matomakiTeravainenInitialDirichletPolynomial
    (a : ℕ → ℂ) (N : ℝ) (s : ℂ) : ℂ :=
  dirichletPolynomial a (natOpenClosedInterval 0 N) s

/-- [MT23, Lemma 3.2], credited there to [IK04, Theorem 9.1], in the
source's complete normalization.  It is the standard mean-value theorem for
`A(s)=∑_{n≤N}aₙn⁻ˢ` on the zero line and over `[-T,T]`.

The printed equality
`(2T+O(N)) ∑_{n≤N}|aₙ|²` is expressed as an absolute-error
inequality.  One positive absolute constant is quantified before `N,T` and
the arbitrary complex coefficient sequence, so no parameter dependence is
hidden in the `O` term. -/
def MatomakiTeravainenLemmaThreeTwoStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (N T : ℝ) (a : ℕ → ℂ),
      1 ≤ N → 1 ≤ T →
      let S : ℝ :=
        ∑ n ∈ natOpenClosedInterval 0 N, ‖a n‖ ^ (2 : ℕ)
      let I : ℝ :=
        ∫ t in Set.Icc (-T) T,
          ‖matomakiTeravainenInitialDirichletPolynomial a N
              ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)
      |I - 2 * T * S| ≤ C * N * S

/-- [IK04, Theorem 9.4], the discrete mean-value theorem for Dirichlet
polynomials.  For arbitrary complex coefficients in
`D(s)=∑_{n≤N}aₙn⁻ˢ` and a finite one-spaced set of heights in `[0,T]`,
it bounds the discrete mean square by

`(∑|aₙ|²) (T + N) log(2N)`.

The source's absolute implied constant is quantified before every varying
parameter.  The coefficient support is exactly `1≤n≤N`, and the value at
`it` is represented by the shared initial-polynomial definition. -/
def IwaniecKowalskiTheoremNineFourStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (N T : ℝ) (a : ℕ → ℂ) (R : Finset ℝ),
      1 ≤ N → 1 ≤ T →
      (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
      IsOneSpaced (↑R : Set ℝ) →
      (∑ t ∈ R,
          ‖matomakiTeravainenInitialDirichletPolynomial a N
              ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)) ≤
        C * (T + N) * Real.log (2 * N) *
          (∑ n ∈ natOpenClosedInterval 0 N, ‖a n‖ ^ (2 : ℕ))

/-- [IK04, Theorem 9.6], labelled “Montgomery” in the source and commonly
called the Halász--Montgomery inequality.  For arbitrary complex
coefficients in `D(s)=∑_{n≤N}aₙn⁻ˢ` and a finite one-spaced set of
heights in `[0,T]`, it bounds the discrete mean square by

`(∑|aₙ|²) (N + R√T) log(2T)`, where `R` is the number of heights.

The unadorned source `≪` is expanded into one positive absolute constant,
quantified before `N,T`, the coefficient sequence, and the height set.  The
support is exactly the source interval `1≤n≤N`; coefficients outside that
interval are irrelevant.  The polynomial is evaluated at `it`, so its terms
are exactly `aₙn⁻ⁱᵗ`. -/
def IwaniecKowalskiTheoremNineSixStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (N T : ℝ) (a : ℕ → ℂ) (R : Finset ℝ),
      1 ≤ N → 1 ≤ T →
      (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
      IsOneSpaced (↑R : Set ℝ) →
      (∑ t ∈ R,
          ‖matomakiTeravainenInitialDirichletPolynomial a N
              ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)) ≤
        C * (N + (R.card : ℝ) * T ^ (1 / 2 : ℝ)) *
          Real.log (2 * T) *
          (∑ n ∈ natOpenClosedInterval 0 N, ‖a n‖ ^ (2 : ℕ))

/-- The conventional zero extension of the finite coefficient vector
`(aₙ)_{1≤n≤N}` to integer indices.  It makes the printed term `a_{n+k}`
literal also when the integer shift leaves `[1,N]`. -/
noncomputable def matomakiTeravainenZeroExtendedCoefficient
    (a : ℕ → ℂ) (N : ℝ) (m : ℤ) : ℂ :=
  if 0 < m ∧ (m : ℝ) ≤ N then a m.toNat else 0

/-- The integer shifts satisfying the source condition `0<|k|≤R`. -/
noncomputable def matomakiTeravainenNonzeroIntegerShifts (R : ℝ) : Finset ℤ := by
  classical
  let K : ℕ := ⌊R⌋₊
  exact (Finset.Icc (-(K : ℤ)) (K : ℤ)).erase 0

/-- The shifted-coefficient correlation on the right side of
[MT23, Lemma 3.3]. -/
noncomputable def matomakiTeravainenShiftedCorrelation
    (a : ℕ → ℂ) (N T : ℝ) : ℝ :=
  ∑ k ∈ matomakiTeravainenNonzeroIntegerShifts (N / T),
    ∑ n ∈ natOpenClosedInterval 0 N,
      ‖a n‖ * ‖matomakiTeravainenZeroExtendedCoefficient a N ((n : ℤ) + k)‖

/-- [MT23, Lemma 3.3], the improved mean-value theorem, with the source's
line `Re(s)=0`, symmetric interval `[-T,T]`, full initial polynomial, and
both terms of the sparse-correlation bound.

The unadorned `≪` is expanded into one positive absolute constant, quantified
before `N,T` and the coefficients.  The paper's finite coefficient vector is
zero-extended outside `1≤n≤N`, which is the standard convention making
`a_{n+k}` meaningful for negative shifts.  MT23 derives this statement from
[IK04, Lemma 7.1] using `Y=10T` and `xₘ=(2π)⁻¹ log m`; that derivation is
part of the cited MT23 lemma and is not conflated with a separate normalized
statement of the Iwaniec--Kowalski input. -/
def MatomakiTeravainenLemmaThreeThreeStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (N T : ℝ) (a : ℕ → ℂ),
      1 ≤ N → 1 ≤ T →
      (∫ t in Set.Icc (-T) T,
          ‖matomakiTeravainenInitialDirichletPolynomial a N
              ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)) ≤
        C *
          (T * (∑ n ∈ natOpenClosedInterval 0 N, ‖a n‖ ^ (2 : ℕ)) +
            T * matomakiTeravainenShiftedCorrelation a N T)

/-! ## The Section 5 rough-pair sieve bound -/

/-- The zero-line coefficient used in the displayed rough-pair estimate in
[MT23, Section 5, p. 16].  The factor `1/n` converts the roughness indicator
into the coefficient of the Dirichlet polynomial on `Re(s)=1`; the outer
indicator is the literal support `X/(2P₁)<n≤4X/P₁`. -/
noncomputable def matomakiTeravainenSectionFiveRoughCoefficient
    (X P₁ : ℝ) (n : ℕ) : ℂ :=
  if n ∈ natOpenClosedInterval (X / (2 * P₁)) (4 * X / P₁) then
    ((matomakiTeravainenRoughIndicator n
        (X ^ (2 / 11 : ℝ)) / (n : ℝ) : ℝ) : ℂ)
  else 0

/-- [MT23, Section 5, displayed estimate on p. 16 immediately after the
application of Lemma 3.3].  This is the exact diagonal-plus-shifted-pair
upper bound used on the complement of `U`.

The source writes that the second estimate follows from a simple upper-bound
sieve, referring to [IK04, Theorem 6.7] for a similar argument.  We record
the published displayed conclusion itself, rather than incorrectly treating
the fixed prime-tuple theorem as a literal instance.  The implied constant
and starting scale are uniform in `X`, the printed exponent `alpha`, and the
height `T`. -/
def MatomakiTeravainenSectionFiveRoughSieveStatement : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧
    ∀ X alpha T : ℝ, X₀ ≤ X →
      let c : ℝ := 21 / 10
      let h : ℝ := (Real.log X) ^ c
      let P₁ : ℝ := (Real.log X) ^ alpha
      let N : ℝ := 4 * X / P₁
      c - 1 - 1 / 10000 ≤ alpha → alpha ≤ c - 1 →
      X / h ≤ T → T ≤ X →
      let b := matomakiTeravainenSectionFiveRoughCoefficient X P₁
      T * (∑ n ∈ natOpenClosedInterval 0 N,
              ‖b n‖ ^ (2 : ℕ)) +
          T * matomakiTeravainenShiftedCorrelation b N T ≤
        C *
          (T * P₁ / (X * Real.log X) +
            1 / (Real.log X) ^ (2 : ℕ))

/-! ## Matomäki--Teräväinen's pointwise minorant property -/

/-- The prime indicator on the right side of [MT23, Theorem 2.1(i)]. -/
def matomakiTeravainenPrimeIndicator (n : ℕ) : ℝ :=
  if n.Prime then 1 else 0

/-- [MT23, Theorem 2.1(i)] in the theorem's complete printed setup.
The constants are exactly `c=2.1`, `h=(log X)^c`, `h₁=X^(99/100)`, and
`a∈[c-1-1/10000,c-1]`, with `P₁=(log X)^a`; the minorant is the four-term
function from equation (2.3), whose internal roughness level is
`z=X^(2/11)`.

Although `h,h₁,a,P₁` do not occur in part (i)'s pointwise inequality, they
are retained as surrounding quantifiers and definitions because the source
states all three parts under this fixed setup.  “ε sufficiently small” is
represented by an existential positive threshold.  There is no exceptional
set in part (i): the conclusion holds for every integer in the printed
closed interval `[2X^(1/2),3X]`. -/
def MatomakiTeravainenTheoremTwoOnePartOneStatement : Prop :=
  ∃ εₘₐₓ : ℝ, 0 < εₘₐₓ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∀ X : ℝ, 3 ≤ X →
        let c : ℝ := 21 / 10
        let _h : ℝ := (Real.log X) ^ c
        let _h₁ : ℝ := X ^ (99 / 100 : ℝ)
        ∀ a : ℝ, c - 1 - 1 / 10000 ≤ a → a ≤ c - 1 →
          let _P₁ : ℝ := (Real.log X) ^ a
          ∀ n : ℕ,
            2 * X ^ (1 / 2 : ℝ) ≤ (n : ℝ) → (n : ℝ) ≤ 3 * X →
              matomakiTeravainenMinorant X ε n ≤
                matomakiTeravainenPrimeIndicator n

/-- [MT23, Theorem 2.1(ii)] in its complete printed setup.  The assertion is
the single-`P₁` long-interval lower bound, uniformly for every
`a∈[c-1-1/10000,c-1]` and every real `x∈(X,2X]`, once `X` exceeds a
threshold depending on the fixed small `ε`.  The weight is exactly the
four-term minorant (2.3), and `h₁=X^(99/100)`.

This is not equation (2.7): that later formula sums over several prime blocks
and replaces the right side by `γ/log X`.  Neither that consequence nor the
variance assertion in part (iii) is included here. -/
def MatomakiTeravainenTheoremTwoOnePartTwoStatement : Prop :=
  ∃ εₘₐₓ : ℝ, 0 < εₘₐₓ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∃ X₀ : ℝ, 3 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          let c : ℝ := 21 / 10
          let _h : ℝ := (Real.log X) ^ c
          let h₁ : ℝ := X ^ (99 / 100 : ℝ)
          ∀ a : ℝ, c - 1 - 1 / 10000 ≤ a → a ≤ c - 1 →
            let P₁ : ℝ := (Real.log X) ^ a
            ∀ x : ℝ, X < x → x ≤ 2 * X →
              h₁ / (200 * Real.log P₁ * Real.log X) ≤
                matomakiTeravainenPrimeProductSum
                  (matomakiTeravainenMinorant X ε) P₁ x h₁

/-! ## Matomäki--Teräväinen's twisted fourth-moment estimates -/

/-- The unit-coefficient segment
`N(s)=∑_{N<n≤N'} n⁻ˢ` in [MT23, Lemma 3.5]. -/
noncomputable def matomakiTeravainenZetaSegmentPolynomial
    (N N' : ℝ) (s : ℂ) : ℂ :=
  dirichletPolynomial (fun _ ↦ 1) (natOpenClosedInterval N N') s

/-- The finite maximum `max_{m∼A} |aₘ|` in [MT23, Lemma 3.5(i)].
The `NNReal` supremum gives zero on an empty range; the source hypothesis
`A≥1` makes the relevant dyadic range nonempty. -/
noncomputable def dyadicComplexCoefficientSup (a : ℕ → ℂ) (A : ℝ) : ℝ :=
  ↑((dyadicInterval A).sup fun m ↦ Real.toNNReal ‖a m‖)

/-- The common left side of [MT23, Lemma 3.5(i),(ii)], on the source's
line `Re(s)=1` and height interval `[T/2,T]`. -/
noncomputable def matomakiTeravainenTwistedFourthMoment
    (A N N' T : ℝ) (a : ℕ → ℂ) : ℝ :=
  ∫ t in Set.Icc (T / 2) T,
    ‖matomakiTeravainenZetaSegmentPolynomial N N' (onePlusIT t)‖ ^ (4 : ℕ) *
      ‖dyadicDirichletPolynomial a A (onePlusIT t)‖ ^ (2 : ℕ)

/-- [MT23, Lemma 3.5(i)], the normalization of Watt [Watt95, equation
(4.7)] used by Matomäki--Teräväinen.  All four scale hypotheses and the
source's exact range `N<N'≤2N` are explicit.  The unadorned `≪` is
expanded as a positive constant depending only on `ε`, quantified before
`A,N,N',T` and the arbitrary complex coefficient sequence. -/
def MatomakiTeravainenLemmaThreeFivePartOneStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (A N N' T : ℝ) (a : ℕ → ℂ),
      1 ≤ A → 1 ≤ N → 1 ≤ N' → 1 ≤ T →
      N < N' → N' ≤ 2 * N →
      matomakiTeravainenTwistedFourthMoment A N N' T a ≤
        C * T ^ ε *
          (((T + A ^ (2 : ℕ) * T ^ (1 / 2 : ℝ)) /
                (N ^ (2 : ℕ) * A) +
              (T + A) / (T ^ (4 : ℕ) * A)) *
            dyadicComplexCoefficientSup a A ^ (2 : ℕ))

/-- [MT23, Lemma 3.5(ii)], the normalization of
Deshouillers--Iwaniec [DI82, equation (14)] used by
Matomäki--Teräväinen.  It has the same quantifiers and integration range
as part (i), the additional printed term `A^(5/4)T^(3/4)`, and the source's
averaged squared coefficient norm `A⁻¹∑_{m∼A}|aₘ|²`. -/
def MatomakiTeravainenLemmaThreeFivePartTwoStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (A N N' T : ℝ) (a : ℕ → ℂ),
      1 ≤ A → 1 ≤ N → 1 ≤ N' → 1 ≤ T →
      N < N' → N' ≤ 2 * N →
      matomakiTeravainenTwistedFourthMoment A N N' T a ≤
        C * T ^ ε *
          (((T + A ^ (2 : ℕ) * T ^ (1 / 2 : ℝ) +
                A ^ (5 / 4 : ℝ) * T ^ (3 / 4 : ℝ)) /
                (N ^ (2 : ℕ) * A) +
              (T + A) / (T ^ (4 : ℕ) * A)) *
            ((1 / A) *
              ∑ m ∈ dyadicInterval A, ‖a m‖ ^ (2 : ℕ)))

/-! ## Vinogradov--Korobov decay for the structured Type-II factor -/

/-- [MT23, equation (5.6)], stated for the structured coefficient
from [MT23, equation (2.11)].  Matomaki--Teravainen derive this estimate as
a corollary of the Vinogradov--Korobov zero-free region, citing
[Harman 2007, Lemma 1.5].

The source notation `\ll` is expanded into a positive constant after the
fixed parameters `epsilon,A` and before all moving parameters.  The
polynomial, its support, and the paper scales `z_0,z,delta_A,T_0,T_1` are
written literally.  In particular, this is the published estimate for the
structured product encoded through its coefficient sequence; no unsupported
localization from a full dyadic prime sum is inserted. -/
def MatomakiTeravainenEquationFiveSixStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∀ A : ℝ, 5 ≤ A →
      ∃ X0 C : ℝ, 3 ≤ X0 ∧ 0 < C ∧
        ∀ (X M1 t : ℝ) (R : ℕ) (Q : Fin R → ℝ), X0 ≤ X →
          let z0 : ℝ :=
            Real.exp
              (Real.log X / (Real.log (Real.log X)) ^ (3 : ℕ))
          let z : ℝ := X ^ (2 / 11 : ℝ)
          let delta : ℝ := (Real.log X) ^ (-10 * A)
          let T0 : ℝ := X ^ (1 / 1000 : ℝ)
          1 ≤ R →
          R ≤ ⌊Real.log z / Real.log z0⌋₊ →
          (∀ j : Fin R, z0 ≤ Q j ∧ Q j < z) →
          (∏ j, Q j) = M1 →
          X ^ (epsilon / 2) ≤ M1 → M1 ≤ z →
          T0 ≤ t → t ≤ X →
          ‖
              (dirichletPolynomial
                (matomakiTeravainenStructuredTypeIICoefficient delta R Q)
                (natOpenClosedInterval M1 ((1 + delta) ^ R * M1))
                (onePlusIT t))‖ ≤
            C * Real.exp (-2 * (Real.log X) ^ (1 / 10 : ℝ))

/-! ## Harman's dyadic prime-polynomial estimate -/

/-- Harman's notation `p \sim P`: primes in the half-open interval
`[P,2P)`.  The finite search range is extensionally exact for every real
`P`; the hypotheses of Lemma 1.5 later impose `P ≥ 2`. -/
noncomputable def harmanDyadicPrimes (P : ℝ) : Finset ℕ :=
  (Finset.range ⌈2 * P⌉₊).filter fun p ↦
    p.Prime ∧ P ≤ (p : ℝ) ∧ (p : ℝ) < 2 * P

/-- The prime Dirichlet polynomial in [Harman07, Lemma 1.5]. -/
noncomputable def harmanPrimePolynomial (P σ t : ℝ) : ℂ :=
  dirichletPolynomial (fun _ ↦ 1) (harmanDyadicPrimes P)
    ((σ : ℂ) + (t : ℂ) * Complex.I)

/-- [Harman07, Lemma 1.5, p. 14], with `p \sim P` interpreted as
`P ≤ p < 2P`.  The source hypotheses are `V ≥ e`, `P ≥ 2`,
`V ≤ |t| < 2V`, and `s=σ+it`.

The implied constant is allowed to depend on the fixed real part `σ`, so
it is quantified after `σ` and before `V,P,t`.  This literal dyadic estimate
does not itself give a uniform bound for the much shorter prime intervals in
[MT23, equation (5.6)]. -/
def HarmanLemmaOneFiveStatement : Prop :=
  ∀ σ : ℝ, ∃ C : ℝ, 0 < C ∧
    ∀ (V P t : ℝ),
      Real.exp 1 ≤ V → 2 ≤ P →
      V ≤ |t| → |t| < 2 * V →
      ‖harmanPrimePolynomial P σ t‖ ≤
        C *
          (P ^ (1 - σ) *
              Real.exp
                (-Real.log P /
                  (Real.log V) ^ (7 / 10 : ℝ)) +
            P ^ (1 - σ) / V * (Real.log P) ^ (3 : ℕ))

/-! ## Iwaniec--Kowalski's fixed prime-tuple upper-bound sieve -/

/-- The number `ν_p` of distinct residue classes occupied by a fixed tuple
`(a_i)`: the quantity in [IK04, equation (6.96)]. -/
noncomputable def ikPrimeTupleResidueCount {k : ℕ}
    (a : Fin k → ℤ) (p : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin k)).image fun i ↦ a i % (p : ℤ)).card

/-- The number of `m ≤ x` for which every `m-a_i` is prime, as in
[IK04, Theorem 6.7]. -/
noncomputable def ikPrimeTupleCount {k : ℕ}
    (a : Fin k → ℤ) (x : ℝ) : ℕ := by
  classical
  exact ((Finset.Icc 1 ⌊x⌋₊).filter fun m : ℕ ↦
    ∀ i : Fin k, ∃ q : ℕ,
      q.Prime ∧ (m : ℤ) - a i = (q : ℤ)).card

/-- The local Euler factor in the singular series (6.96).  Non-prime
indices contribute `1`, allowing the singular series to be represented by
`HasProd` over `ℕ`. -/
noncomputable def ikPrimeTupleEulerFactor {k : ℕ}
    (a : Fin k → ℤ) (p : ℕ) : ℝ :=
  if p.Prime then
    (1 - (ikPrimeTupleResidueCount a p : ℝ) / (p : ℝ)) /
      (1 - (p : ℝ)⁻¹) ^ k
  else 1

/-- [IK04, Theorem 6.7, equations (6.96)--(6.97)], for a fixed admissible
tuple of distinct shifts.  The singular-series value `B`, the error constant
`C`, and the threshold `x₀` are chosen after the tuple, faithfully allowing
the source's `O`-constant to depend on that fixed tuple.

This theorem counts a fixed tuple of simultaneous prime values.  The
rough-number pair estimate used in [MT23, Section 5] is described there as
“similar to” this theorem and remains a separate local sieve derivation. -/
def IwaniecKowalskiTheoremSixSevenStatement : Prop :=
  ∀ k : ℕ, 0 < k →
    ∀ a : Fin k → ℤ,
      Function.Injective a →
      (∀ p : ℕ, p.Prime → ikPrimeTupleResidueCount a p < p) →
      ∃ B C x₀ : ℝ,
        HasProd (ikPrimeTupleEulerFactor a) B ∧
        0 < C ∧ 3 ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x →
          (ikPrimeTupleCount a x : ℝ) ≤
            (2 : ℝ) ^ k * (k.factorial : ℝ) * B * x /
                (Real.log x) ^ k *
              (1 + C * Real.log (Real.log (3 * x)) / Real.log x)

/-- The explicit external trust boundary.  All fields have
faithful quantified source statements.  Paper-specific consequences not
literally supplied by those sources remain internal proof obligations. -/
structure ExternalInputs : Prop where
  guthMaynardMainLargeValues : GuthMaynardMainLargeValuesStatement
  guthMaynardLongPolynomial : GuthMaynardLongPolynomialStatement
  hildebrandTenenbaumCorollaryOneThree :
    HildebrandTenenbaumCorollaryOneThreeStatement
  mertensSecondTheorem : MertensSecondTheoremStatement
  lucaTothTheoremOne : LucaTothTheoremOneStatement
  matomakiTeravainenLemmaThreeFour :
    MatomakiTeravainenLemmaThreeFourStatement
  matomakiTeravainenLemmaThreeOne :
    MatomakiTeravainenLemmaThreeOneStatement
  matomakiTeravainenEquationTwoFour :
    MatomakiTeravainenEquationTwoFourStatement
  matomakiTeravainenPropositionTwoTwo :
    MatomakiTeravainenPropositionTwoTwoStatement
  matomakiTeravainenLemmaThreeThree :
    MatomakiTeravainenLemmaThreeThreeStatement
  matomakiTeravainenSectionFiveRoughSieve :
    MatomakiTeravainenSectionFiveRoughSieveStatement
  matomakiTeravainenTheoremTwoOnePartOne :
    MatomakiTeravainenTheoremTwoOnePartOneStatement
  matomakiTeravainenTheoremTwoOnePartTwo :
    MatomakiTeravainenTheoremTwoOnePartTwoStatement
  wattEquationFourSeven :
    MatomakiTeravainenLemmaThreeFivePartOneStatement
  deshouillersIwaniecEquationFourteen :
    MatomakiTeravainenLemmaThreeFivePartTwoStatement
  iwaniecKowalskiTheoremNineOne :
    MatomakiTeravainenLemmaThreeTwoStatement
  iwaniecKowalskiTheoremNineFour :
    IwaniecKowalskiTheoremNineFourStatement
  iwaniecKowalskiTheoremNineSix :
    IwaniecKowalskiTheoremNineSixStatement
  matomakiTeravainenEquationFiveSix :
    MatomakiTeravainenEquationFiveSixStatement
  harmanLemmaOneFive : HarmanLemmaOneFiveStatement
  iwaniecKowalskiTheoremSixSeven :
    IwaniecKowalskiTheoremSixSevenStatement

def assumptionsModule : ProofModule :=
  { name := "Assumptions"
    paperLocation := "Cited external inputs used throughout Sections 4--7"
    purpose :=
      "Track every unformalized published theorem as an explicit, cited hypothesis, replacing each slot by its exact source statement."
    dependsOn := ["Definitions"]
    status := .externalAssumption }

end ExactSemiprimes
