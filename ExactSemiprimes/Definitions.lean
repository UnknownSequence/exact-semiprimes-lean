import Mathlib

/-!
# Shared definitions and formalization metadata

This file imports Mathlib and contains the stable definitions shared by the
formalization, together with typed metadata describing the proof
modules.  Mathematical definitions are added only when their intended paper
meaning can be represented without hiding asymptotic quantifiers.
-/

namespace ExactSemiprimes

open scoped BigOperators ENNReal
open Filter Set MeasureTheory Asymptotics

noncomputable section

/-! ## Analytic and arithmetic objects -/

/-- The point `1 + it` on the line on which the paper evaluates its
Dirichlet polynomials. -/
def onePlusIT (t : ℝ) : ℂ := 1 + (t : ℂ) * Complex.I

/-- The paper's convention `n ∼ N`, namely `N < n ≤ 2N`. -/
def InDyadicRange (N : ℝ) (n : ℕ) : Prop :=
  N < (n : ℝ) ∧ (n : ℝ) ≤ 2 * N

/-- The finite set of natural numbers in the paper's half-open dyadic range. -/
def dyadicInterval (N : ℝ) : Finset ℕ :=
  Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊

@[simp]
theorem mem_dyadicInterval {N : ℝ} (hN : 0 ≤ N) {n : ℕ} :
    n ∈ dyadicInterval N ↔ InDyadicRange N n := by
  simp only [dyadicInterval, Finset.mem_Ioc, InDyadicRange]
  rw [Nat.floor_lt hN, Nat.le_floor_iff (by positivity)]

/-- The closed integer interval `[N,2N]` appearing in the published
Guth--Maynard statements.  It is deliberately distinct from the paper's
convention `n ∼ N`, which means `(N,2N]`. -/
def closedDyadicInterval (N : ℕ) : Finset ℕ :=
  Finset.Icc N (2 * N)

/-- The exponential sum `∑_{N≤n≤2N} bₙ n^{it}` in the
Guth--Maynard large-values theorems. -/
def oscillatoryDirichletSum (b : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ closedDyadicInterval N, b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)

/-- A finite Dirichlet polynomial, using Mathlib's complex power. -/
def dirichletPolynomial (a : ℕ → ℂ) (S : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ S, a n * (n : ℂ) ^ (-s)

/-- A Dirichlet polynomial supported on `N < n ≤ 2N`. -/
def dyadicDirichletPolynomial (a : ℕ → ℂ) (N : ℝ) (s : ℂ) : ℂ :=
  dirichletPolynomial a (dyadicInterval N) s

/-- The primes in the paper's dyadic interval. -/
def dyadicPrimes (P : ℝ) : Finset ℕ :=
  (dyadicInterval P).filter Nat.Prime

/-- The reciprocal-prime sum over `p ≤ X`. -/
def reciprocalPrimeSum (X : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (X + 1)).filter Nat.Prime, (p : ℝ)⁻¹

/-- The number `Ψ(X,Y)` of positive integers at most `X` whose prime factors
are all at most `Y`. -/
def smoothNumberCount (X Y : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter fun n ↦ n.maxPrimeFac ≤ Y).card

/-- The specialization `Ψ(X,(log X)^a)` used in the sparse-support estimate. -/
def logPowerSmoothNumberCount (a : ℝ) (X : ℕ) : ℕ :=
  smoothNumberCount X ⌊(Real.log (X : ℝ)) ^ a⌋₊

/-- The unweighted prime Dirichlet polynomial on `P < p ≤ 2P`. -/
def primeDirichletPolynomial (P : ℝ) (s : ℂ) : ℂ :=
  dirichletPolynomial (fun _ ↦ 1) (dyadicPrimes P) s

/-- Distinct points of `R` have distance at least one. -/
def IsOneSpaced (R : Set ℝ) : Prop :=
  R.Pairwise fun x y ↦ 1 ≤ |x - y|

/-- The finite one-spaced sets occurring in large-values estimates. -/
def IsFiniteOneSpaced (R : Set ℝ) : Prop :=
  R.Finite ∧ IsOneSpaced R

/-- The usual divisor-counting function, exposed as a named definition for
the coefficient hypotheses. -/
def divisorCount (n : ℕ) : ℕ := n.divisors.card

/-- The coefficient estimate `|a_n| ≤ A d(n)^B`, with its multiplicative
constant exposed.  Keeping `A` explicit is essential in any theorem whose
conclusion is meant to be uniform in the coefficient sequence. -/
def IsDivisorBoundedByConstant (B A : ℝ) (a : ℕ → ℂ) : Prop :=
  0 ≤ B ∧ 0 < A ∧ ∀ n : ℕ, 0 < n →
    ‖a n‖ ≤ A * (divisorCount n : ℝ) ^ B

/-- The usual non-uniform notation `|a_n| ≪ d(n)^B`. -/
def IsDivisorBoundedBy (B : ℝ) (a : ℕ → ℂ) : Prop :=
  ∃ A : ℝ, IsDivisorBoundedByConstant B A a

/-- A coefficient sequence is divisor bounded for some fixed exponent. -/
def IsDivisorBounded (a : ℕ → ℂ) : Prop :=
  ∃ B : ℝ, IsDivisorBoundedBy B a

/-- The paper's quantified meaning of `f(T) = T^{o(1)}`.  Uniform versions
with auxiliary parameters must put those parameters outside this definition. -/
def IsSubpowerAtTop (f : ℝ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → f =O[atTop] fun T : ℝ ↦ T ^ η

/-! ## Integer intervals, exceptional sets, and semiprimes -/

/-- Natural numbers in the real interval `(x,y]`. -/
def natOpenClosedInterval (x y : ℝ) : Finset ℕ :=
  Finset.Ioc ⌊x⌋₊ ⌊y⌋₊

@[simp]
theorem mem_natOpenClosedInterval {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) {n : ℕ} :
    n ∈ natOpenClosedInterval x y ↔ x < (n : ℝ) ∧ (n : ℝ) ≤ y := by
  simp only [natOpenClosedInterval, Finset.mem_Ioc]
  rw [Nat.floor_lt hx, Nat.le_floor_iff hy]

/-- The natural numbers in `(x,x+h]`. -/
def shortInterval (x h : ℝ) : Finset ℕ :=
  natOpenClosedInterval x (x + h)

/-- The number of integers with property `P` in `(x,x+h]`. -/
def intervalCount (P : ℕ → Prop) (x h : ℝ) : ℕ := by
  classical
  exact ((shortInterval x h).filter P).card

/-- The logarithmic interval length `(log x)^c`, interpreted using real
exponentiation. -/
def logarithmicLength (c : ℝ) (x : ℕ) : ℝ :=
  (Real.log (x : ℝ)) ^ c

/-- Exact semiprimes, with prime factors counted with multiplicity.  Mathlib's
`Nat.IsSemiprime` is `Ω(n)=2`, so it includes squares of primes. -/
def IsExactSemiprime (n : ℕ) : Prop := n.IsSemiprime

/-- A product of two primes is an exact semiprime; multiplicity is allowed. -/
theorem exactSemiprime_of_prime_mul {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    IsExactSemiprime (p * q) := by
  exact hp.mul_isAlmostPrime_two hq

/-- The set `E₂` of exact semiprimes. -/
def semiprimes : Set ℕ := {n | IsExactSemiprime n}

/-- The interval `(x,x+(log x)^c]` contains an exact semiprime. -/
def LogIntervalContainsSemiprime (c : ℝ) (x : ℕ) : Prop :=
  ∃ n ∈ shortInterval (x : ℝ) (logarithmicLength c x), IsExactSemiprime n

/-- A product of two primes whose displayed first factor lies in `(L,U]`. -/
def IsWindowedPrimeProduct (L U : ℝ) (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q ∧
    L < (p : ℝ) ∧ (p : ℝ) ≤ U

/-- Every windowed prime product belongs to the exact-semiprime set. -/
theorem exactSemiprime_of_windowedPrimeProduct {L U : ℝ} {n : ℕ}
    (h : IsWindowedPrimeProduct L U n) : IsExactSemiprime n := by
  rcases h with ⟨p, q, hp, hq, rfl, _⟩
  exact exactSemiprime_of_prime_mul hp hq

/-- The number of such windowed prime products in `(x,x+h]`. -/
def windowedPrimeProductCount (x h L U : ℝ) : ℕ :=
  intervalCount (IsWindowedPrimeProduct L U) x h

/-- Exceptions to `P` among the integers in `[1,X]`. -/
def exceptionalUpTo (P : ℕ → Prop) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 X).filter fun n ↦ ¬ P n

/-- Exceptions to `P` in the dyadic block `[X,2X]`. -/
def exceptionalOnDyadicBlock (P : ℕ → Prop) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc X (2 * X)).filter fun n ↦ ¬ P n

/-- `P` holds for almost all positive integers: the number of exceptions up
to `X` is `o(X)`. -/
def ForAlmostAllIntegers (P : ℕ → Prop) : Prop :=
  (fun X : ℕ ↦ ((exceptionalUpTo P X).card : ℝ)) =o[atTop]
    (fun X : ℕ ↦ (X : ℝ))

/-- A power-of-logarithm exceptional-set estimate, with the exponent and all
parameter dependence explicit in the surrounding quantifiers. -/
def HasLogPowerExceptionalBound (P : ℕ → Prop) (δ : ℝ) : Prop :=
  (fun X : ℕ ↦ ((exceptionalUpTo P X).card : ℝ)) =O[atTop]
    (fun X : ℕ ↦ (X : ℝ) / (Real.log (X : ℝ)) ^ δ)

/-- The measurable set where an analytic function is larger than `V` on the
line `Re(s)=1` and in the height interval `[0,T]`. -/
def largeValueSet (A : ℂ → ℂ) (T V : ℝ) : Set ℝ :=
  Set.Icc 0 T ∩ {t | V < ‖A (onePlusIT t)‖}

end

/-- Status of a module in the staged formalization. -/
inductive FormalizationStatus where
  | structureOnly
  | externalAssumption
  | comparisonOnly
  | toBeProved
  | inProgress
  | proved
  /-- The module's lemmas are proved, but its originally announced end
  statement was replaced by a different route in the final proof. -/
  | superseded
  deriving Repr, BEq

/-- Build-time description of one mathematical proof module. -/
structure ProofModule where
  name : String
  paperLocation : String
  purpose : String
  dependsOn : List String
  status : FormalizationStatus := .structureOnly
  deriving Repr, BEq

end ExactSemiprimes
