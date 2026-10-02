import ExactSemiprimes.Assumptions
import ExactSemiprimes.Completion.ParameterizedReduction

/-! # Long-interval lower bound for the Harman minorant -/

namespace ExactSemiprimes
namespace Completion

open scoped BigOperators

noncomputable section

/-! ## The minorant interface -/

/-- Real-valued indicator of the primes. -/
def realPrimeIndicator (n : ℕ) : ℝ :=
  if n.Prime then 1 else 0

/-- The two independently introduced real prime indicators are identical. -/
@[simp]
theorem realPrimeIndicator_eq_matomakiTeravainenPrimeIndicator (n : ℕ) :
    realPrimeIndicator n = matomakiTeravainenPrimeIndicator n :=
  rfl

/-- A prime minorant restricted to a real interval of integer arguments.
This is the source-faithful interface for [MT23, Theorem 2.1(i)]; the Harman
weight may be negative, so no nonnegativity is imposed. -/
def IsPrimeMinorantOn
    (weight : ℕ → ℝ) (lower upper : ℝ) : Prop :=
  ∀ n : ℕ, lower ≤ (n : ℝ) → (n : ℝ) ≤ upper →
    weight n ≤ realPrimeIndicator n

/-- The exact interval on which [MT23, Theorem 2.1(i)] supplies minorant
domination. -/
def IsPrimeMinorantOnMatomakiTeravainenRange
    (weight : ℕ → ℝ) (X : ℝ) : Prop :=
  IsPrimeMinorantOn weight (2 * X ^ (1 / 2 : ℝ)) (3 * X)

/-- Every inner coefficient index in a weighted prime-product sum lies in a
specified real interval. -/
def PrimeProductInnerFactorsInRange
    (lower upper P x h : ℝ) : Prop :=
  ∀ p ∈ dyadicPrimes P,
    ∀ n ∈ shortInterval (x / (p : ℝ)) (h / (p : ℝ)),
      lower ≤ (n : ℝ) ∧ (n : ℝ) ≤ upper

/-- A global prime minorant.  This stronger legacy interface remains useful
for deductions whose weights are known to be globally dominated, but the
published Harman minorant is connected below through `IsPrimeMinorantOn`. -/
def IsPrimeMinorant (weight : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, weight n ≤ realPrimeIndicator n

/-- Global domination restricts to every local range. -/
theorem IsPrimeMinorant.onRange
    {weight : ℕ → ℝ} (hminorant : IsPrimeMinorant weight)
    (lower upper : ℝ) : IsPrimeMinorantOn weight lower upper := by
  intro n _hnLower _hnUpper
  exact hminorant n

/-- Weighted prime-product sums are monotone in their coefficient weight. -/
theorem weightedPrimeProductSum_mono
    {weight₁ weight₂ : ℕ → ℝ} (hweight : ∀ n, weight₁ n ≤ weight₂ n)
    (P x h : ℝ) :
    weightedPrimeProductSum weight₁ P x h ≤
      weightedPrimeProductSum weight₂ P x h := by
  apply Finset.sum_le_sum
  intro p _hp
  apply Finset.sum_le_sum
  intro n _hn
  exact hweight n

/-- Local minorant domination suffices for a weighted prime-product sum when
every inner factor occurring in that sum lies in the domination range. -/
theorem weightedPrimeProductSum_le_primeIndicator_on
    {weight : ℕ → ℝ} {lower upper P x h : ℝ}
    (hminorant : IsPrimeMinorantOn weight lower upper)
    (hinner : PrimeProductInnerFactorsInRange lower upper P x h) :
    weightedPrimeProductSum weight P x h ≤
      weightedPrimeProductSum realPrimeIndicator P x h := by
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro n hn
  exact hminorant n (hinner p hp n hn).1 (hinner p hp n hn).2

/-- The source-range specialization of the local sum comparison. -/
theorem weightedPrimeProductSum_le_primeIndicator_on_matomakiTeravainenRange
    {weight : ℕ → ℝ} {X P x h : ℝ}
    (hminorant : IsPrimeMinorantOnMatomakiTeravainenRange weight X)
    (hinner : PrimeProductInnerFactorsInRange
      (2 * X ^ (1 / 2 : ℝ)) (3 * X) P x h) :
    weightedPrimeProductSum weight P x h ≤
      weightedPrimeProductSum realPrimeIndicator P x h :=
  weightedPrimeProductSum_le_primeIndicator_on hminorant hinner

/-- The defining minorant inequality passes directly to every finite
prime-product interval sum. -/
theorem weightedPrimeProductSum_le_primeIndicator
    {weight : ℕ → ℝ} (hminorant : IsPrimeMinorant weight)
    (P x h : ℝ) :
    weightedPrimeProductSum weight P x h ≤
      weightedPrimeProductSum realPrimeIndicator P x h :=
  weightedPrimeProductSum_mono hminorant P x h

/-- A lower bound proved for the minorant is therefore also a lower bound
for the corresponding prime-pair sum. -/
theorem lowerBound_primeIndicator_of_minorant
    {weight : ℕ → ℝ} (hminorant : IsPrimeMinorant weight)
    {P x h lower : ℝ}
    (hlower : lower ≤ weightedPrimeProductSum weight P x h) :
    lower ≤ weightedPrimeProductSum realPrimeIndicator P x h :=
  hlower.trans (weightedPrimeProductSum_le_primeIndicator hminorant P x h)

/-! ## Exact application of the published pointwise theorem -/

/-- The local-range formulation obtained from the printed
[MT23, Theorem 2.1(i)].  The apparently unused `h,h₁,P₁` definitions are
retained because they belong to the theorem's common printed setup; no part
of Theorem 2.1(ii) or (iii) is included here. -/
def PrintedMinorantOnRangeStatement : Prop :=
  ∃ εₘₐₓ : ℝ, 0 < εₘₐₓ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∀ X : ℝ, 3 ≤ X →
        let c : ℝ := 21 / 10
        let _h : ℝ := (Real.log X) ^ c
        let _h₁ : ℝ := X ^ (99 / 100 : ℝ)
        ∀ a : ℝ, c - 1 - 1 / 10000 ≤ a → a ≤ c - 1 →
          let _P₁ : ℝ := (Real.log X) ^ a
          IsPrimeMinorantOnMatomakiTeravainenRange
            (matomakiTeravainenMinorant X ε) X

/-- The newly typed source theorem supplies exactly the local minorant
interface for the four-term minorant in its printed parameter range. -/
theorem printedMinorantOnRange_of_matomakiTeravainenTheoremTwoOnePartOne
    (hsource : MatomakiTeravainenTheoremTwoOnePartOneStatement) :
    PrintedMinorantOnRangeStatement := by
  obtain ⟨εₘₐₓ, hεₘₐₓ, hsource⟩ := hsource
  refine ⟨εₘₐₓ, hεₘₐₓ, ?_⟩
  intro ε hε hεUpper X hX
  dsimp only
  intro a haLower haUpper
  dsimp only [IsPrimeMinorantOnMatomakiTeravainenRange, IsPrimeMinorantOn]
  intro n hnLower hnUpper
  rw [realPrimeIndicator_eq_matomakiTeravainenPrimeIndicator]
  exact hsource ε hε hεUpper X hX a haLower haUpper n hnLower hnUpper

/-! ## Exact long-interval target -/

/-- The explicit long-interval lower bound `(minorant-long)` for one dyadic
prime block.  It is a predicate, not an assumption; below it is supplied on
the exact printed parameter range by [MT23, Theorem 2.1(ii)]. -/
def HasLongIntervalMinorantLowerBound
    (weight : ℕ → ℝ) (X P : ℝ) : Prop :=
  ∀ x : ℝ, X < x → x ≤ 2 * X →
    (X ^ (99 / 100 : ℝ)) /
        (200 * Real.log P * Real.log X) ≤
      weightedPrimeProductSum weight P x (X ^ (99 / 100 : ℝ))

/-- The long-interval conclusion of [MT23, Theorem 2.1(ii)], transcribed
into the project's `HasLongIntervalMinorantLowerBound` interface without
enlarging the source's parameter range.  In particular, `c` remains fixed
at `2.1`, `a` remains in the printed interval of width `1/10000`, and the
threshold for `X` is allowed to depend on the fixed small `ε`. -/
def PrintedLongIntervalMinorantLowerBoundStatement : Prop :=
  ∃ εₘₐₓ : ℝ, 0 < εₘₐₓ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∃ X₀ : ℝ, 3 ≤ X₀ ∧
        ∀ X : ℝ, X₀ ≤ X →
          let c : ℝ := 21 / 10
          let _h : ℝ := (Real.log X) ^ c
          let _h₁ : ℝ := X ^ (99 / 100 : ℝ)
          ∀ a : ℝ, c - 1 - 1 / 10000 ≤ a → a ≤ c - 1 →
            let P₁ : ℝ := (Real.log X) ^ a
            HasLongIntervalMinorantLowerBound
              (matomakiTeravainenMinorant X ε) X P₁

/-- The exact cited theorem supplies the project's one-block long lower
bound on precisely its published range.  The proof is only a change of
notation: `weightedPrimeProductSum_eq_matomakiTeravainen` identifies the
finite sum used here with the source-scoped sum in `Assumptions`. -/
theorem printedLongIntervalMinorantLowerBound_of_matomakiTeravainenTheoremTwoOnePartTwo
    (hsource : MatomakiTeravainenTheoremTwoOnePartTwoStatement) :
    PrintedLongIntervalMinorantLowerBoundStatement := by
  obtain ⟨εₘₐₓ, hεₘₐₓ, hsource⟩ := hsource
  refine ⟨εₘₐₓ, hεₘₐₓ, ?_⟩
  intro ε hε hεUpper
  obtain ⟨X₀, hX₀, hsource⟩ := hsource ε hε hεUpper
  refine ⟨X₀, hX₀, ?_⟩
  intro X hX
  dsimp only
  intro a haLower haUpper
  dsimp only [HasLongIntervalMinorantLowerBound]
  intro x hxLower hxUpper
  rw [weightedPrimeProductSum_eq_matomakiTeravainen]
  exact hsource X hX a haLower haUpper x hxLower hxUpper

/-- Pointwise normalized form used when the dyadic blocks are summed. -/
theorem normalized_longAverage_lower_bound
    {weight : ℕ → ℝ} {X P x : ℝ}
    (hX : 0 < X)
    (hlong : HasLongIntervalMinorantLowerBound weight X P)
    (hxLower : X < x) (hxUpper : x ≤ 2 * X) :
    1 / (200 * Real.log P * Real.log X) ≤
      weightedPrimeProductAverage weight P x (X ^ (99 / 100 : ℝ)) := by
  have hh : 0 < X ^ (99 / 100 : ℝ) := Real.rpow_pos_of_pos hX _
  rw [weightedPrimeProductAverage]
  apply (le_div_iff₀ hh).2
  have h := hlong x hxLower hxUpper
  convert h using 1
  ring

/-- Combining the exact long lower bound with minorant domination gives the
same normalized lower bound for genuine prime pairs. -/
theorem normalized_primeIndicator_lower_bound_of_minorant
    {weight : ℕ → ℝ} {X P x : ℝ}
    (hX : 0 < X) (hminorant : IsPrimeMinorant weight)
    (hlong : HasLongIntervalMinorantLowerBound weight X P)
    (hxLower : X < x) (hxUpper : x ≤ 2 * X) :
    1 / (200 * Real.log P * Real.log X) ≤
      weightedPrimeProductAverage realPrimeIndicator P x
        (X ^ (99 / 100 : ℝ)) := by
  have hh : 0 < X ^ (99 / 100 : ℝ) := Real.rpow_pos_of_pos hX _
  rw [weightedPrimeProductAverage]
  apply (le_div_iff₀ hh).2
  have h := (hlong x hxLower hxUpper).trans
    (weightedPrimeProductSum_le_primeIndicator hminorant P x
      (X ^ (99 / 100 : ℝ)))
  convert h using 1
  ring

def longIntervalMinorantModule : ProofModule :=
  { name := "Completion.LongIntervalMinorant"
    paperLocation := "Section 7.2, long-interval lower bound [MT23, Theorem 2.1(ii)]"
    purpose :=
      "Apply the exact MT23 pointwise minorant and long-interval theorem on their printed ranges, and transfer local domination to prime-product sums."
    dependsOn :=
      [ "Assumptions.matomakiTeravainenTheoremTwoOnePartOne",
        "Assumptions.matomakiTeravainenTheoremTwoOnePartTwo",
        "Assumptions.mertensSecondTheorem" ]
    status := .proved }

end

end Completion
end ExactSemiprimes
