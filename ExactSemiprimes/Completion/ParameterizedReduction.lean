import ExactSemiprimes.Completion.ComponentAssembly
import ExactSemiprimes.Completion.GeneralPerronReduction

/-! # Parameterized Matomäki--Teräväinen reduction (paper Proposition 7.1) -/

namespace ExactSemiprimes
namespace Completion

open scoped BigOperators
open MeasureTheory

noncomputable section

/-- The weighted sum over pairs `p,n` with `p` prime in `(P,2P]` and
`x < p*n ≤ x+h`.  Writing the inner interval after division by `p`
makes the sum manifestly finite. -/
def weightedPrimeProductSum (weight : ℕ → ℝ) (P x h : ℝ) : ℝ :=
  ∑ p ∈ dyadicPrimes P,
    ∑ n ∈ shortInterval (x / (p : ℝ)) (h / (p : ℝ)), weight n

/-- The normalized weighted short-interval average used in Proposition 7.1. -/
def weightedPrimeProductAverage (weight : ℕ → ℝ)
    (P x h : ℝ) : ℝ :=
  weightedPrimeProductSum weight P x h / h

/-- The exact short/long variance appearing in Proposition 7.1, before the
outer normalization by `X`. -/
def shortLongPrimeProductVariance (weight : ℕ → ℝ)
    (X P h h₁ : ℝ) : ℝ :=
  ∫ x in Set.Ioc X (2 * X),
    |weightedPrimeProductAverage weight P x h -
      weightedPrimeProductAverage weight P x h₁| ^ 2

/-! ## Connection with the published `c = 2.1` reduction -/

/-- Our finite prime-product sum is definitionally the sum used in the
source-scoped transcription of Matomäki--Teräväinen Lemma 3.1. -/
theorem weightedPrimeProductSum_eq_matomakiTeravainen
    (weight : ℕ → ℝ) (P x h : ℝ) :
    weightedPrimeProductSum weight P x h =
      matomakiTeravainenPrimeProductSum weight P x h :=
  rfl

/-- The only normalization difference between the internal variance and the
published one is that the source puts `1/X` in front of the integral. -/
theorem normalized_shortLongPrimeProductVariance_eq_matomakiTeravainen
    (weight : ℕ → ℝ) (X P h h₁ : ℝ) :
    shortLongPrimeProductVariance weight X P h h₁ / X =
      matomakiTeravainenShortLongVariance weight X P h h₁ := by
  simp only [shortLongPrimeProductVariance,
    weightedPrimeProductAverage, weightedPrimeProductSum_eq_matomakiTeravainen,
    matomakiTeravainenShortLongVariance]
  ring

/-- Fixed-scale closure of the generalized reduction after the exact
Parseval interface has been supplied.  This is the internal-variance version
of `variance_le_of_parsevalAtScale_and_cumulative`; no restriction on the
logarithmic exponents `a,c` occurs in this normalization step. -/
theorem normalized_shortLongVariance_le_of_parsevalAtScale_and_cumulative
    {weight : ℕ → ℝ} {X P h hlong T₀ K C L : ℝ}
    (hparseval : PerronParsevalAtScaleStatement
      weight X P h hlong T₀ K)
    (hcutoff : T₀ ≤ X / h) (hL : 0 < L)
    (hcumulative : ∀ U : ℝ, X / h ≤ U →
      perronProductIntegral weight X P U ≤
        C * (U / (X / h)) / L) :
    ∃ Cparseval : ℝ, 0 < Cparseval ∧
      shortLongPrimeProductVariance weight X P h hlong / X ≤
        Cparseval * (K ^ (2 : ℕ) / T₀ + C / L + 2 * C / L) := by
  obtain ⟨Cparseval, hCparseval, hvariance⟩ :=
    variance_le_of_parsevalAtScale_and_cumulative
      hparseval hcutoff hL hcumulative
  refine ⟨Cparseval, hCparseval, ?_⟩
  rw [normalized_shortLongPrimeProductVariance_eq_matomakiTeravainen]
  exact hvariance

/-- The exact part of the internal reduction already supplied by the printed
Matomäki--Teräväinen Lemma 3.1.  This deliberately retains the source's
fixed exponent `c = 2.1` and narrow `a`-window; the parameter extension in
`ParameterizedReductionStatement` remains a new proof obligation. -/
def PrintedParameterizedReductionStatement : Prop :=
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
              (∀ T : ℝ, X / h ≤ T →
                perronProductIntegral
                    (matomakiTeravainenMinorant X ε) X P₁ T ≤
                  Cdp * (T / (X / h)) / (Real.log X) ^ (2 + ε)) →
              shortLongPrimeProductVariance
                  (matomakiTeravainenMinorant X ε) X P₁ h h₁ / X ≤
                Cvar / (Real.log X) ^ (2 + ε)

/-- The exact cited Lemma 3.1 discharges the printed-range internal
reduction, with no strengthening of its quantifiers. -/
theorem printedParameterizedReduction_of_matomakiTeravainenLemmaThreeOne
    (hsource : MatomakiTeravainenLemmaThreeOneStatement) :
    PrintedParameterizedReductionStatement := by
  obtain ⟨εₘₐₓ, hεₘₐₓ, hsource⟩ := hsource
  refine ⟨εₘₐₓ, hεₘₐₓ, ?_⟩
  intro ε hε hεmax a haLower haUpper Cdp hCdp
  obtain ⟨Cvar, hCvar, hvariance⟩ :=
    hsource ε hε hεmax a haLower haUpper Cdp hCdp
  refine ⟨Cvar, hCvar, ?_⟩
  intro X hX
  dsimp only
  intro hperron
  rw [normalized_shortLongPrimeProductVariance_eq_matomakiTeravainen]
  apply hvariance X hX
  intro T hT
  rw [← perronProductIntegral_eq_matomakiTeravainen]
  exact hperron T hT

/-- The full mathematical target of Proposition 7.1 for a chosen family of
minorants.  The family is indexed by the natural scale `X`, because the
Harman minorant in the paper changes with `X`.  A separate module must
construct that family from equation (2.3) and prove that it satisfies this
target; it is not hidden as an external assumption here. -/
def ParameterizedReductionStatement
    (minorant : ℕ → ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ a c : ℝ,
        35 / 32 + η ≤ a → a ≤ 11 / 10 →
        a ≤ c - 1 → 2 + η < c →
        ∃ C : ℝ, 0 < C ∧
          ∃ X₀ : ℕ, 3 ≤ X₀ ∧
            ∀ X : ℕ, X₀ ≤ X →
              (shortLongPrimeProductVariance
                  (minorant X)
                  (X : ℝ)
                  ((Real.log (X : ℝ)) ^ a)
                  ((Real.log (X : ℝ)) ^ c)
                  ((X : ℝ) ^ (99 / 100 : ℝ))) / (X : ℝ) ≤
                C / (Real.log (X : ℝ)) ^ (2 + ε₀)

def parameterizedReductionModule : ProofModule :=
  { name := "Completion.ParameterizedReduction"
    paperLocation := "Proposition 7.1"
    purpose :=
      "Connect the exact published c=2.1 Perron reduction to the internal variance. The variance bound for the wider window is Final/BlockVariance.lean, using the labelled extension E1."
    dependsOn := ["Completion.PerronTarget", "Completion.ComponentAssembly"]
    status := .superseded }

end

end Completion
end ExactSemiprimes
