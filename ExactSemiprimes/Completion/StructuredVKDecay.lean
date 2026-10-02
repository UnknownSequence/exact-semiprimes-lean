import ExactSemiprimes.Completion.StructuredPrimeFactors
import ExactSemiprimes.Assumptions

/-! # Vinogradov--Korobov decay for the structured Type-II factor

This module is the source-faithful bridge from the published estimate
[MT23, equation (5.6)] to the structured short-prime product used by the
formalized Type-II argument.  The only internal ingredient is the exact
finite-fibre identity proved in `Completion.StructuredPrimeFactors`.
-/

namespace ExactSemiprimes
namespace Completion

noncomputable section

/-- The precise analytic decay needed in MT23 equation (5.6), expressed in
terms of the product of the short prime polynomials. -/
def StructuredShortSegmentDecayStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∀ A : ℝ, 5 ≤ A →
      ∃ X₀ C : ℝ, 3 ≤ X₀ ∧ 0 < C ∧
        ∀ (X M₁ t : ℝ) (R : ℕ) (Q : Fin R → ℝ), X₀ ≤ X →
          let z₀ : ℝ :=
            Real.exp
              (Real.log X / (Real.log (Real.log X)) ^ (3 : ℕ))
          let z : ℝ := X ^ (2 / 11 : ℝ)
          let delta : ℝ := (Real.log X) ^ (-10 * A)
          let T₀ : ℝ := X ^ (1 / 1000 : ℝ)
          1 ≤ R →
          R ≤ ⌊Real.log z / Real.log z₀⌋₊ →
          (∀ j : Fin R, z₀ ≤ Q j ∧ Q j < z) →
          (∏ j, Q j) = M₁ →
          X ^ (epsilon / 2) ≤ M₁ → M₁ ≤ z →
          T₀ ≤ t → t ≤ X →
          ‖structuredShortPrimeProduct Q delta t‖ ≤
            C * Real.exp (-2 * (Real.log X) ^ (1 / 10 : ℝ))

/-- The published coefficient-polynomial estimate (5.6) implies the exact
structured-product formulation.  This is a deterministic consequence of
the finite-fibre identity; no additional Fourier/Perron projector is
required. -/
theorem structuredShortSegmentDecay_of_matomakiTeravainenEquationFiveSix
    (hFiveSix : MatomakiTeravainenEquationFiveSixStatement) :
    StructuredShortSegmentDecayStatement := by
  intro epsilon hepsilon A hA
  obtain ⟨X₀, C, hX₀, hC, hsource⟩ := hFiveSix epsilon hepsilon A hA
  refine ⟨X₀, C, hX₀, hC, ?_⟩
  intro X M₁ t R Q hX
  dsimp only
  intro hR hRupper hQ hprod hMlower hMupper htLower htUpper
  have hXthree : 3 ≤ X := hX₀.trans hX
  have hXone : 1 < X := by linarith
  have hdelta : 0 ≤ (Real.log X) ^ (-10 * A) :=
    Real.rpow_nonneg (Real.log_nonneg hXone.le) _
  have hz₀pos :
      0 < Real.exp
        (Real.log X / (Real.log (Real.log X)) ^ (3 : ℕ)) :=
    Real.exp_pos _
  have hQpos : ∀ j : Fin R, 0 < Q j := fun j ↦
    hz₀pos.trans_le (hQ j).1
  rw [← structuredTypeIICoefficient_polynomial_eq_shortPrimeProduct
    hdelta hR hQpos hprod]
  exact hsource X M₁ t R Q hX hR hRupper hQ hprod
    hMlower hMupper htLower htUpper

/-- The same decay, exposed directly from the global explicit assumption
bundle used by the final theorem. -/
theorem structuredShortSegmentDecay_of_inputs
    (inputs : ExternalInputs) : StructuredShortSegmentDecayStatement :=
  structuredShortSegmentDecay_of_matomakiTeravainenEquationFiveSix
    inputs.matomakiTeravainenEquationFiveSix

def structuredVKDecayModule : ProofModule :=
  { name := "Completion.StructuredVKDecay"
    paperLocation := "MT23 equation (5.6), structured Type-II factor"
    purpose :=
      "Transport the published Vinogradov--Korobov coefficient-polynomial estimate across the proved finite-fibre identity to the exact structured short-prime product."
    dependsOn :=
      [ "Assumptions.matomakiTeravainenEquationFiveSix",
        "Completion.StructuredPrimeFactors" ]
    status := .proved }

end
end Completion
end ExactSemiprimes
