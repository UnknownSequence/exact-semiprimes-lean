import ExactSemiprimes.Definitions

/-! # Consequences of failure of the first sparse branch -/

namespace ExactSemiprimes
namespace Sparse

/-- A residual lower bound with positive left side forces the size exponent
`σ` below `1/2`.  The error term is explicit. -/
theorem sigma_lt_half_of_residual {a θ σ error : ℝ}
    (hθ : 0 ≤ θ) (hpositive : 0 < 1 - 1 / a - error)
    (hresidual : 1 - 1 / a - error ≤ θ * (1 - 2 * σ)) :
    σ < 1 / 2 := by
  by_contra h
  have hfactor : 1 - 2 * σ ≤ 0 := by linarith
  have hproduct : θ * (1 - 2 * σ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hθ hfactor
  linarith

/-- Replacing `σ` by a lower threshold `s` only enlarges the residual
right-hand side. -/
theorem residual_mono_lower_threshold {a θ σ s error : ℝ}
    (hθ : 0 ≤ θ) (hs : s ≤ σ)
    (hresidual : 1 - 1 / a - error ≤ θ * (1 - 2 * σ)) :
    1 - 1 / a - error ≤ θ * (1 - 2 * s) := by
  have hfactor : 1 - 2 * σ ≤ 1 - 2 * s := by linarith
  exact hresidual.trans (mul_le_mul_of_nonneg_left hfactor hθ)

def residualRangeModule : ProofModule :=
  { name := "Sparse.ResidualRange"
    paperLocation := "Single-threshold argument (comparison with Section 6): residual inequality θ(1-2σ₁) ≥ 1-1/a-O(ε)"
    purpose := "Extract σ₁ < 1/2 and the lower bounds needed in the second branch."
    dependsOn := ["Definitions"]
    status := .proved }

end Sparse
end ExactSemiprimes
