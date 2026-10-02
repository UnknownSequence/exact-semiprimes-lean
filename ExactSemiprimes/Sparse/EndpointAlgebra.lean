import ExactSemiprimes.Definitions

/-! # Algebra giving the endpoint a > 35/32 -/

namespace ExactSemiprimes
namespace Sparse

/-- Clearing the positive denominator turns the last sparse inequality into
the threshold `a > 6 / (5 + 2s)`. -/
theorem endpointThresholdIff {a s : ℝ} (ha : 0 < a)
    (hden : 0 < 5 + 2 * s) :
    1 / a < 5 * (1 - 1 / a) + 2 * s ↔ 6 / (5 + 2 * s) < a := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hleft : (1 / a) * a = 1 := by
    field_simp
  have hright : (5 * (1 - 1 / a) + 2 * s) * a =
      a * (5 + 2 * s) - 5 := by
    field_simp [ha0]
    ring
  constructor
  · intro h
    rw [div_lt_iff₀ hden]
    have h' := mul_lt_mul_of_pos_right h ha
    rw [hleft, hright] at h'
    linarith
  · intro h
    have h' : 6 < a * (5 + 2 * s) := (div_lt_iff₀ hden).mp h
    rw [div_lt_iff₀ ha]
    rw [hright]
    linarith

/-- The exact endpoint furnished by the hybrid large-values threshold. -/
theorem endpointThresholdValue :
    (6 / (5 + 2 * (17 / 70 : ℚ)) : ℚ) = 35 / 32 := by
  norm_num

/-- The algebraic heart of the two-branch sparse argument, with all `O(ε)`
losses removed.  Any strict room in `a > 6/(5+2s)` yields strict room in the
key exponent inequality. -/
theorem endpointKeyInequality {a s σ₁ σ₂ θ : ℝ}
    (ha : 0 < a) (hden : 0 < 5 + 2 * s)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hσ₁ : s ≤ σ₁) (hσ₂ : s ≤ σ₂)
    (hres : 1 - 1 / a ≤ θ * (1 - 2 * σ₁))
    (hath : 6 / (5 + 2 * s) < a) :
    1 / a < (5 - 8 * σ₁) * θ + 2 * σ₂ * (1 - θ) := by
  have hθcompl : 0 ≤ 1 - θ := by linarith
  have hsigma1term :
      θ * (1 - 2 * σ₁) ≤ θ * (1 - 2 * s) := by
    have := mul_le_mul_of_nonneg_left hσ₁ hθ0
    nlinarith
  have hsigma2term :
      2 * s * (1 - θ) ≤ 2 * σ₂ * (1 - θ) := by
    have := mul_le_mul_of_nonneg_right hσ₂ hθcompl
    nlinarith
  have hbase : 1 / a < 5 * (1 - 1 / a) + 2 * s :=
    (endpointThresholdIff ha hden).2 hath
  nlinarith

def endpointAlgebraModule : ProofModule :=
  { name := "Sparse.EndpointAlgebra"
    paperLocation := "Single-threshold argument (comparison with Section 6): rewrite through equation a > 35/32 + O(ε)"
    purpose := "Combine σⱼ ≥ 17/70-O(ε) with the residual inequality and solve for a."
    dependsOn := ["Definitions"]
    status := .proved }

end Sparse
end ExactSemiprimes
