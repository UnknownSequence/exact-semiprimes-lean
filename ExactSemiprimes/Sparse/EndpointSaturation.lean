import ExactSemiprimes.Sparse.EndpointAlgebra

/-! # Exact saturation calculation at (s,a,θ) = (17/70,35/32,1/6) -/

namespace ExactSemiprimes
namespace Sparse

/-- At the limiting triple, the residual inequality is an equality. -/
theorem residualSaturation :
    (1 / 6 : ℚ) * (1 - 2 * (17 / 70)) = 1 - 1 / (35 / 32) := by
  norm_num

/-- At the limiting triple, the second-branch key inequality is also an
equality.  This is why the final theorem has a strict endpoint. -/
theorem keySaturation :
    (5 - 8 * (17 / 70 : ℚ)) * (1 / 6) +
        2 * (17 / 70) * (1 - 1 / 6) = 1 / (35 / 32) := by
  norm_num

def endpointSaturationModule : ProofModule :=
  { name := "Sparse.EndpointSaturation"
    paperLocation := "Single-threshold endpoint a > 35/32 (comparison with Section 6)"
    purpose := "Verify the rational identities explaining why the endpoint remains strict."
    dependsOn := ["Sparse.EndpointAlgebra"]
    status := .proved }

end Sparse
end ExactSemiprimes
