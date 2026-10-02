import ExactSemiprimes.Definitions

/-! # Exact rational arithmetic for the exponent `2.092` -/

namespace ExactSemiprimes
namespace Results

/-- The lower endpoint `1.0919` of the explicit prime window lies strictly
above the threshold `1925/1763` of the Type II argument. -/
theorem explicitMargin :
    (10919 / 10000 : ℚ) - 1925 / 1763 = 197 / 17630000 := by
  norm_num

/-- The advertised decimal exponent lies strictly between the new threshold
`3688/1763`, the threshold `67/32` of the single-threshold argument, and the
previously published exponent `2.1`. -/
theorem cleanExponentOrder :
    (3688 / 1763 : ℚ) < 523 / 250 ∧ (523 / 250 : ℚ) < 67 / 32 ∧
      (67 / 32 : ℚ) < 21 / 10 := by
  norm_num

/-- Exact room in the lower and upper buffers of the prime-factor window. -/
theorem cleanWindowOrder :
    (1091 / 1000 : ℚ) < 10919 / 10000 ∧
      (21839 / 20000 : ℚ) < 273 / 250 := by
  norm_num

/-- The decimal `2.092` is exactly `523 / 250`. -/
theorem cleanExponentValue : (2.092 : ℚ) = 523 / 250 := by
  norm_num

def explicitExponentArithmeticModule : ProofModule :=
  { name := "Results.ExplicitExponentArithmetic"
    paperLocation := "Section 7.3, identity 1.0919 - 1925/1763 = 197/17630000"
    purpose := "Verify the rational margins and both buffered prime-window inclusions."
    dependsOn := ["Definitions"]
    status := .proved }

end Results
end ExactSemiprimes
