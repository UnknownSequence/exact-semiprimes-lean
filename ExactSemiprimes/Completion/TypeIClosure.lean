import ExactSemiprimes.Completion.PerronTarget
import ExactSemiprimes.Assumptions

/-! # Closure of Type-I convolution components -/

namespace ExactSemiprimes
namespace Completion

noncomputable section

/-! The imported Deshouillers--Iwaniec estimate is kept outside the trusted
kernel.  The following lemmas check the power calculation made after that
estimate is inserted. -/

/-- With the paper's choice `L=X^(1/10)`, its nontrivial Type-I factor is
exactly `X^{-(1-1/a)/20}`. -/
theorem typeI_length_power_identity {X a : ℝ} (hX : 0 < X) :
    (X ^ (1 / 10 : ℝ)) ^ (-(1 - 1 / a) / 2) =
      X ^ (-(1 - 1 / a) / 20) := by
  rw [← Real.rpow_mul hX.le]
  congr 1
  ring

/-- The Type-I exponent has a genuine negative margin for every `a>1`. -/
theorem typeI_saving_positive {a : ℝ} (ha : 1 < a) :
    0 < (1 - 1 / a) / 20 := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hinv : 1 / a < 1 := by
    rw [div_lt_one ha0]
    exact ha
  positivity

/-- Any explicitly reserved error smaller than the Type-I margin leaves a
negative power of the main scale. -/
theorem typeI_exponent_remains_negative {a error : ℝ}
    (herror : error < (1 - 1 / a) / 20) :
    -(1 - 1 / a) / 20 + error < 0 := by
  linarith

/-- A convenient exact power-saving form of the preceding exponent check. -/
theorem typeI_power_bound_with_margin
    {X a error κ : ℝ} (hX : 1 ≤ X)
    (hκ : κ ≤ (1 - 1 / a) / 20 - error) :
    X ^ (-(1 - 1 / a) / 20 + error) ≤ X ^ (-κ) := by
  apply Real.rpow_le_rpow_of_exponent_le hX
  linarith

def typeIClosureModule : ProofModule :=
  { name := "Completion.TypeIClosure"
    paperLocation := "Proof of Proposition 7.1, Type-I power check"
    purpose :=
      "Verify the exact Type-I exponent and its error margin. The source factorization, analytic insertion, and finite-slice layer are tracked separately in TypeIComponentClosure."
    dependsOn :=
      ["Completion.PerronTarget", "Assumptions.deshouillersIwaniecEquationFourteen"]
    status := .proved }

end

end Completion
end ExactSemiprimes
