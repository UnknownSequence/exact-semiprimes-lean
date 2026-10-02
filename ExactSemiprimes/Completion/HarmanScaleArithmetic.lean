import ExactSemiprimes.Completion.StructuredPrimeFactors

namespace ExactSemiprimes
namespace Completion

open Filter Asymptotics

noncomputable section

/-- The two elementary growth comparisons needed to specialize Harman's
printed dyadic estimate at the paper's scales. -/
theorem eventually_harman_scale_arithmetic :
    ∀ᶠ X : ℝ in atTop,
      4 * (Real.log (Real.log X)) ^ (3 : ℕ) ≤
          (Real.log X) ^ (1 / 5 : ℝ) ∧
      3 * Real.log (Real.log X) +
          4 * (Real.log X) ^ (1 / 10 : ℝ) ≤
        (1 / 1000 : ℝ) * Real.log X := by
  have hcubicRaw :=
    (isLittleO_log_rpow_rpow_atTop (3 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 5)).bound
      (by norm_num : (0 : ℝ) < 1 / 4)
  have hcubic := Real.tendsto_log_atTop.eventually hcubicRaw
  have hlogRaw :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).bound
      (by norm_num : (0 : ℝ) < 1 / 6000)
  have hlog := Real.tendsto_log_atTop.eventually hlogRaw
  have hsmallPower : ∀ᶠ X : ℝ in atTop,
      8000 ≤ (Real.log X) ^ (9 / 10 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 10)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop 8000
  filter_upwards [hcubic, hlog, hsmallPower,
    eventually_ge_atTop (Real.exp (Real.exp 1))] with
      X hcubicX hlogX hsmallPowerX hX
  have hXone : 1 < X :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hX
  have hL : 0 < Real.log X := Real.log_pos hXone
  have hLL : 0 ≤ Real.log (Real.log X) := by
    have hlogXge : Real.exp 1 ≤ Real.log X := by
      rw [← Real.log_exp (Real.exp 1)]
      exact Real.log_le_log (Real.exp_pos _) hX
    exact Real.log_nonneg (by linarith [Real.exp_one_gt_two])
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hLL _),
    Real.norm_of_nonneg (Real.rpow_nonneg hL.le _)] at hcubicX
  rw [Real.rpow_one, Real.norm_of_nonneg hLL,
    Real.norm_of_nonneg hL.le] at hlogX
  have hcubicFinal :
      4 * (Real.log (Real.log X)) ^ (3 : ℕ) ≤
        (Real.log X) ^ (1 / 5 : ℝ) := by
    have hrpowThree :
        (Real.log (Real.log X)) ^ (3 : ℝ) =
          (Real.log (Real.log X)) ^ (3 : ℕ) := by
      exact Real.rpow_natCast _ 3
    rw [hrpowThree] at hcubicX
    nlinarith
  have hsmallPowerFinal :
      8000 * (Real.log X) ^ (1 / 10 : ℝ) ≤ Real.log X := by
    have hmul := mul_le_mul_of_nonneg_right hsmallPowerX
      (Real.rpow_nonneg hL.le (1 / 10 : ℝ))
    calc
      8000 * (Real.log X) ^ (1 / 10 : ℝ) ≤
          (Real.log X) ^ (9 / 10 : ℝ) *
            (Real.log X) ^ (1 / 10 : ℝ) := by
        simpa [mul_comm] using hmul
      _ = Real.log X := by
        rw [← Real.rpow_add hL]
        norm_num
  constructor
  · exact hcubicFinal
  · nlinarith


def harmanScaleArithmeticModule : ProofModule :=
  { name := "Completion.HarmanScaleArithmetic"
    paperLocation := "Proposition 7.1, Vinogradov--Korobov scale arithmetic"
    purpose :=
      "Prove the eventual logarithmic comparisons needed to specialize Harman's dyadic estimate at the paper's parameter scales."
    dependsOn := ["Completion.StructuredPrimeFactors"]
    status := .proved }

end
end Completion
end ExactSemiprimes

