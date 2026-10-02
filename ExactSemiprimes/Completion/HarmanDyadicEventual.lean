import ExactSemiprimes.Completion.HarmanScaleArithmetic
import ExactSemiprimes.Completion.HarmanNumericPaperScale

namespace ExactSemiprimes
namespace Completion

open Filter

noncomputable section

/-- The full dyadic (not short-segment) prime polynomial has the required
paper-scale cancellation uniformly throughout the relevant box. -/
theorem eventually_harmanDyadic_at_paper_scales
    (hHarman : HarmanLemmaOneFiveStatement) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ X : ℝ in atTop,
        ∀ (Q t : ℝ),
          Real.exp
              (Real.log X /
                (Real.log (Real.log X)) ^ (3 : ℕ)) ≤ Q →
          Q ≤ X →
          X ^ (1 / 1000 : ℝ) ≤ t → t ≤ X →
          ‖harmanPrimePolynomial Q 1 t‖ ≤
            C * Real.exp (-4 * (Real.log X) ^ (1 / 10 : ℝ)) := by
  obtain ⟨C, hC, hHarmanPoint⟩ :=
    harman_dyadic_exp_decay_of_numeric_scales hHarman
  have htLarge : ∀ᶠ X : ℝ in atTop,
      Real.exp 1 ≤ X ^ (1 / 1000 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 1000)).eventually_ge_atTop _
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [eventually_harman_scale_arithmetic, htLarge,
    eventually_ge_atTop (Real.exp (Real.exp 1))] with
      X hscale htLargeX hX
  intro Q t hQlower hQupper htLower htUpper
  have htLarge' : Real.exp 1 ≤ t := htLargeX.trans htLower
  have hXone : 1 < X :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hX
  have hLexp : Real.exp 1 ≤ Real.log X := by
    rw [← Real.log_exp (Real.exp 1)]
    exact Real.log_le_log (Real.exp_pos _) hX
  have hLstrict : 1 < Real.log X := by
    linarith [Real.exp_one_gt_two]
  have hL : 1 ≤ Real.log X := hLstrict.le
  have hLL : 0 < Real.log (Real.log X) := Real.log_pos hLstrict
  have hLpower : (Real.log X) ^ (1 / 5 : ℝ) ≤ Real.log X := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1 / 5 : ℝ) ≤ 1)
  have hfour :
      4 ≤ Real.log X / (Real.log (Real.log X)) ^ (3 : ℕ) := by
    rw [le_div_iff₀ (by positivity :
      0 < (Real.log (Real.log X)) ^ (3 : ℕ))]
    exact hscale.1.trans hLpower
  have hQtwo : 2 ≤ Q := by
    have htwoexp : 2 ≤ Real.exp 4 := by
      exact (Real.exp_one_gt_two.le).trans
        (Real.exp_le_exp.mpr (by norm_num))
    have hexp : Real.exp 4 ≤
        Real.exp
          (Real.log X /
            (Real.log (Real.log X)) ^ (3 : ℕ)) :=
      Real.exp_le_exp.mpr hfour
    exact htwoexp.trans (hexp.trans hQlower)
  obtain ⟨hfirst, hsecond⟩ :=
    harman_numeric_at_paper_scales_of_arithmetic hX hQlower hQupper
      htLower htUpper htLarge' hscale.1 hscale.2
  simpa only [mul_assoc] using
    hHarmanPoint Q t ((Real.log X) ^ (1 / 10 : ℝ))
      htLarge' hQtwo (Real.rpow_nonneg (Real.log_nonneg hXone.le) _)
      hfirst hsecond


def harmanDyadicEventualModule : ProofModule :=
  { name := "Completion.HarmanDyadicEventual"
    paperLocation := "Proposition 7.1, full-dyadic VK surrogate"
    purpose :=
      "Derive the uniform paper-scale exponential decay for Harman's full dyadic prime polynomial as an independent consequence of the literal dyadic source statement."
    dependsOn :=
      [ "Completion.StructuredPrimeFactors",
        "Completion.HarmanScaleArithmetic",
        "Completion.HarmanNumericPaperScale" ]
    status := .proved }

end
end Completion
end ExactSemiprimes
