import ExactSemiprimes.Completion.StructuredPrimeFactors

namespace ExactSemiprimes
namespace Completion

noncomputable section

/-- The real-variable specialization of Harman's two printed terms at the
paper scales.  The two `hscale` hypotheses are eventually supplied by
`eventually_harman_scale_arithmetic` in the companion scratch file. -/
theorem harman_numeric_at_paper_scales_of_arithmetic
    {X Q t : ℝ}
    (hX : Real.exp (Real.exp 1) ≤ X)
    (hQlower :
      Real.exp
          (Real.log X /
            (Real.log (Real.log X)) ^ (3 : ℕ)) ≤ Q)
    (hQupper : Q ≤ X)
    (htlower : X ^ (1 / 1000 : ℝ) ≤ t)
    (htupper : t ≤ X)
    (htLarge : Real.exp 1 ≤ t)
    (hscaleOne :
      4 * (Real.log (Real.log X)) ^ (3 : ℕ) ≤
        (Real.log X) ^ (1 / 5 : ℝ))
    (hscaleTwo :
      3 * Real.log (Real.log X) +
          4 * (Real.log X) ^ (1 / 10 : ℝ) ≤
        (1 / 1000 : ℝ) * Real.log X) :
    4 * (Real.log X) ^ (1 / 10 : ℝ) ≤
          Real.log Q / (Real.log t) ^ (7 / 10 : ℝ) ∧
      (Real.log Q) ^ (3 : ℕ) / t ≤
        Real.exp (-4 * (Real.log X) ^ (1 / 10 : ℝ)) := by
  have hXone : 1 < X :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hX
  have hL : 0 < Real.log X := Real.log_pos hXone
  have hLL : 0 < Real.log (Real.log X) := by
    have hlogXge : Real.exp 1 ≤ Real.log X := by
      rw [← Real.log_exp (Real.exp 1)]
      exact Real.log_le_log (Real.exp_pos _) hX
    exact Real.log_pos (by linarith [Real.exp_one_gt_two])
  have hQpos : 0 < Q :=
    (Real.exp_pos _).trans_le hQlower
  have htpos : 0 < t := (Real.exp_pos 1).trans_le htLarge
  have hlogQLower :
      Real.log X / (Real.log (Real.log X)) ^ (3 : ℕ) ≤
        Real.log Q := by
    rw [← Real.log_exp
      (Real.log X / (Real.log (Real.log X)) ^ (3 : ℕ))]
    exact Real.log_le_log (Real.exp_pos _) hQlower
  have hlogQUpper : Real.log Q ≤ Real.log X :=
    Real.log_le_log hQpos hQupper
  have hlogtPos : 0 < Real.log t :=
    Real.log_pos ((Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le htLarge)
  have hlogtUpper : Real.log t ≤ Real.log X :=
    Real.log_le_log htpos htupper
  have hdenomUpper :
      (Real.log t) ^ (7 / 10 : ℝ) ≤
        (Real.log X) ^ (7 / 10 : ℝ) :=
    Real.rpow_le_rpow hlogtPos.le hlogtUpper (by norm_num)
  have hLLcubePos :
      0 < (Real.log (Real.log X)) ^ (3 : ℕ) := by positivity
  have hbaseRatio :
      4 * (Real.log X) ^ (4 / 5 : ℝ) ≤
        Real.log X / (Real.log (Real.log X)) ^ (3 : ℕ) := by
    rw [le_div_iff₀ hLLcubePos]
    calc
      4 * (Real.log X) ^ (4 / 5 : ℝ) *
            (Real.log (Real.log X)) ^ (3 : ℕ) =
          (Real.log X) ^ (4 / 5 : ℝ) *
            (4 * (Real.log (Real.log X)) ^ (3 : ℕ)) := by ring
      _ ≤ (Real.log X) ^ (4 / 5 : ℝ) *
            (Real.log X) ^ (1 / 5 : ℝ) :=
        mul_le_mul_of_nonneg_left hscaleOne
          (Real.rpow_nonneg hL.le _)
      _ = Real.log X := by
        rw [← Real.rpow_add hL]
        norm_num
  have hYdenom :
      4 * (Real.log X) ^ (1 / 10 : ℝ) *
          (Real.log t) ^ (7 / 10 : ℝ) ≤ Real.log Q := by
    calc
      4 * (Real.log X) ^ (1 / 10 : ℝ) *
          (Real.log t) ^ (7 / 10 : ℝ) ≤
        4 * (Real.log X) ^ (1 / 10 : ℝ) *
          (Real.log X) ^ (7 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hdenomUpper
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hL.le _))
      _ = 4 * (Real.log X) ^ (4 / 5 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hL]
        norm_num
      _ ≤ Real.log X /
          (Real.log (Real.log X)) ^ (3 : ℕ) := hbaseRatio
      _ ≤ Real.log Q := hlogQLower
  constructor
  · exact (le_div_iff₀ (Real.rpow_pos_of_pos hlogtPos _)).2 hYdenom
  · have hlogQNonneg : 0 ≤ Real.log Q := by
      exact hlogQLower.trans' (div_pos hL hLLcubePos).le
    have hcube :
        (Real.log Q) ^ (3 : ℕ) ≤ (Real.log X) ^ (3 : ℕ) :=
      pow_le_pow_left₀ hlogQNonneg hlogQUpper 3
    have hdiv :
        (Real.log Q) ^ (3 : ℕ) / t ≤
          (Real.log X) ^ (3 : ℕ) / X ^ (1 / 1000 : ℝ) := by
      exact div_le_div₀ (pow_nonneg hL.le 3) hcube
        (Real.rpow_pos_of_pos (zero_lt_one.trans hXone) _)
        htlower
    apply hdiv.trans
    have hpowExp :
        (Real.log X) ^ (3 : ℕ) =
          Real.exp (3 * Real.log (Real.log X)) := by
      rw [show (3 : ℝ) * Real.log (Real.log X) =
        Real.log ((Real.log X) ^ (3 : ℕ)) by
          rw [Real.log_pow]
          ring,
        Real.exp_log]
      positivity
    have hXrpowExp :
        X ^ (1 / 1000 : ℝ) =
          Real.exp ((1 / 1000 : ℝ) * Real.log X) := by
      rw [Real.rpow_def_of_pos (zero_lt_one.trans hXone)]
      congr 1
      ring
    rw [hpowExp, hXrpowExp, ← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    linarith


def harmanNumericPaperScaleModule : ProofModule :=
  { name := "Completion.HarmanNumericPaperScale"
    paperLocation := "Proposition 7.1, dyadic prime-polynomial estimate"
    purpose :=
      "Convert the paper's Q- and t-range hypotheses plus two eventual growth inequalities into the two numeric hypotheses of Harman's dyadic exponential-decay bound."
    dependsOn := ["Completion.StructuredPrimeFactors"]
    status := .proved }

end
end Completion
end ExactSemiprimes

