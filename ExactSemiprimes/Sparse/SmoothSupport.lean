import ExactSemiprimes.Sparse.PrimePowerPolynomial
import ExactSemiprimes.Assumptions

/-! # Smooth-number bound for the sparse support -/

namespace ExactSemiprimes
namespace Sparse

open Filter

noncomputable section

/-!
The Hildebrand--Tenenbaum input is stated as convergence of the logarithmic
exponent.  The first lemma below records the elementary pointwise passage
from a strict upper bound for that exponent to a power bound.  The zero-count
case is separated explicitly: taking a logarithm loses the distinction
between zero and one in Mathlib, but the desired inequality is then immediate.
-/

/-- A strict upper bound for the logarithmic exponent gives the corresponding
power bound.  This formulation explicitly handles the possible zero-count
case before applying `Real.le_rpow_iff_log_le` to a positive count. -/
theorem logPowerSmoothNumberCount_le_rpow_of_logRatio_lt
    (a exponent : ℝ) {X : ℕ} (hX : 1 < X)
    (hRatio :
      Real.log (logPowerSmoothNumberCount a X : ℝ) /
          Real.log (X : ℝ) < exponent) :
    (logPowerSmoothNumberCount a X : ℝ) ≤ (X : ℝ) ^ exponent := by
  have hXpos : 0 < (X : ℝ) := by positivity
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hlogBound :
      Real.log (logPowerSmoothNumberCount a X : ℝ) <
        exponent * Real.log (X : ℝ) :=
    (div_lt_iff₀ hlogX).mp hRatio
  by_cases hCount : logPowerSmoothNumberCount a X = 0
  · rw [hCount, Nat.cast_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg X) exponent
  · have hCountPos : 0 < (logPowerSmoothNumberCount a X : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hCount
    exact (Real.le_rpow_iff_log_le hCountPos hXpos).2 hlogBound.le

/-- Fixed-`a` power-saving consequence of the cited
Hildebrand--Tenenbaum logarithmic limit.  Every positive slack is allowed,
and the assertion is uniform in all sufficiently large natural cutoffs `X`.
-/
theorem eventually_logPowerSmoothNumberCount_le_rpow
    (hHT : HildebrandTenenbaumCorollaryOneThreeStatement)
    {a δ : ℝ} (ha : 1 < a) (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop,
      (logPowerSmoothNumberCount a X : ℝ) ≤
        (X : ℝ) ^ (1 - 1 / a + δ) := by
  have hLimit := hHT a ha
  have hExponent :
      ∀ᶠ X : ℕ in atTop,
        Real.log (logPowerSmoothNumberCount a X : ℝ) /
            Real.log (X : ℝ) < 1 - 1 / a + δ :=
    (tendsto_order.1 hLimit).2 _ (by linarith)
  filter_upwards [hExponent, eventually_ge_atTop 2] with X hRatio hX
  exact logPowerSmoothNumberCount_le_rpow_of_logRatio_lt
    a (1 - 1 / a + δ) (by omega) hRatio

/-- Threshold form of `eventually_logPowerSmoothNumberCount_le_rpow`, useful
for paper-level substitutions that name a single lower cutoff. -/
theorem exists_logPowerSmoothNumberCount_le_rpow
    (hHT : HildebrandTenenbaumCorollaryOneThreeStatement)
    {a δ : ℝ} (ha : 1 < a) (hδ : 0 < δ) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (logPowerSmoothNumberCount a X : ℝ) ≤
        (X : ℝ) ^ (1 - 1 / a + δ) := by
  exact (eventually_atTop.1
    (eventually_logPowerSmoothNumberCount_le_rpow hHT ha hδ))

def smoothSupportModule : ProofModule :=
  { name := "Sparse.SmoothSupport"
    paperLocation := "Section 6.1, smooth-support estimate"
    purpose :=
      "Derive the fixed-a bound Ψ(X,(log X)^a) ≤ X^(1-1/a+δ) for every positive slack δ from the cited Hildebrand--Tenenbaum limit."
    dependsOn :=
      [ "Sparse.PrimePowerPolynomial",
        "Assumptions.hildebrandTenenbaumCorollaryOneThree" ]
    status := .proved }

end

end Sparse
end ExactSemiprimes
