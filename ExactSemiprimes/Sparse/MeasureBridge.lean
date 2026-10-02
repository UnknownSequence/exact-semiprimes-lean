import ExactSemiprimes.Sparse.SupportGeometry

/-!
# From sparse mean values to magnitude-bin measure bounds

The Heath--Brown input controls an integral.  The paper uses it on a set
where both factors have pointwise lower bounds.  This module records that
measure-theoretic conversion explicitly.
-/

namespace ExactSemiprimes
namespace Sparse

open MeasureTheory

noncomputable section

/-- Pointwise lower bounds for two complex functions turn their product
mean square into a lower bound proportional to the measure of the set. -/
theorem lowerSquares_mul_measureReal_le_setIntegral
    {E : Set ℝ} (hE : MeasurableSet E) (hEfinite : volume E ≠ ⊤)
    {Q A : ℝ → ℂ} {q a : ℝ}
    (hq : 0 ≤ q) (ha : 0 ≤ a)
    (hQ : ∀ t ∈ E, q ≤ ‖Q t‖)
    (hA : ∀ t ∈ E, a ≤ ‖A t‖)
    (hint : IntegrableOn
      (fun t ↦ ‖Q t‖ ^ (2 : ℕ) * ‖A t‖ ^ (2 : ℕ)) E) :
    (q ^ (2 : ℕ) * a ^ (2 : ℕ)) * volume.real E ≤
      ∫ t in E, ‖Q t‖ ^ (2 : ℕ) * ‖A t‖ ^ (2 : ℕ) := by
  apply setIntegral_ge_of_const_le_real hE hEfinite _ hint
  intro t ht
  exact mul_le_mul
    (pow_le_pow_left₀ hq (hQ t ht) 2)
    (pow_le_pow_left₀ ha (hA t ht) 2)
    (sq_nonneg a) (sq_nonneg ‖Q t‖)

/-- Division form used in the magnitude-bin argument.  An upper bound for
the sparse mean-value integral and positive pointwise lower bounds give an
explicit upper bound for the measure of the bin. -/
theorem measureReal_le_sparseIntegralBound_div
    {E : Set ℝ} (hE : MeasurableSet E) (hEfinite : volume E ≠ ⊤)
    {Q A : ℝ → ℂ} {q a I : ℝ}
    (hq : 0 < q) (ha : 0 < a)
    (hQ : ∀ t ∈ E, q ≤ ‖Q t‖)
    (hA : ∀ t ∈ E, a ≤ ‖A t‖)
    (hint : IntegrableOn
      (fun t ↦ ‖Q t‖ ^ (2 : ℕ) * ‖A t‖ ^ (2 : ℕ)) E)
    (hupper :
      (∫ t in E, ‖Q t‖ ^ (2 : ℕ) * ‖A t‖ ^ (2 : ℕ)) ≤ I) :
    volume.real E ≤ I / (q ^ (2 : ℕ) * a ^ (2 : ℕ)) := by
  have hlower := lowerSquares_mul_measureReal_le_setIntegral
    hE hEfinite hq.le ha.le hQ hA hint
  apply (le_div_iff₀ (mul_pos (sq_pos_of_pos hq) (sq_pos_of_pos ha))).2
  simpa only [mul_comm] using hlower.trans hupper

/-- Metadata for the integral-to-measure conversion used by both sparse
branches. -/
def measureBridgeModule : ProofModule :=
  { name := "Sparse.MeasureBridge"
    paperLocation := "Section 6.1, passage from the Heath--Brown mean value to |V_{σ₁,σ₂}|"
    purpose :=
      "Convert a sparse product mean-value upper bound and pointwise magnitude-bin lower bounds into an explicit measure bound."
    dependsOn := ["Sparse.SupportGeometry", "Mathlib set-integral monotonicity"]
    status := .proved }

end

end Sparse
end ExactSemiprimes
