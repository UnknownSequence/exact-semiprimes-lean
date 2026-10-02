import ExactSemiprimes.TypeII.MediumFullAssembly

/-!
# Explicit reserve parameters for the outer Type-II assembly

This module fixes concrete fractions of the medium-bin cardinality saving.
The choices are deliberately elementary: the threshold shift is the smaller
of `eps` and `kappa/8`, the product-length loss is `kappa/8`, and the final
negative-power saving is `kappa/4`.  The lemmas below verify that these
choices simultaneously fit the hybrid threshold and exponent budgets.
-/

namespace ExactSemiprimes
namespace TypeII

noncomputable section

/-- Exponent spent absorbing the finite powered-slice loss. -/
def mediumThresholdShift (eps kappa : ℝ) : ℝ :=
  min eps (kappa / 8)

/-- Power loss used to absorb the logarithmic product error. -/
def mediumProductLoss (kappa : ℝ) : ℝ :=
  kappa / 8

/-- Negative power retained after all medium-bin losses. -/
def mediumResidualSaving (kappa : ℝ) : ℝ :=
  kappa / 4

theorem mediumThresholdShift_pos {eps kappa : ℝ}
    (heps : 0 < eps) (hkappa : 0 < kappa) :
    0 < mediumThresholdShift eps kappa := by
  exact lt_min heps (by positivity)

theorem mediumThresholdShift_le_eps (eps kappa : ℝ) :
    mediumThresholdShift eps kappa ≤ eps :=
  min_le_left _ _

theorem mediumThresholdShift_le_kappa_div_eight (eps kappa : ℝ) :
    mediumThresholdShift eps kappa ≤ kappa / 8 :=
  min_le_right _ _

theorem mediumProductLoss_pos {kappa : ℝ} (hkappa : 0 < kappa) :
    0 < mediumProductLoss kappa := by
  dsimp [mediumProductLoss]
  positivity

theorem mediumResidualSaving_pos {kappa : ℝ} (hkappa : 0 < kappa) :
    0 < mediumResidualSaving kappa := by
  dsimp [mediumResidualSaving]
  positivity

/-- The two losses and the retained saving fit inside `kappa` whenever the
relevant minimum magnitude exponent is at most one. -/
theorem medium_explicit_reserve_gap
    {eps kappa tau₁ tau₂ : ℝ}
    (hkappa : 0 < kappa)
    (htau₁ : 0 ≤ tau₁) (htau₂ : 0 ≤ tau₂)
    (hmin : min tau₁ tau₂ ≤ 1) :
    2 * mediumProductLoss kappa * min tau₁ tau₂ +
        mediumResidualSaving kappa ≤
      kappa - 2 * mediumThresholdShift eps kappa := by
  have hminNonneg : 0 ≤ min tau₁ tau₂ := le_min htau₁ htau₂
  have hweighted :
      (kappa / 4) * min tau₁ tau₂ ≤ kappa / 4 :=
    by
      simpa using mul_le_mul_of_nonneg_left hmin
        (by positivity : 0 ≤ kappa / 4)
  have hshift := mediumThresholdShift_le_kappa_div_eight eps kappa
  dsimp [mediumProductLoss, mediumResidualSaving]
  nlinarith

/-- The shifted hybrid-threshold condition itself gives the harmless
`min tau₁ tau₂ ≤ 1` input used by the reserve calculation.  This is where
the outer pointwise large-value hypothesis enters; the weaker `R₂`
lower-magnitude condition alone would not suffice. -/
theorem min_unshifted_le_one_of_shifted_hybrid_threshold
    {thresholdLoss eps shift tau₁ tau₂ : ℝ}
    (hthresholdLoss : 0 ≤ thresholdLoss) (heps : 0 ≤ eps)
    (hshift : 0 ≤ shift)
    (hupper : min (tau₁ + shift) tau₂ ≤
      17 / 70 - thresholdLoss * eps) :
    min tau₁ tau₂ ≤ 1 := by
  have hmono : min tau₁ tau₂ ≤ min (tau₁ + shift) tau₂ := by
    exact min_le_min (by linarith) le_rfl
  have hthreshold : 17 / 70 - thresholdLoss * eps ≤ 1 := by
    have hproduct : 0 ≤ thresholdLoss * eps :=
      mul_nonneg hthresholdLoss heps
    norm_num at hproduct ⊢
    linarith
  exact hmono.trans (hupper.trans hthreshold)

/-- Ready-to-use reserve gap after the shifted upper threshold has been
verified for an occupied bin. -/
theorem medium_explicit_reserve_gap_of_hybrid_threshold
    {thresholdLoss eps kappa tau₁ tau₂ : ℝ}
    (hthresholdLoss : 0 ≤ thresholdLoss) (heps : 0 ≤ eps)
    (hkappa : 0 < kappa)
    (htau₁ : 0 ≤ tau₁) (htau₂ : 0 ≤ tau₂)
    (hupper : min (tau₁ + mediumThresholdShift eps kappa) tau₂ ≤
      17 / 70 - thresholdLoss * eps) :
    2 * mediumProductLoss kappa * min tau₁ tau₂ +
        mediumResidualSaving kappa ≤
      kappa - 2 * mediumThresholdShift eps kappa := by
  apply medium_explicit_reserve_gap hkappa htau₁ htau₂
  exact min_unshifted_le_one_of_shifted_hybrid_threshold
    hthresholdLoss heps
    (le_min heps (by positivity)) hupper

/-- If rounding a logarithmic bin costs at most `eps`, the additional
powered-slice shift still fits an absolute threshold margin of `2*eps`.
Thus the outer constant can be chosen as `thresholdLoss + 2`, independently
of the coefficient parameters and of `kappa`. -/
theorem medium_shifted_threshold_with_absolute_margin
    {thresholdLoss eps kappa tau₁ tau₂ : ℝ}
    (heps : 0 ≤ eps)
    (hkappa : 0 ≤ kappa)
    (hrounded : min tau₁ tau₂ ≤
      17 / 70 - (thresholdLoss + 2) * eps + eps) :
    min (tau₁ + mediumThresholdShift eps kappa) tau₂ ≤
      17 / 70 - thresholdLoss * eps := by
  have hshiftNonneg : 0 ≤ mediumThresholdShift eps kappa :=
    le_min heps (by positivity)
  have hminShift := min_add_left_le_min_add
    (x := tau₁) (y := tau₂) hshiftNonneg
  have hshiftLe := mediumThresholdShift_le_eps eps kappa
  linarith

/-- The absolute threshold constant selected by the preceding lemma. -/
def outerThresholdLoss (thresholdLoss : ℝ) : ℝ :=
  thresholdLoss + 2

theorem outerThresholdLoss_pos {thresholdLoss : ℝ}
    (hthresholdLoss : 0 < thresholdLoss) :
    0 < outerThresholdLoss thresholdLoss := by
  dsimp [outerThresholdLoss]
  linarith

/-- Metadata for the explicit reserve allocation. -/
def outerParameterReserveModule : ProofModule :=
  { name := "TypeII.OuterParameterReserve"
    paperLocation :=
      "Proof of Proposition 5.1, outer epsilon and saving allocation"
    purpose :=
      "Choose explicit threshold-shift, product-loss, and residual-saving parameters and verify both the hybrid-threshold budget and the final negative-power gap."
    dependsOn := ["TypeII.MediumFullAssembly"]
    status := .proved }

end

end TypeII
end ExactSemiprimes
