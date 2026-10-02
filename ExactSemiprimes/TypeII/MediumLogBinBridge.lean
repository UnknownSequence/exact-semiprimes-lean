import ExactSemiprimes.TypeII.MediumFullAssembly

/-!
# Unit logarithmic bins and the weighted medium estimate

This module makes precise the fixed-factor comparison hidden by the paper's
notation that a Dirichlet-polynomial magnitude is comparable to a length
raised to a bin exponent. It uses the upper edge of each unit log bin,
proves the strict large-value hypotheses needed by MediumFullAssembly, and
shows that the actual squared-product sum costs only the absolute factor
`exp 4` beyond the cardinality weight.
-/

namespace ExactSemiprimes
namespace TypeII

noncomputable section

open scoped BigOperators

/-- The upper edge of the normalized unit logarithmic bin. -/
def upperBinExponent (N : ℝ) (k : ℤ) : ℝ :=
  ((k : ℝ) + 1) / Real.log N

theorem rpow_neg_upperBinExponent {N : ℝ} (hN : 1 < N) (k : ℤ) :
    N ^ (-upperBinExponent N k) = Real.exp (-((k : ℝ) + 1)) := by
  rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hN)]
  congr 1
  rw [upperBinExponent]
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  field_simp

theorem magnitude_bounds_of_mem_logMagnitudeBin_upperExponent
    {N : ℝ} {M : ℂ → ℂ} {k : ℤ} {t : ℝ}
    (hN : 1 < N) (ht : t ∈ logMagnitudeBin M k)
    (hpos : 0 < typeIIMagnitude M t) :
    N ^ (-upperBinExponent N k) < typeIIMagnitude M t ∧
      typeIIMagnitude M t ≤
        Real.exp 1 * N ^ (-upperBinExponent N k) := by
  have hb := magnitude_bounds_of_mem_logMagnitudeBin ht hpos
  rw [rpow_neg_upperBinExponent hN k]
  refine ⟨hb.1, hb.2.trans_eq ?_⟩
  rw [← Real.exp_add]
  congr 1
  ring

theorem sq_rpow_neg_eq_rpow_neg_two_mul
    {N tau : ℝ} (hN : 0 ≤ N) :
    (N ^ (-tau)) ^ (2 : ℕ) = N ^ (-2 * tau) := by
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hN]
  congr 1
  ring

theorem exp_one_pow_four : (Real.exp 1) ^ (4 : ℕ) = Real.exp 4 := by
  rw [← Real.exp_nat_mul]
  norm_num

/-- A simultaneous unit logarithmic bin contributes at most the expected
cardinality weight, up to the explicit fixed factor `exp 4`. -/
theorem sum_typeIIWeight_logMagnitudePairBin_le_expFour_cardWeight
    {N₁ N₂ : ℝ} (hN₁ : 1 < N₁) (hN₂ : 1 < N₂)
    {M₁ M₂ : ℂ → ℂ} {k₁ k₂ : ℤ} (R : Finset ℝ)
    (hbin : ∀ t ∈ R, t ∈ logMagnitudePairBin M₁ M₂ k₁ k₂)
    (hpos₁ : ∀ t ∈ R, 0 < typeIIMagnitude M₁ t)
    (hpos₂ : ∀ t ∈ R, 0 < typeIIMagnitude M₂ t) :
    (∑ t ∈ R,
      (typeIIMagnitude M₁ t) ^ 2 * (typeIIMagnitude M₂ t) ^ 2) ≤
      Real.exp 4 *
        ((R.card : ℝ) * N₁ ^ (-2 * upperBinExponent N₁ k₁) *
          N₂ ^ (-2 * upperBinExponent N₂ k₂)) := by
  have hpoint : ∀ t ∈ R,
      (typeIIMagnitude M₁ t) ^ 2 * (typeIIMagnitude M₂ t) ^ 2 ≤
        Real.exp 4 * N₁ ^ (-2 * upperBinExponent N₁ k₁) *
          N₂ ^ (-2 * upperBinExponent N₂ k₂) := by
    intro t ht
    have hb₁ :=
      (magnitude_bounds_of_mem_logMagnitudeBin_upperExponent hN₁
        (hbin t ht).1 (hpos₁ t ht)).2
    have hb₂ :=
      (magnitude_bounds_of_mem_logMagnitudeBin_upperExponent hN₂
        (hbin t ht).2 (hpos₂ t ht)).2
    have hs₁ :
        (typeIIMagnitude M₁ t) ^ 2 ≤
          (Real.exp 1 * N₁ ^ (-upperBinExponent N₁ k₁)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos 1).le
        (Real.rpow_nonneg (by linarith) _))).2 hb₁
    have hs₂ :
        (typeIIMagnitude M₂ t) ^ 2 ≤
          (Real.exp 1 * N₂ ^ (-upperBinExponent N₂ k₂)) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos 1).le
        (Real.rpow_nonneg (by linarith) _))).2 hb₂
    calc
      (typeIIMagnitude M₁ t) ^ 2 * (typeIIMagnitude M₂ t) ^ 2 ≤
          (Real.exp 1 * N₁ ^ (-upperBinExponent N₁ k₁)) ^ 2 *
            (Real.exp 1 * N₂ ^ (-upperBinExponent N₂ k₂)) ^ 2 :=
        mul_le_mul hs₁ hs₂ (sq_nonneg _) (sq_nonneg _)
      _ = Real.exp 4 * N₁ ^ (-2 * upperBinExponent N₁ k₁) *
          N₂ ^ (-2 * upperBinExponent N₂ k₂) := by
        rw [mul_pow, mul_pow,
          sq_rpow_neg_eq_rpow_neg_two_mul (zero_le_one.trans hN₁.le),
          sq_rpow_neg_eq_rpow_neg_two_mul (zero_le_one.trans hN₂.le),
          ← exp_one_pow_four]
        ring
  calc
    (∑ t ∈ R,
        (typeIIMagnitude M₁ t) ^ 2 * (typeIIMagnitude M₂ t) ^ 2) ≤
        ∑ _t ∈ R,
          (Real.exp 4 * N₁ ^ (-2 * upperBinExponent N₁ k₁) *
            N₂ ^ (-2 * upperBinExponent N₂ k₂)) := by
      exact Finset.sum_le_sum hpoint
    _ = Real.exp 4 *
        ((R.card : ℝ) * N₁ ^ (-2 * upperBinExponent N₁ k₁) *
          N₂ ^ (-2 * upperBinExponent N₂ k₂)) := by
      simp
      ring

/-- If the value in a unit logarithmic bin is at least `N⁻ˢᶦᵍᵐᵃ`, then the
upper edge of that bin is at most `sigma + 1 / log N`. -/
theorem upperBinExponent_le_of_rpow_le_magnitude
    {N sigma : ℝ} {M : ℂ → ℂ} {k : ℤ} {t : ℝ}
    (hN : 1 < N) (ht : t ∈ logMagnitudeBin M k)
    (hpos : 0 < typeIIMagnitude M t)
    (hlarge : N ^ (-sigma) ≤ typeIIMagnitude M t) :
    upperBinExponent N k ≤ sigma + 1 / Real.log N := by
  have hupper := (magnitude_bounds_of_mem_logMagnitudeBin ht hpos).2
  have hNpos : 0 < N := zero_lt_one.trans hN
  have hexp : Real.exp (Real.log N * (-sigma)) ≤
      Real.exp (-(k : ℝ)) := by
    rw [← Real.rpow_def_of_pos hNpos]
    exact hlarge.trans hupper
  have hargs := Real.exp_le_exp.mp hexp
  have hlog : 0 < Real.log N := Real.log_pos hN
  have hk : (k : ℝ) / Real.log N ≤ sigma := by
    rw [div_le_iff₀ hlog]
    linarith
  rw [upperBinExponent, add_div]
  linarith

theorem lt_upperBinExponent_of_magnitude_lt_rpow
    {N alpha : ℝ} {M : ℂ → ℂ} {k : ℤ} {t : ℝ}
    (hN : 1 < N) (ht : t ∈ logMagnitudeBin M k)
    (hpos : 0 < typeIIMagnitude M t)
    (hsmall : typeIIMagnitude M t < N ^ (-alpha)) :
    alpha < upperBinExponent N k := by
  have hlower :=
    (magnitude_bounds_of_mem_logMagnitudeBin_upperExponent hN ht hpos).1
  have hpowers : N ^ (-upperBinExponent N k) < N ^ (-alpha) :=
    hlower.trans hsmall
  have hexponents :=
    (Real.strictMono_rpow_of_base_gt_one hN).lt_iff_lt.mp hpowers
  linarith

theorem typeIIMagnitudes_pos_of_mem_largeValueR2
    {R : Set ℝ} {M₁ M₂ : ℂ → ℂ} {N₁ N₂ T eps t : ℝ}
    (hT : 0 < T) (ht : t ∈ largeValueR2 R M₁ M₂ N₁ N₂ T eps) :
    0 < typeIIMagnitude M₁ t ∧ 0 < typeIIMagnitude M₂ t := by
  have ht' := mem_largeValueR2_iff.mp ht
  have hinv : 0 < T⁻¹ := inv_pos.mpr hT
  exact ⟨hinv.trans_le ht'.2.2.2.1, hinv.trans_le ht'.2.2.2.2⟩

/-- An occupied `R₂` bin automatically lies strictly beyond the lower
`10 eps` threshold in both normalized coordinates. -/
theorem upperBinExponents_medium_lower_bounds_of_nonempty_R2_bin
    {S : Set ℝ} {N₁ N₂ T eps shift : ℝ} {M₁ M₂ : ℂ → ℂ}
    {k₁ k₂ : ℤ} {R : Finset ℝ}
    (hN₁ : 1 < N₁) (hN₂ : 1 < N₂) (hT : 0 < T)
    (heps : 0 ≤ eps) (hshift : 0 ≤ shift) (hRne : R.Nonempty)
    (hR2 : ∀ t ∈ R, t ∈ largeValueR2 S M₁ M₂ N₁ N₂ T eps)
    (hbin : ∀ t ∈ R, t ∈ logMagnitudePairBin M₁ M₂ k₁ k₂) :
    0 ≤ upperBinExponent N₁ k₁ ∧
      0 ≤ upperBinExponent N₂ k₂ ∧
      10 * eps ≤ upperBinExponent N₁ k₁ + shift ∧
      10 * eps ≤ upperBinExponent N₂ k₂ := by
  obtain ⟨t, ht⟩ := hRne
  have htR2 := mem_largeValueR2_iff.mp (hR2 t ht)
  have hpos := typeIIMagnitudes_pos_of_mem_largeValueR2 hT (hR2 t ht)
  have htau₁ : 10 * eps < upperBinExponent N₁ k₁ :=
    lt_upperBinExponent_of_magnitude_lt_rpow hN₁ (hbin t ht).1 hpos.1
      (by simpa only [neg_mul] using htR2.2.1)
  have htau₂ : 10 * eps < upperBinExponent N₂ k₂ :=
    lt_upperBinExponent_of_magnitude_lt_rpow hN₂ (hbin t ht).2 hpos.2
      (by simpa only [neg_mul] using htR2.2.2.1)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- The outer pointwise large-value alternative transfers to the upper
edges of the two unit bins.  The only loss is their explicit widths, plus
the powered-branch shift on the first coordinate. -/
theorem min_upperBinExponent_add_shift_le_of_largeValue_disjunction
    {N₁ N₂ sigma shift loss : ℝ} {M₁ M₂ : ℂ → ℂ}
    {k₁ k₂ : ℤ} {t : ℝ}
    (hN₁ : 1 < N₁) (hN₂ : 1 < N₂)
    (hbin : t ∈ logMagnitudePairBin M₁ M₂ k₁ k₂)
    (hpos₁ : 0 < typeIIMagnitude M₁ t)
    (hpos₂ : 0 < typeIIMagnitude M₂ t)
    (hlarge : N₁ ^ (-sigma) ≤ typeIIMagnitude M₁ t ∨
      N₂ ^ (-sigma) ≤ typeIIMagnitude M₂ t)
    (hwidth₁ : 1 / Real.log N₁ + shift ≤ loss)
    (hwidth₂ : 1 / Real.log N₂ ≤ loss) :
    min (upperBinExponent N₁ k₁ + shift)
        (upperBinExponent N₂ k₂) ≤ sigma + loss := by
  rcases hlarge with hlarge₁ | hlarge₂
  · have htau₁ := upperBinExponent_le_of_rpow_le_magnitude
      hN₁ hbin.1 hpos₁ hlarge₁
    exact (min_le_left _ _).trans (by linarith)
  · have htau₂ := upperBinExponent_le_of_rpow_le_magnitude
      hN₂ hbin.2 hpos₂ hlarge₂
    exact (min_le_right _ _).trans (by linarith)

/-- Specialization to the absolute outer threshold constant selected in
`OuterParameterReserve`: two epsilon-units cover the bin width and the
powered-slice shift. -/
theorem min_upperBinExponent_shifted_outer_threshold
    {N₁ N₂ thresholdLoss eps shift : ℝ}
    {M₁ M₂ : ℂ → ℂ} {k₁ k₂ : ℤ} {t : ℝ}
    (hN₁ : 1 < N₁) (hN₂ : 1 < N₂)
    (hbin : t ∈ logMagnitudePairBin M₁ M₂ k₁ k₂)
    (hpos₁ : 0 < typeIIMagnitude M₁ t)
    (hpos₂ : 0 < typeIIMagnitude M₂ t)
    (hlarge :
      N₁ ^ (-(17 / 70 - (thresholdLoss + 2) * eps)) ≤
          typeIIMagnitude M₁ t ∨
        N₂ ^ (-(17 / 70 - (thresholdLoss + 2) * eps)) ≤
          typeIIMagnitude M₂ t)
    (hwidth₁ : 1 / Real.log N₁ + shift ≤ 2 * eps)
    (hwidth₂ : 1 / Real.log N₂ ≤ 2 * eps) :
    min (upperBinExponent N₁ k₁ + shift)
        (upperBinExponent N₂ k₂) ≤
      17 / 70 - thresholdLoss * eps := by
  have h := min_upperBinExponent_add_shift_le_of_largeValue_disjunction
    hN₁ hN₂ hbin hpos₁ hpos₂ hlarge hwidth₁ hwidth₂
  linarith

/-- Any independent bound for the cardinality weight immediately controls
the actual squared product sum on the bin, with only the fixed `exp 4`
loss.  This is the direct interface to `MediumFullAssembly`. -/
theorem sum_typeIIWeight_logMagnitudePairBin_le_of_cardWeight
    {N₁ N₂ W : ℝ} (hN₁ : 1 < N₁) (hN₂ : 1 < N₂)
    {M₁ M₂ : ℂ → ℂ} {k₁ k₂ : ℤ} (R : Finset ℝ)
    (hbin : ∀ t ∈ R, t ∈ logMagnitudePairBin M₁ M₂ k₁ k₂)
    (hpos₁ : ∀ t ∈ R, 0 < typeIIMagnitude M₁ t)
    (hpos₂ : ∀ t ∈ R, 0 < typeIIMagnitude M₂ t)
    (hcardWeight :
      (R.card : ℝ) * N₁ ^ (-2 * upperBinExponent N₁ k₁) *
        N₂ ^ (-2 * upperBinExponent N₂ k₂) ≤ W) :
    (∑ t ∈ R,
      (typeIIMagnitude M₁ t) ^ 2 * (typeIIMagnitude M₂ t) ^ 2) ≤
      Real.exp 4 * W := by
  exact (sum_typeIIWeight_logMagnitudePairBin_le_expFour_cardWeight
    hN₁ hN₂ R hbin hpos₁ hpos₂).trans
      (mul_le_mul_of_nonneg_left hcardWeight (Real.exp_pos 4).le)

/-- Metadata for the exact log-bin edge and weight insertion. -/
def mediumLogBinBridgeModule : ProofModule :=
  { name := "TypeII.MediumLogBinBridge"
    paperLocation :=
      "Proof of Proposition 5.1, insertion of the unit logarithmic R₂ bins"
    purpose :=
      "Convert literal unit log-bin membership into the strict normalized large-value thresholds, transfer the outer large-value disjunction with explicit bin-width loss, and bound the actual squared-product sum by exp(4) times the completed cardinality weight."
    dependsOn := ["TypeII.MediumFullAssembly", "TypeII.LargeValuePartition"]
    status := .proved }

end

end TypeII
end ExactSemiprimes
