import ExactSemiprimes.TypeII.PoweredPolynomial
import ExactSemiprimes.TypeII.MediumThresholdBridge
import ExactSemiprimes.TypeII.LargeValuePartition
import ExactSemiprimes.Hybrid.HybridDensity

/-! # Cardinality of the medium Type-II bins -/

namespace ExactSemiprimes
namespace TypeII

noncomputable section

/-!
## Combining the two orderings

The analytic work which supplies either branch is deliberately not repeated
here.  The lemmas below only perform the exact order split and rewrite the
answer using `min τ₁ τ₂`.
-/

/-- In the branch `τ₁ ≤ τ₂`, a bound with exponent `2τ₁-κ` is exactly the
common minimum-exponent bound. -/
theorem mediumCardinality_min_of_first_le_second
    {R : Finset ℝ} {T C τ₁ τ₂ κ : ℝ}
    (horder : τ₁ ≤ τ₂)
    (hbound : (R.card : ℝ) ≤ C * T ^ (2 * τ₁ - κ)) :
    (R.card : ℝ) ≤ C * T ^ (2 * min τ₁ τ₂ - κ) := by
  simpa [min_eq_left horder] using hbound

/-- In the branch `τ₂ < τ₁`, a bound with exponent `2τ₂-κ` is exactly the
common minimum-exponent bound. -/
theorem mediumCardinality_min_of_second_lt_first
    {R : Finset ℝ} {T C τ₁ τ₂ κ : ℝ}
    (horder : τ₂ < τ₁)
    (hbound : (R.card : ℝ) ≤ C * T ^ (2 * τ₂ - κ)) :
    (R.card : ℝ) ≤ C * T ^ (2 * min τ₁ τ₂ - κ) := by
  simpa [min_eq_right horder.le] using hbound

/-- A branchwise pair of cardinality estimates yields the common form used
in equation (5.3).  No hybrid-density estimate is assumed by this theorem;
the two implications are its explicit inputs. -/
theorem mediumCardinality_min_of_ordered_bounds
    {R : Finset ℝ} {T C τ₁ τ₂ κ : ℝ}
    (hfirst : τ₁ ≤ τ₂ →
      (R.card : ℝ) ≤ C * T ^ (2 * τ₁ - κ))
    (hsecond : τ₂ < τ₁ →
      (R.card : ℝ) ≤ C * T ^ (2 * τ₂ - κ)) :
    (R.card : ℝ) ≤ C * T ^ (2 * min τ₁ τ₂ - κ) := by
  by_cases horder : τ₁ ≤ τ₂
  · exact mediumCardinality_min_of_first_le_second horder (hfirst horder)
  · have hreverse : τ₂ < τ₁ := lt_of_not_ge horder
    exact mediumCardinality_min_of_second_lt_first hreverse
      (hsecond hreverse)

/-!
## Applying the hybrid density theorem in the two order branches

The following statements keep the quantifier order of the proved hybrid
density theorem.  In the `τ₂ < τ₁` branch it applies directly to the second
Type-II polynomial.  In the `τ₁ ≤ τ₂` branch it applies to one already
selected dyadic slice of the `ℓ`-fold convolution of the first polynomial.
The finite pigeonhole step which selects such a slice at every height is
deliberately not hidden in either statement.
-/

/-- The direct, unpowered `M₂` branch of the medium-bin argument. -/
def MediumUnpoweredSecondBranchStatement : Prop :=
  ∃ thresholdLoss : ℝ, 0 < thresholdLoss ∧
    ∀ B : ℝ, 0 ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 1000 →
        ∃ κ : ℝ, 0 < κ ∧
          ∀ A : ℝ, 1 ≤ A →
            ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
              ∀ (T : ℝ) (N₂ : ℕ) (τ₁ τ₂ : ℝ) (a₂ : ℕ → ℂ)
                  (R : Finset ℝ),
                T₀ ≤ T → 1 ≤ N₂ →
                T ^ (9 / 11 - 10 * ε) ≤ (N₂ : ℝ) →
                (N₂ : ℝ) ≤ T ^ (1 - ε / 10) →
                10 * ε ≤ τ₂ →
                τ₂ ≤ 17 / 70 - thresholdLoss * ε →
                τ₂ < τ₁ →
                IsDivisorBoundedByConstant B A a₂ →
                IsOneSpaced (↑R : Set ℝ) →
                (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
                (∀ t ∈ R,
                  (N₂ : ℝ) ^ (-τ₂) <
                    ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ)
                      (onePlusIT t)‖) →
                (R.card : ℝ) ≤
                  C * T ^ (2 * min τ₁ τ₂ - κ)

/-- The unpowered second branch is a literal specialization of the discrete
hybrid density theorem, followed only by `min τ₁ τ₂ = τ₂`. -/
theorem mediumUnpoweredSecondBranch_of_hybridDiscreteDensity
    (hHybrid : Hybrid.HybridDiscreteDensityStatement) :
    MediumUnpoweredSecondBranchStatement := by
  obtain ⟨thresholdLoss, hthresholdLoss, hHybrid⟩ := hHybrid
  refine ⟨thresholdLoss, hthresholdLoss, ?_⟩
  intro B hB ε hε hεsmall
  obtain ⟨κ, hκ, hHybrid⟩ := hHybrid B hB ε hε hεsmall
  refine ⟨κ, hκ, ?_⟩
  intro A hA
  obtain ⟨C, T₀, hC, hT₀, hHybrid⟩ := hHybrid A hA
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T N₂ τ₁ τ₂ a₂ R hT hN₂ hN₂lower hN₂upper
    hτ₂lower hτ₂upper horder ha₂ hspaced hR hlarge
  exact mediumCardinality_min_of_second_lt_first horder
    (hHybrid T N₂ τ₂ a₂ R hT hN₂ hN₂lower hN₂upper
      hτ₂lower hτ₂upper ha₂ hspaced hR hlarge)

/-- The literature inputs therefore close the direct `M₂` order branch; no
additional analytic premise is introduced locally. -/
theorem mediumUnpoweredSecondBranch_of_guthMaynard
    (inputs : ExactSemiprimes.ExternalInputs) :
    MediumUnpoweredSecondBranchStatement := by
  exact mediumUnpoweredSecondBranch_of_hybridDiscreteDensity
    (Hybrid.hybridDensity_of_guthMaynard inputs.guthMaynardMainLargeValues
      inputs.guthMaynardLongPolynomial).1

/-- The prepared powered `M₁` branch.  Here `P` is the natural base of one
dyadic product slice and the displayed polynomial is exactly that slice of
the collected `ℓ`-fold convolution coefficient. -/
def MediumPreparedPoweredFirstBranchStatement : Prop :=
  ∃ thresholdLoss : ℝ, 0 < thresholdLoss ∧
    ∀ ℓ : ℕ, 1 ≤ ℓ →
      ∀ B : ℝ, 0 ≤ B →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 1000 →
          ∃ κ : ℝ, 0 < κ ∧
            ∀ A : ℝ, 1 ≤ A →
              ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
                ∀ (T : ℝ) (M P : ℕ) (τ₁ τ₂ : ℝ) (a₁ : ℕ → ℂ)
                    (R : Finset ℝ),
                  T₀ ≤ T → 1 ≤ M → 1 ≤ P →
                  T ^ (9 / 11 - 10 * ε) ≤ (P : ℝ) →
                  (P : ℝ) ≤ T ^ (1 - ε / 10) →
                  10 * ε ≤ τ₁ →
                  τ₁ ≤ 17 / 70 - thresholdLoss * ε →
                  τ₁ ≤ τ₂ →
                  IsDivisorBoundedByConstant B A a₁ →
                  IsOneSpaced (↑R : Set ℝ) →
                  (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
                  (∀ t ∈ R,
                    (P : ℝ) ^ (-τ₁) <
                      ‖dyadicDirichletPolynomial
                        (powerConvolutionCoefficient a₁
                          (dyadicInterval (M : ℝ)) ℓ)
                        (P : ℝ) (onePlusIT t)‖) →
                  (R.card : ℝ) ≤
                    C * T ^ (2 * min τ₁ τ₂ - κ)

/-- Once a powered dyadic slice has been selected, its coefficient sequence
has the repaired divisor exponent `Bℓ+ℓ-1`; the hybrid density theorem then
gives the desired first-branch cardinality estimate. -/
theorem mediumPreparedPoweredFirstBranch_of_hybridDiscreteDensity
    (hHybrid : Hybrid.HybridDiscreteDensityStatement) :
    MediumPreparedPoweredFirstBranchStatement := by
  obtain ⟨thresholdLoss, hthresholdLoss, hHybrid⟩ := hHybrid
  refine ⟨thresholdLoss, hthresholdLoss, ?_⟩
  intro ℓ hℓ B hB ε hε hεsmall
  let Bpowered : ℝ := B * (ℓ : ℝ) + (ℓ : ℝ) - 1
  have hBpowered : 0 ≤ Bpowered := by
    dsimp [Bpowered]
    have hℓreal : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
    nlinarith
  obtain ⟨κ, hκ, hHybrid⟩ :=
    hHybrid Bpowered hBpowered ε hε hεsmall
  refine ⟨κ, hκ, ?_⟩
  intro A hA
  have hApowered : 1 ≤ A ^ ℓ := one_le_pow₀ hA
  obtain ⟨C, T₀, hC, hT₀, hHybrid⟩ := hHybrid (A ^ ℓ) hApowered
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T M P τ₁ τ₂ a₁ R hT hM hP hPlower hPupper
    hτ₁lower hτ₁upper horder ha₁ hspaced hR hlarge
  have haPowered :
      IsDivisorBoundedByConstant Bpowered (A ^ ℓ)
        (powerConvolutionCoefficient a₁
          (dyadicInterval (M : ℝ)) ℓ) := by
    simpa [Bpowered] using
      (powerConvolutionCoefficient_isDivisorBoundedByConstant
        (S := dyadicInterval (M : ℝ)) hℓ ha₁)
  have hcard := hHybrid T P τ₁
    (powerConvolutionCoefficient a₁ (dyadicInterval (M : ℝ)) ℓ) R
    hT hP hPlower hPupper hτ₁lower hτ₁upper haPowered
    hspaced hR hlarge
  exact mediumCardinality_min_of_first_le_second horder hcard

/-- The Guth--Maynard inputs close the prepared powered branch as well. -/
theorem mediumPreparedPoweredFirstBranch_of_guthMaynard
    (inputs : ExactSemiprimes.ExternalInputs) :
    MediumPreparedPoweredFirstBranchStatement := by
  exact mediumPreparedPoweredFirstBranch_of_hybridDiscreteDensity
    (Hybrid.hybridDensity_of_guthMaynard inputs.guthMaynardMainLargeValues
      inputs.guthMaynardLongPolynomial).1

/-!
## The negative-power calculation

Write `Mᵢ = T^ηᵢ`.  The lower product estimate
`T^(1-ξ) ≤ M₁M₂` says `1-ξ ≤ η₁+η₂`.  Since a nonnegative weighted average
of `τ₁,τ₂` is at least `(η₁+η₂) min(τ₁,τ₂)`, multiplication by the modeled
bin sizes cancels the exponent `2 min(τ₁,τ₂)`.  The explicit gap hypothesis

`2 ξ min(τ₁,τ₂) + δ ≤ κ`

then leaves the power `T^{-δ}`.  This isolates exactly how much of `κ` is
spent absorbing the product-length error.
-/

/-- Exact conversion of the product lower bound to a lower bound for the
sum of modeled length exponents. -/
theorem lengthExponent_sum_lower_of_modeled_product
    {T M₁ M₂ η₁ η₂ ξ : ℝ}
    (hT : 1 < T)
    (hM₁ : M₁ = T ^ η₁) (hM₂ : M₂ = T ^ η₂)
    (hproduct : T ^ (1 - ξ) ≤ M₁ * M₂) :
    1 - ξ ≤ η₁ + η₂ := by
  rw [hM₁, hM₂, ← Real.rpow_add (by positivity)] at hproduct
  exact (Real.rpow_le_rpow_left_iff hT).mp hproduct

/-- Conversely, the exponent-sum lower bound implies the modeled product
lower bound. -/
theorem modeled_product_lower_of_lengthExponent_sum
    {T M₁ M₂ η₁ η₂ ξ : ℝ}
    (hT : 1 ≤ T)
    (hM₁ : M₁ = T ^ η₁) (hM₂ : M₂ = T ^ η₂)
    (hsum : 1 - ξ ≤ η₁ + η₂) :
    T ^ (1 - ξ) ≤ M₁ * M₂ := by
  rw [hM₁, hM₂, ← Real.rpow_add (by positivity)]
  exact Real.rpow_le_rpow_of_exponent_le hT hsum

/-- Algebraic identity for the modeled contribution of one medium bin. -/
theorem modeledMediumFactor_eq_rpow
    {T M₁ M₂ η₁ η₂ τ₁ τ₂ κ : ℝ}
    (hT : 0 < T)
    (hM₁ : M₁ = T ^ η₁) (hM₂ : M₂ = T ^ η₂) :
    T ^ (2 * min τ₁ τ₂ - κ) *
        M₁ ^ (-2 * τ₁) * M₂ ^ (-2 * τ₂) =
      T ^ (2 * min τ₁ τ₂ - κ -
        2 * η₁ * τ₁ - 2 * η₂ * τ₂) := by
  rw [hM₁, hM₂, ← Real.rpow_mul hT.le, ← Real.rpow_mul hT.le,
    ← Real.rpow_add hT, ← Real.rpow_add hT]
  congr 1
  ring

/-- The exponent inequality behind the negative-power saving.  The proof
checks both orderings of `τ₁,τ₂` separately. -/
theorem mediumWeightedExponent_le_neg
    {η₁ η₂ τ₁ τ₂ κ ξ δ : ℝ}
    (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (hproduct : 1 - ξ ≤ η₁ + η₂)
    (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 ≤ τ₂)
    (hgap : 2 * ξ * min τ₁ τ₂ + δ ≤ κ) :
    2 * min τ₁ τ₂ - κ - 2 * η₁ * τ₁ - 2 * η₂ * τ₂ ≤ -δ := by
  by_cases horder : τ₁ ≤ τ₂
  · rw [min_eq_left horder] at hgap ⊢
    have hproductWeighted :
        0 ≤ (η₁ + η₂ - (1 - ξ)) * τ₁ :=
      mul_nonneg (sub_nonneg.mpr hproduct) hτ₁
    have horderingWeighted : 0 ≤ η₂ * (τ₂ - τ₁) :=
      mul_nonneg hη₂ (sub_nonneg.mpr horder)
    nlinarith
  · have hreverse : τ₂ ≤ τ₁ := le_of_not_ge horder
    rw [min_eq_right hreverse] at hgap ⊢
    have hproductWeighted :
        0 ≤ (η₁ + η₂ - (1 - ξ)) * τ₂ :=
      mul_nonneg (sub_nonneg.mpr hproduct) hτ₂
    have horderingWeighted : 0 ≤ η₁ * (τ₁ - τ₂) :=
      mul_nonneg hη₁ (sub_nonneg.mpr hreverse)
    nlinarith

/-- Multiplication by the two modeled bin sizes leaves a negative power of
`T`.  Every length and gap condition used by the cancellation is explicit. -/
theorem modeledMediumFactor_le_negativePower
    {T M₁ M₂ η₁ η₂ τ₁ τ₂ κ ξ δ : ℝ}
    (hT : 1 < T)
    (hM₁ : M₁ = T ^ η₁) (hM₂ : M₂ = T ^ η₂)
    (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (hproduct : T ^ (1 - ξ) ≤ M₁ * M₂)
    (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 ≤ τ₂)
    (hgap : 2 * ξ * min τ₁ τ₂ + δ ≤ κ) :
    T ^ (2 * min τ₁ τ₂ - κ) *
        M₁ ^ (-2 * τ₁) * M₂ ^ (-2 * τ₂) ≤
      T ^ (-δ) := by
  have hsum : 1 - ξ ≤ η₁ + η₂ :=
    lengthExponent_sum_lower_of_modeled_product hT hM₁ hM₂ hproduct
  rw [modeledMediumFactor_eq_rpow (by positivity) hM₁ hM₂]
  exact Real.rpow_le_rpow_of_exponent_le hT.le
    (mediumWeightedExponent_le_neg hη₁ hη₂ hsum hτ₁ hτ₂ hgap)

/-- A frequently used form of the gap: if `min(τ₁,τ₂) ≤ σmax`, it is
enough to reserve `2ξσmax+δ` of the cardinality saving. -/
theorem modeledMediumFactor_le_negativePower_of_thresholdGap
    {T M₁ M₂ η₁ η₂ τ₁ τ₂ κ ξ δ σmax : ℝ}
    (hT : 1 < T)
    (hM₁ : M₁ = T ^ η₁) (hM₂ : M₂ = T ^ η₂)
    (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (hproduct : T ^ (1 - ξ) ≤ M₁ * M₂)
    (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 ≤ τ₂)
    (hξ : 0 ≤ ξ) (hthreshold : min τ₁ τ₂ ≤ σmax)
    (hgap : 2 * ξ * σmax + δ ≤ κ) :
    T ^ (2 * min τ₁ τ₂ - κ) *
        M₁ ^ (-2 * τ₁) * M₂ ^ (-2 * τ₂) ≤
      T ^ (-δ) := by
  have hscaled : 2 * ξ * min τ₁ τ₂ ≤ 2 * ξ * σmax := by
    exact mul_le_mul_of_nonneg_left hthreshold (by positivity)
  apply modeledMediumFactor_le_negativePower hT hM₁ hM₂ hη₁ hη₂
    hproduct hτ₁ hτ₂
  linarith

/-- Final cardinality-weighted form.  Given the common discrete bound, the
modeled contribution of a medium bin is at most `C T^{-δ}`. -/
theorem weightedMediumCardinality_le_negativePower
    {R : Finset ℝ}
    {T M₁ M₂ η₁ η₂ τ₁ τ₂ κ ξ δ C : ℝ}
    (hT : 1 < T)
    (hM₁ : M₁ = T ^ η₁) (hM₂ : M₂ = T ^ η₂)
    (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (hproduct : T ^ (1 - ξ) ≤ M₁ * M₂)
    (hτ₁ : 0 ≤ τ₁) (hτ₂ : 0 ≤ τ₂)
    (hgap : 2 * ξ * min τ₁ τ₂ + δ ≤ κ)
    (hC : 0 ≤ C)
    (hcard : (R.card : ℝ) ≤ C * T ^ (2 * min τ₁ τ₂ - κ)) :
    (R.card : ℝ) * M₁ ^ (-2 * τ₁) * M₂ ^ (-2 * τ₂) ≤
      C * T ^ (-δ) := by
  have hM₁nonneg : 0 ≤ M₁ := by
    rw [hM₁]
    exact Real.rpow_nonneg (by linarith) _
  have hM₂nonneg : 0 ≤ M₂ := by
    rw [hM₂]
    exact Real.rpow_nonneg (by linarith) _
  have hweight : 0 ≤ M₁ ^ (-2 * τ₁) * M₂ ^ (-2 * τ₂) :=
    mul_nonneg (Real.rpow_nonneg hM₁nonneg _)
      (Real.rpow_nonneg hM₂nonneg _)
  have hfactor := modeledMediumFactor_le_negativePower hT hM₁ hM₂
    hη₁ hη₂ hproduct hτ₁ hτ₂ hgap
  calc
    (R.card : ℝ) * M₁ ^ (-2 * τ₁) * M₂ ^ (-2 * τ₂) =
        (R.card : ℝ) *
          (M₁ ^ (-2 * τ₁) * M₂ ^ (-2 * τ₂)) := by ring
    _ ≤ (C * T ^ (2 * min τ₁ τ₂ - κ)) *
          (M₁ ^ (-2 * τ₁) * M₂ ^ (-2 * τ₂)) :=
      mul_le_mul_of_nonneg_right hcard hweight
    _ = C * (T ^ (2 * min τ₁ τ₂ - κ) *
          M₁ ^ (-2 * τ₁) * M₂ ^ (-2 * τ₂)) := by ring
    _ ≤ C * T ^ (-δ) := mul_le_mul_of_nonneg_left hfactor hC

def mediumRangeCardinalityModule : ProofModule :=
  { name := "TypeII.MediumRangeCardinality"
    paperLocation := "Proof of Proposition 5.1, cardinality of the R₂ bins"
    purpose :=
      "Apply the proved hybrid density theorem to the direct M₂ branch and to a prepared powered-M₁ dyadic slice, combine the order branches, and prove the negative-power cancellation. Endpoint-compatible slicing, pointwise selection, uniform eventual absorption of the 1/ell threshold loss, natural slice scales, and finite-cover aggregation are proved here; the common hybrid constants are supplied by MediumFiniteUniformization and assembled in MediumFullAssembly."
    dependsOn :=
      ["TypeII.MediumThresholdBridge", "TypeII.LargeValuePartition",
        "Hybrid.HybridDensity"]
    status := .proved }

end

end TypeII
end ExactSemiprimes
