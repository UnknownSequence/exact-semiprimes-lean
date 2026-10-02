import ExactSemiprimes.Completion.TypeIComponentClosure
import ExactSemiprimes.Completion.TypeIOverIIClosure

/-!
# Deterministic finite-slice insertion and Cauchy--Schwarz

A pointwise insertion arising from a polynomial power naturally has the
form `1 ≤ K * ∑ i, Bᵢ(t)`.  One cannot in general choose a single index
`i` uniformly in `t`.  This file carries the complete finite sum through
the integral.  Finite Cauchy--Schwarz gives the sharp structural loss
`card J`, and each resulting slice may then be estimated independently.

The theorem is purely deterministic.  It has no number-theoretic input.
-/

namespace ExactSemiprimes
namespace Completion

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Integrated Cauchy--Schwarz after insertion of a finite sum of
nonnegative slices.  The factor `J.card` is the finite Cauchy--Schwarz loss
in `(sum Bᵢ)^2`; `R i` is an arbitrary supplied bound for the corresponding
twisted slice moment. -/
theorem finiteSlice_inserted_cauchy
    {ι : Type*} (J : Finset ι) {E : Set ℝ} {u v K L : ℝ}
    {Long Short : ℝ → ℝ} {Slice : ι → ℝ → ℝ}
    {R : ι → ℝ}
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc u v)
    (hK : 0 ≤ K)
    (hLong : Continuous Long) (hShort : Continuous Short)
    (hSlice : ∀ i ∈ J, Continuous (Slice i))
    (hSliceNonneg : ∀ i ∈ J, ∀ t ∈ E, 0 ≤ Slice i t)
    (hinsert : ∀ t ∈ E, 1 ≤ K * ∑ i ∈ J, Slice i t)
    (hlongMoment : (∫ t in E, Long t ^ (4 : ℕ)) ≤ L)
    (hsliceMoment : ∀ i ∈ J,
      (∫ t in E, Short t ^ (4 : ℕ) * Slice i t ^ (2 : ℕ)) ≤
        R i) :
    (∫ t in E, Long t ^ (2 : ℕ) * Short t ^ (2 : ℕ)) ≤
      K *
        ((((J.card : ℝ) * ∑ i ∈ J, R i) ^ (1 / 2 : ℝ)) *
          L ^ (1 / 2 : ℝ)) := by
  let SliceSum : ℝ → ℝ := fun t ↦ ∑ i ∈ J, Slice i t
  have hSliceSum : Continuous SliceSum := by
    dsimp [SliceSum]
    apply continuous_finsetSum
    intro i hi
    exact hSlice i hi
  have hSliceSumNonneg : ∀ t ∈ E, 0 ≤ SliceSum t := by
    intro t ht
    exact Finset.sum_nonneg fun i hi ↦ hSliceNonneg i hi t ht
  have hmeasF : AEStronglyMeasurable
      (fun t ↦ Short t ^ 2 * SliceSum t) (volume.restrict E) :=
    ((hShort.pow 2).mul hSliceSum).aestronglyMeasurable
  have hmeasG : AEStronglyMeasurable
      (fun t ↦ Long t ^ 2) (volume.restrict E) :=
    (hLong.pow 2).aestronglyMeasurable
  have hintF : IntegrableOn
      (fun t ↦ (Short t ^ 2 * SliceSum t) ^ 2) E :=
    (((hShort.pow 2).mul hSliceSum).pow 2).integrableOn_Icc.mono_set hEsub
  have hintG : IntegrableOn (fun t ↦ (Long t ^ 2) ^ 2) E :=
    ((hLong.pow 2).pow 2).integrableOn_Icc.mono_set hEsub
  have hintLeft : IntegrableOn
      (fun t ↦ Long t ^ 2 * Short t ^ 2) E :=
    ((hLong.pow 2).mul (hShort.pow 2)).integrableOn_Icc.mono_set hEsub
  have hintProduct : IntegrableOn
      (fun t ↦ (Short t ^ 2 * SliceSum t) * (Long t ^ 2)) E :=
    (((hShort.pow 2).mul hSliceSum).mul
      (hLong.pow 2)).integrableOn_Icc.mono_set hEsub
  have hcauchy := typeI_integral_le_inserted_cauchy
    hE hK hSliceSumNonneg
    (fun t ht ↦ by simpa [SliceSum] using hinsert t ht)
    hmeasF hmeasG hintF hintG hintLeft hintProduct
  let sliceWeight : ι → ℝ → ℝ := fun i t ↦
    Short t ^ (4 : ℕ) * Slice i t ^ (2 : ℕ)
  have hsliceWeightCont : ∀ i ∈ J, Continuous (sliceWeight i) := by
    intro i hi
    exact (hShort.pow 4).mul ((hSlice i hi).pow 2)
  have hsliceWeightInt : ∀ i ∈ J, IntegrableOn (sliceWeight i) E := by
    intro i hi
    exact (hsliceWeightCont i hi).integrableOn_Icc.mono_set hEsub
  have hrightInt : IntegrableOn
      (fun t ↦ (J.card : ℝ) * ∑ i ∈ J, sliceWeight i t) E := by
    apply Integrable.const_mul
    exact integrable_finsetSum J hsliceWeightInt
  have hleftInt : IntegrableOn
      (fun t ↦ Short t ^ (4 : ℕ) * SliceSum t ^ (2 : ℕ)) E :=
    ((hShort.pow 4).mul (hSliceSum.pow 2)).integrableOn_Icc.mono_set hEsub
  have htwistedPointwise : ∀ t ∈ E,
      Short t ^ (4 : ℕ) * SliceSum t ^ (2 : ℕ) ≤
        (J.card : ℝ) * ∑ i ∈ J, sliceWeight i t := by
    intro t ht
    have hfinite := sq_sum_le_card_mul_sum_sq
      (s := J) (f := fun i ↦ Slice i t)
    dsimp [SliceSum, sliceWeight]
    calc
      Short t ^ (4 : ℕ) * (∑ i ∈ J, Slice i t) ^ (2 : ℕ) ≤
          Short t ^ (4 : ℕ) *
            ((J.card : ℝ) * ∑ i ∈ J, Slice i t ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hfinite (by positivity)
      _ = (J.card : ℝ) *
          ∑ i ∈ J, Short t ^ (4 : ℕ) * Slice i t ^ (2 : ℕ) := by
        calc
          Short t ^ (4 : ℕ) *
                ((J.card : ℝ) * ∑ i ∈ J, Slice i t ^ (2 : ℕ)) =
              (J.card : ℝ) *
                (Short t ^ (4 : ℕ) *
                  ∑ i ∈ J, Slice i t ^ (2 : ℕ)) := by ring
          _ = _ := by rw [Finset.mul_sum]
  have htwistedIntegral :
      (∫ t in E, Short t ^ (4 : ℕ) * SliceSum t ^ (2 : ℕ)) ≤
        (J.card : ℝ) * ∑ i ∈ J, R i := by
    calc
      (∫ t in E, Short t ^ (4 : ℕ) * SliceSum t ^ (2 : ℕ)) ≤
          ∫ t in E, (J.card : ℝ) * ∑ i ∈ J, sliceWeight i t := by
        apply setIntegral_mono_on hleftInt hrightInt hE
        exact htwistedPointwise
      _ = (J.card : ℝ) * ∑ i ∈ J, ∫ t in E, sliceWeight i t := by
        rw [integral_const_mul, integral_finsetSum]
        intro i hi
        exact hsliceWeightInt i hi
      _ ≤ (J.card : ℝ) * ∑ i ∈ J, R i := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg J.card)
        apply Finset.sum_le_sum
        intro i hi
        simpa [sliceWeight] using hsliceMoment i hi
  have htwistedNonneg : 0 ≤
      ∫ t in E, Short t ^ (4 : ℕ) * SliceSum t ^ (2 : ℕ) :=
    setIntegral_nonneg hE fun t ht ↦
      mul_nonneg (by positivity) (by positivity)
  have htwistedBoundNonneg :
      0 ≤ (J.card : ℝ) * ∑ i ∈ J, R i :=
    htwistedNonneg.trans htwistedIntegral
  have hlongNonneg : 0 ≤ ∫ t in E, Long t ^ (4 : ℕ) :=
    setIntegral_nonneg hE fun t ht ↦ by positivity
  have hLnonneg : 0 ≤ L := hlongNonneg.trans hlongMoment
  have htwistedHalf := Real.rpow_le_rpow htwistedNonneg htwistedIntegral
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hlongHalf := Real.rpow_le_rpow hlongNonneg hlongMoment
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hproduct :
      ((∫ t in E, Short t ^ (4 : ℕ) * SliceSum t ^ (2 : ℕ)) ^
          (1 / 2 : ℝ)) *
          ((∫ t in E, Long t ^ (4 : ℕ)) ^ (1 / 2 : ℝ)) ≤
        (((J.card : ℝ) * ∑ i ∈ J, R i) ^ (1 / 2 : ℝ)) *
          L ^ (1 / 2 : ℝ) := by
    exact mul_le_mul htwistedHalf hlongHalf
      (Real.rpow_nonneg hlongNonneg _)
      (Real.rpow_nonneg htwistedBoundNonneg _)
  exact hcauchy.trans (mul_le_mul_of_nonneg_left hproduct hK)

/-- Three-factor variant used by the Type-I/II components.  The first
Cauchy moment is independent of the inserted prime-power slices; the
second moment retains the finite slice sum and therefore pays exactly the
same `J.card` loss. -/
theorem finiteSlice_typeIOverII_inserted_cauchy
    {ι : Type*} (J : Finset ι) {E : Set ℝ} {u v K W : ℝ}
    {A₁ A₂ A₃ : ℝ → ℝ} {Slice : ι → ℝ → ℝ}
    {R : ι → ℝ}
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc u v)
    (hK : 0 ≤ K)
    (hA₁ : Continuous A₁) (hA₂ : Continuous A₂)
    (hA₃ : Continuous A₃)
    (hSlice : ∀ i ∈ J, Continuous (Slice i))
    (hA₂nonneg : ∀ t ∈ E, 0 ≤ A₂ t)
    (hSliceNonneg : ∀ i ∈ J, ∀ t ∈ E, 0 ≤ Slice i t)
    (hinsert : ∀ t ∈ E, 1 ≤ K * ∑ i ∈ J, Slice i t)
    (hWattMoment : (∫ t in E, A₃ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ)) ≤ W)
    (hsliceMoment : ∀ i ∈ J,
      (∫ t in E,
        A₁ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ) *
          Slice i t ^ (2 : ℕ)) ≤ R i) :
    (∫ t in E,
      A₁ t ^ (2 : ℕ) * A₂ t ^ (2 : ℕ) * A₃ t ^ (2 : ℕ)) ≤
      K *
        (W ^ (1 / 2 : ℝ) *
          (((J.card : ℝ) * ∑ i ∈ J, R i) ^ (1 / 2 : ℝ))) := by
  let SliceSum : ℝ → ℝ := fun t ↦ ∑ i ∈ J, Slice i t
  have hSliceSum : Continuous SliceSum := by
    dsimp [SliceSum]
    apply continuous_finsetSum
    intro i hi
    exact hSlice i hi
  have hSliceSumNonneg : ∀ t ∈ E, 0 ≤ SliceSum t := by
    intro t ht
    exact Finset.sum_nonneg fun i hi ↦ hSliceNonneg i hi t ht
  have hmeasF : AEStronglyMeasurable
      (fun t ↦ A₃ t ^ 2 * A₂ t) (volume.restrict E) :=
    ((hA₃.pow 2).mul hA₂).aestronglyMeasurable
  have hmeasG : AEStronglyMeasurable
      (fun t ↦ A₁ t ^ 2 * A₂ t * SliceSum t) (volume.restrict E) :=
    (((hA₁.pow 2).mul hA₂).mul hSliceSum).aestronglyMeasurable
  have hintF : IntegrableOn (fun t ↦ (A₃ t ^ 2 * A₂ t) ^ 2) E :=
    (((hA₃.pow 2).mul hA₂).pow 2).integrableOn_Icc.mono_set hEsub
  have hintG : IntegrableOn
      (fun t ↦ (A₁ t ^ 2 * A₂ t * SliceSum t) ^ 2) E :=
    ((((hA₁.pow 2).mul hA₂).mul hSliceSum).pow 2)
      |>.integrableOn_Icc.mono_set hEsub
  have hintLeft : IntegrableOn
      (fun t ↦ A₁ t ^ 2 * A₂ t ^ 2 * A₃ t ^ 2) E :=
    (((hA₁.pow 2).mul (hA₂.pow 2)).mul (hA₃.pow 2))
      |>.integrableOn_Icc.mono_set hEsub
  have hintProduct : IntegrableOn
      (fun t ↦ (A₃ t ^ 2 * A₂ t) *
        (A₁ t ^ 2 * A₂ t * SliceSum t)) E :=
    (((hA₃.pow 2).mul hA₂).mul
      (((hA₁.pow 2).mul hA₂).mul hSliceSum))
      |>.integrableOn_Icc.mono_set hEsub
  have hcauchy := typeIOverII_integral_le_inserted_cauchy
    hE hK hA₂nonneg hSliceSumNonneg
    (fun t ht ↦ by simpa [SliceSum] using hinsert t ht)
    hmeasF hmeasG hintF hintG hintLeft hintProduct
  let sliceWeight : ι → ℝ → ℝ := fun i t ↦
    A₁ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ) * Slice i t ^ (2 : ℕ)
  have hsliceWeightCont : ∀ i ∈ J, Continuous (sliceWeight i) := by
    intro i hi
    exact ((hA₁.pow 4).mul (hA₂.pow 2)).mul ((hSlice i hi).pow 2)
  have hsliceWeightInt : ∀ i ∈ J, IntegrableOn (sliceWeight i) E := by
    intro i hi
    exact (hsliceWeightCont i hi).integrableOn_Icc.mono_set hEsub
  have hrightInt : IntegrableOn
      (fun t ↦ (J.card : ℝ) * ∑ i ∈ J, sliceWeight i t) E := by
    apply Integrable.const_mul
    exact integrable_finsetSum J hsliceWeightInt
  have hleftInt : IntegrableOn
      (fun t ↦ A₁ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ) *
        SliceSum t ^ (2 : ℕ)) E :=
    (((hA₁.pow 4).mul (hA₂.pow 2)).mul (hSliceSum.pow 2))
      |>.integrableOn_Icc.mono_set hEsub
  have hpointwise : ∀ t ∈ E,
      A₁ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ) * SliceSum t ^ (2 : ℕ) ≤
        (J.card : ℝ) * ∑ i ∈ J, sliceWeight i t := by
    intro t ht
    have hfinite := sq_sum_le_card_mul_sum_sq
      (s := J) (f := fun i ↦ Slice i t)
    dsimp [SliceSum, sliceWeight]
    let prefactor := A₁ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ)
    calc
      prefactor * (∑ i ∈ J, Slice i t) ^ (2 : ℕ) ≤
          prefactor * ((J.card : ℝ) *
            ∑ i ∈ J, Slice i t ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hfinite (by dsimp [prefactor]; positivity)
      _ = (J.card : ℝ) *
          ∑ i ∈ J,
            A₁ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ) *
              Slice i t ^ (2 : ℕ) := by
        dsimp [prefactor]
        calc
          (A₁ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ)) *
                ((J.card : ℝ) * ∑ i ∈ J, Slice i t ^ (2 : ℕ)) =
              (J.card : ℝ) *
                ((A₁ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ)) *
                  ∑ i ∈ J, Slice i t ^ (2 : ℕ)) := by ring
          _ = _ := by rw [Finset.mul_sum]
  have hsliceIntegral :
      (∫ t in E,
        A₁ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ) * SliceSum t ^ (2 : ℕ)) ≤
        (J.card : ℝ) * ∑ i ∈ J, R i := by
    calc
      (∫ t in E,
          A₁ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ) * SliceSum t ^ (2 : ℕ)) ≤
          ∫ t in E, (J.card : ℝ) * ∑ i ∈ J, sliceWeight i t := by
        apply setIntegral_mono_on hleftInt hrightInt hE
        exact hpointwise
      _ = (J.card : ℝ) * ∑ i ∈ J, ∫ t in E, sliceWeight i t := by
        rw [integral_const_mul, integral_finsetSum]
        intro i hi
        exact hsliceWeightInt i hi
      _ ≤ (J.card : ℝ) * ∑ i ∈ J, R i := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg J.card)
        apply Finset.sum_le_sum
        intro i hi
        simpa [sliceWeight] using hsliceMoment i hi
  have hsliceNonneg : 0 ≤
      ∫ t in E,
        A₁ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ) * SliceSum t ^ (2 : ℕ) :=
    setIntegral_nonneg hE fun t ht ↦ by positivity
  have hsliceBoundNonneg : 0 ≤ (J.card : ℝ) * ∑ i ∈ J, R i :=
    hsliceNonneg.trans hsliceIntegral
  have hWattNonneg : 0 ≤ ∫ t in E,
      A₃ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ) :=
    setIntegral_nonneg hE fun t ht ↦ by positivity
  have hWnonneg : 0 ≤ W := hWattNonneg.trans hWattMoment
  have hWattHalf := Real.rpow_le_rpow hWattNonneg hWattMoment
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hsliceHalf := Real.rpow_le_rpow hsliceNonneg hsliceIntegral
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hproduct :
      ((∫ t in E, A₃ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ)) ^
          (1 / 2 : ℝ)) *
          ((∫ t in E,
            A₁ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ) *
              SliceSum t ^ (2 : ℕ)) ^ (1 / 2 : ℝ)) ≤
        W ^ (1 / 2 : ℝ) *
          (((J.card : ℝ) * ∑ i ∈ J, R i) ^ (1 / 2 : ℝ)) := by
    exact mul_le_mul hWattHalf hsliceHalf
      (Real.rpow_nonneg hsliceNonneg _)
      (Real.rpow_nonneg hWnonneg _)
  exact hcauchy.trans (mul_le_mul_of_nonneg_left hproduct hK)

def finiteSliceInsertedCauchyModule : ProofModule :=
  { name := "Completion.FiniteSliceInsertedCauchy"
    paperLocation := "MT23 Section 5.1, finite dyadic insertion"
    purpose :=
      "Carry a quantifier-correct finite sum of inserted slice norms through integrated Cauchy--Schwarz, with the exact cardinality loss and independently supplied slice moments."
    dependsOn := ["Completion.TypeIComponentClosure"]
    status := .proved }

end

end Completion
end ExactSemiprimes
