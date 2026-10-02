import ExactSemiprimes.TypeII.LargeValuePartition
import ExactSemiprimes.TypeII.HalaszMontgomery
import ExactSemiprimes.TypeII.PoweredMeanValue

/-! # Estimates on the extreme Type-II ranges -/

namespace ExactSemiprimes
namespace TypeII

open scoped BigOperators

noncomputable section

/-- Finite high-moment counting inequality used for the large extreme range
`R₁`.  The analytic mean-value theorem only has to bound the moment on the
right. -/
theorem card_largeValues_mul_threshold_pow_le_moment
    {ι : Type*} (R : Finset ι) (F : ι → ℂ)
    {V : ℝ} (hV : 0 ≤ V) (k : ℕ)
    (hlarge : ∀ t ∈ R, V ≤ ‖F t‖) :
    (R.card : ℝ) * V ^ k ≤ ∑ t ∈ R, ‖F t‖ ^ k := by
  calc
    (R.card : ℝ) * V ^ k = ∑ _t ∈ R, V ^ k := by simp
    _ ≤ ∑ t ∈ R, ‖F t‖ ^ k := by
      apply Finset.sum_le_sum
      intro t ht
      exact pow_le_pow_left₀ hV (hlarge t ht) k

/-- Pointwise contribution of the small extreme range `R₃`: if either
factor is at most `T⁻¹` and the other is bounded by `K`, their product has
squared norm at most `T⁻²K²`. -/
theorem smallFactor_product_sq_le
    {A B : ℂ} {T K : ℝ} (hT : 0 < T) (hK : 0 ≤ K)
    (hA : ‖A‖ ≤ K) (hB : ‖B‖ ≤ K)
    (hsmall : ‖A‖ ≤ T⁻¹ ∨ ‖B‖ ≤ T⁻¹) :
    ‖A * B‖ ^ 2 ≤ T⁻¹ ^ 2 * K ^ 2 := by
  rcases hsmall with hsmallA | hsmallB
  · have hprod : ‖A‖ * ‖B‖ ≤ T⁻¹ * K :=
      mul_le_mul hsmallA hB (norm_nonneg B) (by positivity)
    have hnonneg : 0 ≤ T⁻¹ * K := mul_nonneg (by positivity) hK
    have hsq := (sq_le_sq₀
      (mul_nonneg (norm_nonneg A) (norm_nonneg B)) hnonneg).2 hprod
    simpa [norm_mul, mul_pow] using hsq
  · have hprod : ‖A‖ * ‖B‖ ≤ K * T⁻¹ :=
      mul_le_mul hA hsmallB (norm_nonneg B) hK
    have hnonneg : 0 ≤ K * T⁻¹ := mul_nonneg hK (by positivity)
    have hsq := (sq_le_sq₀
      (mul_nonneg (norm_nonneg A) (norm_nonneg B)) hnonneg).2 hprod
    calc
      ‖A * B‖ ^ 2 ≤ (K * T⁻¹) ^ 2 := by
        simpa [norm_mul] using hsq
      _ = T⁻¹ ^ 2 * K ^ 2 := by ring

/-- Summed version of the preceding `R₃` estimate. -/
theorem sum_smallExtremeRange_le
    {ι : Type*} (R : Finset ι) (A B : ι → ℂ)
    {T K : ℝ} (hT : 0 < T) (hK : 0 ≤ K)
    (hA : ∀ t ∈ R, ‖A t‖ ≤ K)
    (hB : ∀ t ∈ R, ‖B t‖ ≤ K)
    (hsmall : ∀ t ∈ R, ‖A t‖ ≤ T⁻¹ ∨ ‖B t‖ ≤ T⁻¹) :
    ∑ t ∈ R, ‖A t * B t‖ ^ 2 ≤
      (R.card : ℝ) * (T⁻¹ ^ 2 * K ^ 2) := by
  calc
    ∑ t ∈ R, ‖A t * B t‖ ^ 2 ≤
        ∑ _t ∈ R, T⁻¹ ^ 2 * K ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      exact smallFactor_product_sq_le hT hK
        (hA t ht) (hB t ht) (hsmall t ht)
    _ = (R.card : ℝ) * (T⁻¹ ^ 2 * K ^ 2) := by simp

/-- The paper's `O(T^{-1/2})` scale follows from the explicit bounds
`#R≤2T` and `K≤T^(1/4)`. -/
theorem sum_smallExtremeRange_le_two_mul_rpow_neg_half
    {ι : Type*} (R : Finset ι) (A B : ι → ℂ)
    {T K : ℝ} (hT : 1 ≤ T) (hK : 0 ≤ K)
    (hcard : (R.card : ℝ) ≤ 2 * T)
    (hKgrowth : K ≤ T ^ (1 / 4 : ℝ))
    (hA : ∀ t ∈ R, ‖A t‖ ≤ K)
    (hB : ∀ t ∈ R, ‖B t‖ ≤ K)
    (hsmall : ∀ t ∈ R, ‖A t‖ ≤ T⁻¹ ∨ ‖B t‖ ≤ T⁻¹) :
    ∑ t ∈ R, ‖A t * B t‖ ^ 2 ≤
      2 * T ^ (-1 / 2 : ℝ) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hbase := sum_smallExtremeRange_le R A B hTpos hK hA hB hsmall
  have hfactorNonneg : 0 ≤ T⁻¹ ^ 2 * K ^ 2 := by positivity
  have hKsq : K ^ 2 ≤ (T ^ (1 / 4 : ℝ)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ hK hKgrowth 2
  calc
    ∑ t ∈ R, ‖A t * B t‖ ^ 2
        ≤ (R.card : ℝ) * (T⁻¹ ^ 2 * K ^ 2) := hbase
    _ ≤ (2 * T) * (T⁻¹ ^ 2 * K ^ 2) :=
      mul_le_mul_of_nonneg_right hcard hfactorNonneg
    _ ≤ (2 * T) *
        (T⁻¹ ^ 2 * (T ^ (1 / 4 : ℝ)) ^ (2 : ℕ)) := by
      gcongr
    _ = 2 * T ^ (-1 / 2 : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_natCast,
        ← Real.rpow_mul hTpos.le, ← Real.rpow_natCast,
        ← Real.rpow_mul hTpos.le]
      rw [← Real.rpow_add hTpos]
      norm_num
      have hcombine :
          T * T ^ (-(3 / 2 : ℝ)) =
            T ^ (-(1 / 2 : ℝ)) := by
        calc
          T * T ^ (-(3 / 2 : ℝ)) =
              T ^ (1 : ℝ) *
                T ^ (-(3 / 2 : ℝ)) := by
            rw [Real.rpow_one]
          _ = T ^ ((1 : ℝ) +
                (-(3 / 2 : ℝ))) := by
            rw [← Real.rpow_add hTpos]
          _ = T ^ (-(1 / 2 : ℝ)) := by
            congr 1
            ring
      rw [mul_assoc, hcombine]

def extremeRangesModule : ProofModule :=
  { name := "TypeII.ExtremeRanges"
    paperLocation := "Proof of Proposition 5.1, treatment of R₁ and R₃"
    purpose :=
      "Formalize the R₁ high-moment counting inequality and the R₃ pointwise and summed reductions. The bounded-power R₁ absorption and weighted endpoint are completed by ExtremeLargeAbsorption and WeightedExtremeRange; the source-closed R₃ endpoint is completed by ExtremeSmallAssembly."
    dependsOn :=
      [ "TypeII.LargeValuePartition",
        "TypeII.PoweredMeanValue",
        "TypeII.HalaszMontgomery" ]
    status := .proved }

end

end TypeII
end ExactSemiprimes
