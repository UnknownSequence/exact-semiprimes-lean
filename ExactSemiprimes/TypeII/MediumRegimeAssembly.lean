import ExactSemiprimes.TypeII.TypeIIEstimate

/-!
# Complete assembly of the medium Type–II regime

This module turns the binwise Guth–Maynard input into a bound for the entire
finite medium range.  It includes the exact logarithmic-bin count and keeps
all parameter choices in the order required by `TypeIIEstimateStatement`.
-/

namespace ExactSemiprimes
namespace TypeII

open Filter
open scoped BigOperators

noncomputable section

theorem inv_log_le_of_rpow_le
    {T N alpha w : ℝ}
    (hT : 1 < T) (halpha : 0 < alpha) (hw : 0 < w)
    (hlower : T ^ alpha ≤ N)
    (hlogSize : 1 ≤ w * alpha * Real.log T) :
    1 < N ∧ 1 / Real.log N ≤ w := by
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hpowOne : 1 < T ^ alpha := Real.one_lt_rpow hT halpha
  have hNone : 1 < N := hpowOne.trans_le hlower
  have hpowPos : 0 < T ^ alpha := Real.rpow_pos_of_pos hTpos alpha
  have hlogLower : alpha * Real.log T ≤ Real.log N := by
    rw [← Real.log_rpow hTpos alpha]
    exact Real.log_le_log hpowPos hlower
  have hlogN : 0 < Real.log N := Real.log_pos hNone
  refine ⟨hNone, ?_⟩
  rw [div_le_iff₀ hlogN]
  exact hlogSize.trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hlogLower hw.le)

theorem eventually_mediumBinWidths
    {eps kappa : ℝ} (heps : 0 < eps) (_hkappa : 0 < kappa)
    (hepsSmall : eps ≤ 1 / 1000) :
    ∀ᶠ T : ℝ in atTop, ∀ N₁ N₂ : ℕ,
      T ^ (eps / 5) ≤ (N₁ : ℝ) →
      T ^ (9 / 11 - 10 * eps) ≤ (N₂ : ℝ) →
      1 < (N₁ : ℝ) ∧ 1 < (N₂ : ℝ) ∧
      1 / Real.log (N₁ : ℝ) + mediumThresholdShift eps kappa ≤
        2 * eps ∧
      1 / Real.log (N₂ : ℝ) ≤ 2 * eps := by
  have halpha₁ : 0 < eps / 5 := by positivity
  have halpha₂ : 0 < 9 / 11 - 10 * eps := by
    norm_num at hepsSmall ⊢
    linarith
  have hc₁ : 0 < eps * (eps / 5) := mul_pos heps halpha₁
  have hc₂ : 0 < (2 * eps) * (9 / 11 - 10 * eps) :=
    mul_pos (by positivity) halpha₂
  have hlog₁ := Real.tendsto_log_atTop.eventually_ge_atTop
    (eps * (eps / 5))⁻¹
  have hlog₂ := Real.tendsto_log_atTop.eventually_ge_atTop
    ((2 * eps) * (9 / 11 - 10 * eps))⁻¹
  filter_upwards [eventually_gt_atTop (1 : ℝ), hlog₁, hlog₂] with
      T hT hlogT₁ hlogT₂
  intro N₁ N₂ hN₁lower hN₂lower
  have hsize₁ : 1 ≤ eps * (eps / 5) * Real.log T := by
    calc
      1 = (eps * (eps / 5)) * (eps * (eps / 5))⁻¹ := by
        exact (mul_inv_cancel₀ (ne_of_gt hc₁)).symm
      _ ≤ (eps * (eps / 5)) * Real.log T :=
        mul_le_mul_of_nonneg_left hlogT₁ hc₁.le
  have hsize₂ :
      1 ≤ (2 * eps) * (9 / 11 - 10 * eps) * Real.log T := by
    calc
      1 = ((2 * eps) * (9 / 11 - 10 * eps)) *
          ((2 * eps) * (9 / 11 - 10 * eps))⁻¹ := by
        exact (mul_inv_cancel₀ (ne_of_gt hc₂)).symm
      _ ≤ ((2 * eps) * (9 / 11 - 10 * eps)) * Real.log T :=
        mul_le_mul_of_nonneg_left hlogT₂ hc₂.le
  have hw₁ := inv_log_le_of_rpow_le hT halpha₁ heps hN₁lower hsize₁
  have hw₂ := inv_log_le_of_rpow_le hT halpha₂ (by positivity)
    hN₂lower hsize₂
  refine ⟨hw₁.1, hw₂.1, ?_, hw₂.2⟩
  have hshift := mediumThresholdShift_le_eps eps kappa
  linarith

theorem logBinCount_cast_le_log_add_one_sq {T : ℝ} (hT : 1 ≤ T) :
    ((((⌊Real.log T⌋ + 1).toNat) ^ 2 : ℕ) : ℝ) ≤
      (Real.log T + 1) ^ (2 : ℕ) := by
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hz : (0 : ℤ) ≤ ⌊Real.log T⌋ + 1 := by
    have := Int.floor_nonneg.mpr hlog
    omega
  have hbase : (((⌊Real.log T⌋ + 1).toNat : ℕ) : ℝ) ≤
      Real.log T + 1 := by
    calc
      (((⌊Real.log T⌋ + 1).toNat : ℕ) : ℝ) =
          ((⌊Real.log T⌋ + 1 : ℤ) : ℝ) := by
        norm_cast
        exact Int.toNat_of_nonneg hz
      _ ≤ Real.log T + 1 := by
        simpa [Int.cast_add, add_comm] using
          add_le_add_right (Int.floor_le (Real.log T)) 1
  norm_num only [Nat.cast_pow]
  exact pow_le_pow_left₀ (by positivity) hbase 2

theorem eventually_logBinCount_le_rpow
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ T : ℝ in atTop,
      ((((⌊Real.log T⌋ + 1).toNat) ^ 2 : ℕ) : ℝ) ≤
        T ^ (delta / 2) := by
  have hquarter : 0 < delta / 4 := by positivity
  have hlog := eventually_log_rpow_le_rpow 2 hquarter
  have hconst : ∀ᶠ T : ℝ in atTop, (4 : ℝ) ≤ T ^ (delta / 4) :=
    (tendsto_rpow_atTop hquarter).eventually_ge_atTop 4
  have hlogOne : ∀ᶠ T : ℝ in atTop, 1 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlog, hconst, hlogOne] with
      T hT hlogT hconstT hlogOneT
  have hcount := logBinCount_cast_le_log_add_one_sq hT
  have hlogT' : (Real.log T) ^ (2 : ℕ) ≤ T ^ (delta / 4) := by
    rw [← Real.rpow_natCast]
    exact hlogT
  have hadd : Real.log T + 1 ≤ 2 * Real.log T := by linarith
  have hsquare : (Real.log T + 1) ^ (2 : ℕ) ≤
      4 * (Real.log T) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (Real.log T + 1), sq_nonneg (Real.log T)]
  calc
    ((((⌊Real.log T⌋ + 1).toNat) ^ 2 : ℕ) : ℝ) ≤
        4 * (Real.log T) ^ (2 : ℕ) := hcount.trans hsquare
    _ ≤ T ^ (delta / 4) * T ^ (delta / 4) :=
      mul_le_mul hconstT hlogT' (by positivity) (by positivity)
    _ = T ^ (delta / 2) := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hT)]
      congr 1
      ring

/-- The exact square logarithmic-bin count is absorbed by half of any fixed
positive power saving.  The nonnegative multiplicative constant is retained
verbatim, which is the form needed after the medium-bin sum. -/
theorem eventually_logBinCount_mul_const_rpow_neg_le
    {delta D : ℝ} (hdelta : 0 < delta) (hD : 0 ≤ D) :
    ∀ᶠ T : ℝ in atTop,
      (((((⌊Real.log T⌋ + 1).toNat) ^ 2 : ℕ) : ℝ) *
        (D * T ^ (-delta))) ≤
      D * T ^ (-(delta / 2)) := by
  have hcount := eventually_logBinCount_le_rpow hdelta
  filter_upwards [hcount, eventually_gt_atTop (1 : ℝ)] with T hcountT hT
  have hTnonneg : 0 ≤ T := (zero_lt_one.trans hT).le
  calc
    (((((⌊Real.log T⌋ + 1).toNat) ^ 2 : ℕ) : ℝ) *
        (D * T ^ (-delta))) ≤
        T ^ (delta / 2) * (D * T ^ (-delta)) :=
      mul_le_mul_of_nonneg_right hcountT
        (mul_nonneg hD (Real.rpow_nonneg hTnonneg _))
    _ = D * (T ^ (delta / 2) * T ^ (-delta)) := by ring
    _ = D * T ^ (delta / 2 + (-delta)) := by
      rw [Real.rpow_add (zero_lt_one.trans hT)]
    _ = D * T ^ (-(delta / 2)) := by ring_nf

/-- Complete discrete assembly of the medium range, retaining the exact
finite logarithmic-bin count. -/
theorem eventually_sum_finiteLargeValueR2_le_logBinCount_of_guthMaynard
    (inputs : ExternalInputs) :
    ∃ thresholdLoss : ℝ, 0 < thresholdLoss ∧
      ∀ B : ℝ, 0 ≤ B →
        ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 1000 →
          ∃ kappa : ℝ, 0 < kappa ∧
            ∀ A L : ℝ, 1 ≤ A → 0 ≤ L →
              ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
                ∀ᶠ T : ℝ in atTop,
                  ∀ (N₁ N₂ : ℕ) (a₁ a₂ : ℕ → ℂ) (R : Finset ℝ),
                    1 ≤ N₁ → 1 ≤ N₂ →
                    (Real.log T) ^ (-L) ≤
                      ((N₁ : ℝ) * (N₂ : ℝ)) / T →
                    ((N₁ : ℝ) * (N₂ : ℝ)) / T ≤
                      (Real.log T) ^ L →
                    T ^ (eps / 5) ≤ (N₁ : ℝ) →
                    (N₁ : ℝ) ≤ T ^ (2 / 11 + eps) →
                    IsDivisorBoundedByConstant B A a₁ →
                    IsDivisorBoundedByConstant B A a₂ →
                    (R : Set ℝ) ⊆ Set.Icc (0 : ℝ) T →
                    IsOneSpaced (R : Set ℝ) →
                    (∀ t ∈ R,
                      (N₁ : ℝ) ^
                          (-(17 / 70 - (thresholdLoss + 2) * eps)) ≤
                            ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ)
                              (onePlusIT t)‖ ∨
                      (N₂ : ℝ) ^
                          (-(17 / 70 - (thresholdLoss + 2) * eps)) ≤
                            ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ)
                              (onePlusIT t)‖) →
                    (∑ t ∈ finiteLargeValueR2 R
                        (dyadicDirichletPolynomial a₁ (N₁ : ℝ))
                        (dyadicDirichletPolynomial a₂ (N₂ : ℝ))
                        (N₁ : ℝ) (N₂ : ℝ) T eps,
                      ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ)
                          (onePlusIT t)‖ ^ 2 *
                      ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ)
                          (onePlusIT t)‖ ^ 2) ≤
                      ((((⌊Real.log T⌋ + 1).toNat) ^ 2 : ℕ) : ℝ) *
                        (Real.exp 4 *
                          ((mediumPowerOrderCap eps : ℝ) * C) *
                          T ^ (-mediumResidualSaving kappa)) := by
  obtain ⟨thresholdLoss, hthresholdLoss, hmedium⟩ :=
    mediumWeightedBin_of_guthMaynard inputs
  refine ⟨thresholdLoss, hthresholdLoss, ?_⟩
  intro B hB eps heps hepsSmall
  have hK : 1 ≤ mediumPowerOrderCap eps := by
    rw [mediumPowerOrderCap, Nat.one_le_ceil_iff]
    positivity
  obtain ⟨kappa, hkappa, hmedium⟩ :=
    hmedium (mediumPowerOrderCap eps) hK B hB eps heps hepsSmall
  refine ⟨kappa, hkappa, ?_⟩
  intro A L hA hL
  obtain ⟨C, T₀, hC, hT₀, hmedium⟩ := hmedium A hA
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  let shift := mediumThresholdShift eps kappa
  let xi := mediumProductLoss kappa
  let delta := mediumResidualSaving kappa
  have hshift : 0 < shift := mediumThresholdShift_pos heps hkappa
  have hxi : 0 < xi := mediumProductLoss_pos hkappa
  have hdelta : 0 < delta := mediumResidualSaving_pos hkappa
  have hgeometry := eventually_exists_outerTypeIILengthGeometry L
    heps (hepsSmall.trans (by norm_num)) hshift hxi
  have hwidths := eventually_mediumBinWidths heps hkappa hepsSmall
  filter_upwards [hgeometry, hwidths, eventually_ge_atTop T₀,
    eventually_gt_atTop (1 : ℝ)] with T hgeometryT hwidthsT hT₀T hTone
  intro N₁ N₂ a₁ a₂ R hN₁ hN₂ hprodLower hprodUpper
    hN₁lower hN₁upper ha₁ ha₂ hR hspaced hlarge
  obtain ⟨eta₁, eta₂, ell, hmodel₁, hmodel₂, heta₁, heta₂,
      hellFive, hellK, hproduct, hPlower, hPupper, hN₂lower,
      hN₂upper, habsorb⟩ :=
    hgeometryT N₁ N₂ hN₁ hN₂ hprodLower hprodUpper
      hN₁lower hN₁upper
  obtain ⟨hN₁gt, hN₂gt, hwidth₁, hwidth₂⟩ :=
    hwidthsT N₁ N₂ hN₁lower hN₂lower
  let M₁ : ℂ → ℂ := dyadicDirichletPolynomial a₁ (N₁ : ℝ)
  let M₂ : ℂ → ℂ := dyadicDirichletPolynomial a₂ (N₂ : ℝ)
  let V : ℝ := Real.exp 4 * ((mediumPowerOrderCap eps : ℝ) * C) *
    T ^ (-delta)
  have hV : 0 ≤ V := by
    dsimp [V]
    positivity
  apply sum_finiteLargeValueR2_le_logBinCount_mul R M₁ M₂
    (N₁ : ℝ) (N₂ : ℝ) T eps V
    (fun t ↦ (typeIIMagnitude M₁ t) ^ 2 *
      (typeIIMagnitude M₂ t) ^ 2)
    (zero_lt_one.trans hTone) (by exact_mod_cast hN₁)
    (by exact_mod_cast hN₂) heps.le hV
  intro k hk
  let Rk := finiteMediumLogMagnitudeBin R M₁ M₂
    (N₁ : ℝ) (N₂ : ℝ) T eps k
  have hRkne : Rk.Nonempty := by
    rcases Finset.mem_image.mp hk with ⟨t, ht, htk⟩
    refine ⟨t, ?_⟩
    exact Finset.mem_filter.mpr ⟨ht, htk⟩
  have hRkR2 : ∀ t ∈ Rk,
      t ∈ largeValueR2 (R : Set ℝ) M₁ M₂
        (N₁ : ℝ) (N₂ : ℝ) T eps := by
    intro t ht
    exact (mem_finiteLargeValueR2_iff.mp
      (Finset.mem_filter.mp ht).1).2
  have hRkbin : ∀ t ∈ Rk,
      t ∈ logMagnitudePairBin M₁ M₂ k.1 k.2 := by
    intro t ht
    have hcanonical := (Finset.mem_filter.mp ht).2
    rw [← hcanonical]
    exact ⟨mem_logMagnitudeBin_floor M₁ t,
      mem_logMagnitudeBin_floor M₂ t⟩
  have hRkpos : ∀ t ∈ Rk,
      0 < typeIIMagnitude M₁ t ∧ 0 < typeIIMagnitude M₂ t := by
    intro t ht
    exact typeIIMagnitudes_pos_of_mem_largeValueR2
      (zero_lt_one.trans hTone) (hRkR2 t ht)
  have htauLower :=
    upperBinExponents_medium_lower_bounds_of_nonempty_R2_bin
      hN₁gt hN₂gt (zero_lt_one.trans hTone) heps.le hshift.le hRkne
      hRkR2 hRkbin
  have htauUpper :
      min (upperBinExponent (N₁ : ℝ) k.1 + shift)
          (upperBinExponent (N₂ : ℝ) k.2) ≤
        17 / 70 - thresholdLoss * eps := by
    obtain ⟨t, ht⟩ := hRkne
    apply min_upperBinExponent_shifted_outer_threshold
      hN₁gt hN₂gt (hRkbin t ht) (hRkpos t ht).1 (hRkpos t ht).2
    · exact hlarge t (mem_finiteLargeValueR2_iff.mp
        (Finset.mem_filter.mp ht).1).1
    · simpa only [shift] using hwidth₁
    · exact hwidth₂
  have hmin :
      min (upperBinExponent (N₁ : ℝ) k.1)
          (upperBinExponent (N₂ : ℝ) k.2) ≤ 1 := by
    have hmono :
        min (upperBinExponent (N₁ : ℝ) k.1)
            (upperBinExponent (N₂ : ℝ) k.2) ≤
          min (upperBinExponent (N₁ : ℝ) k.1 + shift)
            (upperBinExponent (N₂ : ℝ) k.2) := by
      exact min_le_min (by linarith) le_rfl
    have hright : 17 / 70 - thresholdLoss * eps ≤ 1 := by
      have hprodpos : 0 < thresholdLoss * eps := mul_pos hthresholdLoss heps
      nlinarith
    exact hmono.trans (htauUpper.trans hright)
  have hgap :
      2 * xi * min (upperBinExponent (N₁ : ℝ) k.1)
          (upperBinExponent (N₂ : ℝ) k.2) + delta ≤
        kappa - 2 * shift := by
    simpa only [xi, delta, shift] using
      medium_explicit_reserve_gap hkappa htauLower.1 htauLower.2.1 hmin
  have hRkspaced : IsOneSpaced (Rk : Set ℝ) := by
    apply hspaced.mono
    intro t ht
    exact (mem_finiteLargeValueR2_iff.mp
      (Finset.mem_filter.mp ht).1).1
  have hRkinterval : ∀ t ∈ Rk, t ∈ Set.Icc (0 : ℝ) T := by
    intro t ht
    exact hR (mem_finiteLargeValueR2_iff.mp
      (Finset.mem_filter.mp ht).1).1
  have hlarge₁ : ∀ t ∈ Rk,
      (N₁ : ℝ) ^ (-upperBinExponent (N₁ : ℝ) k.1) <
        ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ) (onePlusIT t)‖ := by
    intro t ht
    exact (magnitude_bounds_of_mem_logMagnitudeBin_upperExponent
      hN₁gt (hRkbin t ht).1 (hRkpos t ht).1).1
  have hlarge₂ : ∀ t ∈ Rk,
      (N₂ : ℝ) ^ (-upperBinExponent (N₂ : ℝ) k.2) <
        ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ) (onePlusIT t)‖ := by
    intro t ht
    exact (magnitude_bounds_of_mem_logMagnitudeBin_upperExponent
      hN₂gt (hRkbin t ht).2 (hRkpos t ht).2).1
  have hcardWeight := hmedium ell N₁ N₂ eta₁ eta₂ xi delta shift
    (upperBinExponent (N₁ : ℝ) k.1)
    (upperBinExponent (N₂ : ℝ) k.2) T a₁ a₂ Rk
    (by omega) hellK hN₁ hN₂ hT₀T hTone hmodel₁ hmodel₂
    heta₁ heta₂ hproduct hPlower hPupper hN₂lower hN₂upper
    hshift.le habsorb htauLower.1 htauLower.2.1 htauLower.2.2.1
    htauUpper htauLower.2.2.2 hgap ha₁ ha₂ hRkspaced hRkinterval
    hlarge₁ hlarge₂
  have hbinSum := sum_typeIIWeight_logMagnitudePairBin_le_of_cardWeight
    hN₁gt hN₂gt Rk hRkbin (fun t ht ↦ (hRkpos t ht).1)
    (fun t ht ↦ (hRkpos t ht).2) hcardWeight
  calc
    (∑ t ∈ Rk, (typeIIMagnitude M₁ t) ^ 2 *
        (typeIIMagnitude M₂ t) ^ 2) ≤
        Real.exp 4 * (((ell : ℝ) * C) * T ^ (-delta)) := hbinSum
    _ ≤ V := by
      dsimp only [V]
      have hellReal : (ell : ℝ) ≤ (mediumPowerOrderCap eps : ℝ) := by
        exact_mod_cast hellK
      have hcoeff : (ell : ℝ) * C ≤
          (mediumPowerOrderCap eps : ℝ) * C :=
        mul_le_mul_of_nonneg_right hellReal hC.le
      calc
        Real.exp 4 * (((ell : ℝ) * C) * T ^ (-delta)) =
            (Real.exp 4 * ((ell : ℝ) * C)) * T ^ (-delta) := by ring
        _ ≤ (Real.exp 4 * ((mediumPowerOrderCap eps : ℝ) * C)) *
            T ^ (-delta) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcoeff (Real.exp_pos 4).le)
            (Real.rpow_nonneg (zero_lt_one.trans hTone).le _)

/-- Pure-power form of the complete medium-range estimate.  The square
logarithmic-bin count consumes exactly half of `mediumResidualSaving kappa`;
the coefficient and every outer quantifier are unchanged. -/
theorem eventually_sum_finiteLargeValueR2_le_power_of_guthMaynard
    (inputs : ExternalInputs) :
    ∃ thresholdLoss : ℝ, 0 < thresholdLoss ∧
      ∀ B : ℝ, 0 ≤ B →
        ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 1000 →
          ∃ kappa : ℝ, 0 < kappa ∧
            ∀ A L : ℝ, 1 ≤ A → 0 ≤ L →
              ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
                ∀ᶠ T : ℝ in atTop,
                  ∀ (N₁ N₂ : ℕ) (a₁ a₂ : ℕ → ℂ) (R : Finset ℝ),
                    1 ≤ N₁ → 1 ≤ N₂ →
                    (Real.log T) ^ (-L) ≤
                      ((N₁ : ℝ) * (N₂ : ℝ)) / T →
                    ((N₁ : ℝ) * (N₂ : ℝ)) / T ≤
                      (Real.log T) ^ L →
                    T ^ (eps / 5) ≤ (N₁ : ℝ) →
                    (N₁ : ℝ) ≤ T ^ (2 / 11 + eps) →
                    IsDivisorBoundedByConstant B A a₁ →
                    IsDivisorBoundedByConstant B A a₂ →
                    (R : Set ℝ) ⊆ Set.Icc (0 : ℝ) T →
                    IsOneSpaced (R : Set ℝ) →
                    (∀ t ∈ R,
                      (N₁ : ℝ) ^
                          (-(17 / 70 - (thresholdLoss + 2) * eps)) ≤
                            ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ)
                              (onePlusIT t)‖ ∨
                      (N₂ : ℝ) ^
                          (-(17 / 70 - (thresholdLoss + 2) * eps)) ≤
                            ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ)
                              (onePlusIT t)‖) →
                    (∑ t ∈ finiteLargeValueR2 R
                        (dyadicDirichletPolynomial a₁ (N₁ : ℝ))
                        (dyadicDirichletPolynomial a₂ (N₂ : ℝ))
                        (N₁ : ℝ) (N₂ : ℝ) T eps,
                      ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ)
                          (onePlusIT t)‖ ^ 2 *
                      ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ)
                          (onePlusIT t)‖ ^ 2) ≤
                        (Real.exp 4 *
                          ((mediumPowerOrderCap eps : ℝ) * C)) *
                          T ^ (-(mediumResidualSaving kappa / 2)) := by
  obtain ⟨thresholdLoss, hthresholdLoss, hmedium⟩ :=
    eventually_sum_finiteLargeValueR2_le_logBinCount_of_guthMaynard inputs
  refine ⟨thresholdLoss, hthresholdLoss, ?_⟩
  intro B hB eps heps hepsSmall
  obtain ⟨kappa, hkappa, hmedium⟩ := hmedium B hB eps heps hepsSmall
  refine ⟨kappa, hkappa, ?_⟩
  intro A L hA hL
  obtain ⟨C, T₀, hC, hT₀, hmedium⟩ := hmedium A L hA hL
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  have hdelta : 0 < mediumResidualSaving kappa :=
    mediumResidualSaving_pos hkappa
  have hcoefficient :
      0 ≤ Real.exp 4 * ((mediumPowerOrderCap eps : ℝ) * C) := by
    positivity
  have habsorb := eventually_logBinCount_mul_const_rpow_neg_le
    hdelta hcoefficient
  filter_upwards [hmedium, habsorb] with T hmediumT habsorbT
  intro N₁ N₂ a₁ a₂ R hN₁ hN₂ hprodLower hprodUpper
    hN₁lower hN₁upper ha₁ ha₂ hR hspaced hlarge
  exact (hmediumT N₁ N₂ a₁ a₂ R hN₁ hN₂ hprodLower hprodUpper
    hN₁lower hN₁upper ha₁ ha₂ hR hspaced hlarge).trans (by
      simpa only [mul_assoc] using habsorbT)

/-- Registry entry for the completed medium-regime assembly. -/
def mediumRegimeAssemblyModule : ProofModule :=
  { name := "TypeII.MediumRegimeAssembly"
    paperLocation := "Proof of Proposition 5.1, final discrete R₂ insertion"
    purpose := "Sum the source-closed medium-bin estimate over every occupied logarithmic bin."
    dependsOn := ["TypeII.TypeIIEstimate", "TypeII.MediumLogBinBridge",
      "TypeII.OuterParameterReserve", "TypeII.OuterLengthGeometry"]
    status := .proved }

end
end TypeII
end ExactSemiprimes
