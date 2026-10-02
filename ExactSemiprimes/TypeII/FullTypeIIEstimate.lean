import ExactSemiprimes.TypeII.MediumRegimeAssembly
import ExactSemiprimes.TypeII.ExtremeRegimeAssembly

/-!
# Full Type-II estimate

This module closes the final quantified assembly for Proposition 5.1.  It
combines the source-closed extreme and medium finite-sum estimates, absorbs
all fixed and logarithmic losses into an explicit power saving, and invokes
the exact one-spaced-sum-to-integral bridge.
-/

namespace ExactSemiprimes
namespace TypeII

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

/-- A fixed nonnegative coefficient can be absorbed while retaining one
quarter of the original medium-regime power saving. -/
theorem eventually_const_mul_rpow_neg_half_le_quarter
    {delta D : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ T : ℝ in atTop,
      D * T ^ (-(delta / 2)) ≤ T ^ (-(delta / 4)) := by
  have hquarter : 0 < delta / 4 := by positivity
  have hconstant : ∀ᶠ T : ℝ in atTop, D ≤ T ^ (delta / 4) :=
    (tendsto_rpow_atTop hquarter).eventually_ge_atTop D
  filter_upwards [hconstant, eventually_gt_atTop (1 : ℝ)] with
      T hconstantT hTone
  have hTpos : 0 < T := zero_lt_one.trans hTone
  calc
    D * T ^ (-(delta / 2)) ≤
        T ^ (delta / 4) * T ^ (-(delta / 2)) :=
      mul_le_mul_of_nonneg_right hconstantT
        (Real.rpow_nonneg hTpos.le _)
    _ = T ^ (-(delta / 4)) := by
      rw [← Real.rpow_add hTpos]
      congr 1
      ring

/-- All three finite regimes, and then the exact one-spaced-to-integral
bridge, establish the fully quantified Type-II estimate. -/
theorem typeIIEstimateStatement_of_externalInputs
    (inputs : ExternalInputs) : TypeIIEstimateStatement := by
  obtain ⟨thresholdLoss, hthresholdLoss, hmedium⟩ :=
    eventually_sum_finiteLargeValueR2_le_power_of_guthMaynard inputs
  obtain ⟨Cextreme, hCextreme, hextreme⟩ :=
    eventually_actual_extreme_regimes_le inputs
  refine ⟨thresholdLoss + 2, 1 / 1000, by positivity, by norm_num, ?_⟩
  intro eps heps hepsSmall B hB
  obtain ⟨kappa, hkappa, hmedium⟩ :=
    hmedium B hB eps heps hepsSmall
  let delta := mediumResidualSaving kappa
  have hdelta : 0 < delta := by
    exact mediumResidualSaving_pos hkappa
  let kappa₁ := min (delta / 4) (1 / 2)
  have hkappa₁ : 0 < kappa₁ := by
    dsimp [kappa₁]
    exact lt_min (by positivity) (by norm_num)
  refine ⟨kappa₁, hkappa₁, ?_⟩
  intro A₀ L hA₀ hL
  obtain ⟨Cmedium, Tmedium, hCmedium, hTmedium, hmediumEventually⟩ :=
    hmedium A₀ L hA₀ hL
  have hepsExtreme : eps ≤ 7 / 1144 := by
    norm_num at hepsSmall ⊢
    linarith
  obtain ⟨Dextreme, Q, hDextreme, hextremeEventually⟩ :=
    hextreme B eps L hB heps hepsExtreme hL A₀ hA₀
  let Dmedium : ℝ :=
    Real.exp 4 * ((mediumPowerOrderCap eps : ℝ) * Cmedium)
  have habsorbEventually :
      ∀ᶠ T : ℝ in atTop,
        Dmedium * T ^ (-(delta / 2)) ≤ T ^ (-(delta / 4)) :=
    eventually_const_mul_rpow_neg_half_le_quarter hdelta
  have hcombinedEventually :
      ∀ᶠ T : ℝ in atTop,
        (∀ (N₁ N₂ : ℕ) (a₁ a₂ : ℕ → ℂ) (R : Finset ℝ),
            1 ≤ N₁ → 1 ≤ N₂ →
            (Real.log T) ^ (-L) ≤ ((N₁ : ℝ) * (N₂ : ℝ)) / T →
            ((N₁ : ℝ) * (N₂ : ℝ)) / T ≤ (Real.log T) ^ L →
            T ^ (eps / 5) ≤ (N₁ : ℝ) →
            (N₁ : ℝ) ≤ T ^ (2 / 11 + eps) →
            IsDivisorBoundedByConstant B A₀ a₁ →
            IsDivisorBoundedByConstant B A₀ a₂ →
            (R : Set ℝ) ⊆ Set.Icc (0 : ℝ) T →
            IsOneSpaced (R : Set ℝ) →
            (∀ t ∈ R,
              (N₁ : ℝ) ^ (-(17 / 70 - (thresholdLoss + 2) * eps)) ≤
                  ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ)
                    (onePlusIT t)‖ ∨
                (N₂ : ℝ) ^ (-(17 / 70 - (thresholdLoss + 2) * eps)) ≤
                  ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ)
                    (onePlusIT t)‖) →
            ∀ S : ℝ, 0 ≤ S →
            (∀ t ∈ R,
              ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ)
                (onePlusIT t)‖ ^ 2 ≤ S) →
            (∑ t ∈ R,
                ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ)
                    (onePlusIT t)‖ ^ 2 *
                  ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ)
                    (onePlusIT t)‖ ^ 2) ≤
              8 * Cextreme * Dextreme *
                  (Real.log T) ^ (Q + 1) * S +
                3 * T ^ (-kappa₁)) := by
    filter_upwards [hmediumEventually, hextremeEventually,
      habsorbEventually, eventually_gt_atTop (1 : ℝ)] with
        T hmediumT hextremeT habsorbT hTone
    intro N₁ N₂ a₁ a₂ R hN₁ hN₂ hprodLower hprodUpper
      hN₁lower hN₁upper ha₁ ha₂ hR hspaced hlarge S hS hSbound
    have hmediumRaw := hmediumT N₁ N₂ a₁ a₂ R hN₁ hN₂
      hprodLower hprodUpper hN₁lower hN₁upper ha₁ ha₂ hR hspaced hlarge
    have hmediumBound :
        (∑ t ∈ finiteLargeValueR2 R
            (dyadicDirichletPolynomial a₁ (N₁ : ℝ))
            (dyadicDirichletPolynomial a₂ (N₂ : ℝ))
            (N₁ : ℝ) (N₂ : ℝ) T eps,
          ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ) (onePlusIT t)‖ ^ 2 *
          ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ) (onePlusIT t)‖ ^ 2) ≤
          T ^ (-(delta / 4)) := by
      apply hmediumRaw.trans
      simpa only [Dmedium, delta] using habsorbT
    have hextremeBound := hextremeT a₁ a₂ N₁ N₂ R S hN₁ hN₂
      hprodLower hprodUpper hN₁lower hN₁upper ha₁ ha₂
      (fun t ht ↦ hR ht) hspaced hS hSbound
    have hextremeBound' :
        (∑ t ∈ finiteLargeValueR1 R
            (dyadicDirichletPolynomial a₁ (N₁ : ℝ))
            (dyadicDirichletPolynomial a₂ (N₂ : ℝ))
            (N₁ : ℝ) (N₂ : ℝ) eps,
          ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ) (onePlusIT t)‖ ^ 2 *
          ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ) (onePlusIT t)‖ ^ 2) +
        (∑ t ∈ finiteLargeValueR3 R
            (dyadicDirichletPolynomial a₁ (N₁ : ℝ))
            (dyadicDirichletPolynomial a₂ (N₂ : ℝ))
            (N₁ : ℝ) (N₂ : ℝ) T eps,
          ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ) (onePlusIT t)‖ ^ 2 *
          ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ) (onePlusIT t)‖ ^ 2) ≤
          8 * Cextreme * Dextreme * (Real.log T) ^ (Q + 1) * S +
            2 * T ^ (-1 / 2 : ℝ) := by
      simpa only [norm_mul, mul_pow] using hextremeBound
    have hquarter : T ^ (-(delta / 4)) ≤ T ^ (-kappa₁) := by
      apply Real.rpow_le_rpow_of_exponent_le hTone.le
      exact neg_le_neg (min_le_left (delta / 4) (1 / 2))
    have hhalf : T ^ (-1 / 2 : ℝ) ≤ T ^ (-kappa₁) := by
      apply Real.rpow_le_rpow_of_exponent_le hTone.le
      dsimp [kappa₁]
      have hmin := min_le_right (delta / 4) (1 / 2)
      linarith
    have hpartition :=
      sum_finiteLargeValue_partition_le_of_extremes_combined R
        (dyadicDirichletPolynomial a₁ (N₁ : ℝ))
        (dyadicDirichletPolynomial a₂ (N₂ : ℝ))
        (N₁ : ℝ) (N₂ : ℝ) T eps
        (fun t ↦
          ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ) (onePlusIT t)‖ ^ 2 *
          ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ) (onePlusIT t)‖ ^ 2)
        hextremeBound' hmediumBound
    calc
      (∑ t ∈ R,
          ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ) (onePlusIT t)‖ ^ 2 *
          ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ) (onePlusIT t)‖ ^ 2) ≤
          (8 * Cextreme * Dextreme * (Real.log T) ^ (Q + 1) * S +
            2 * T ^ (-1 / 2 : ℝ)) + T ^ (-(delta / 4)) := hpartition
      _ ≤ 8 * Cextreme * Dextreme * (Real.log T) ^ (Q + 1) * S +
            3 * T ^ (-kappa₁) := by linarith
  obtain ⟨Tcut, hTcut⟩ := Filter.eventually_atTop.mp hcombinedEventually
  let C₂ : ℝ := ((Q + 1 : ℕ) : ℝ)
  let Cfinal : ℝ := 6 + 16 * Cextreme * Dextreme
  let T₀ : ℝ := max 1 Tcut
  have hC₂ : 0 < C₂ := by
    dsimp [C₂]
    positivity
  have hCfinal : 0 < Cfinal := by
    dsimp [Cfinal]
    positivity
  have hT₀ : 1 ≤ T₀ := by
    exact le_max_left 1 Tcut
  refine ⟨C₂, Cfinal, T₀, hC₂, hCfinal, hT₀, ?_⟩
  intro T N₁ N₂ a₁ a₂ U S hT hN₁ hN₂ hprodLower hprodUpper
    hN₁lower hN₁upper ha₁ ha₂ hUmeas hU hlarge hS hSbound
  have hTcutT : Tcut ≤ T := (le_max_right 1 Tcut).trans hT
  have hcombinedT := hTcut T hTcutT
  have hTone : 1 ≤ T := (le_max_left 1 Tcut).trans hT
  have hsum : ∀ R : Finset ℝ,
      (R : Set ℝ) ⊆ U → IsOneSpaced (R : Set ℝ) →
        (∑ t ∈ R,
          ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ) (onePlusIT t)‖ ^ 2 *
          ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ) (onePlusIT t)‖ ^ 2) ≤
          8 * Cextreme * Dextreme * (Real.log T) ^ (Q + 1) * S +
            3 * T ^ (-kappa₁) := by
    intro R hRU hspaced
    apply hcombinedT N₁ N₂ a₁ a₂ R hN₁ hN₂ hprodLower hprodUpper
      hN₁lower hN₁upper ha₁ ha₂
    · exact hRU.trans hU
    · exact hspaced
    · intro t ht
      exact hlarge t (hRU ht)
    · exact hS
    · intro t ht
      exact hSbound t (hRU ht)
  have hintegral :=
    integral_typeII_weight_le_two_mul_of_uniform_oneSpaced_sum_bound
      hUmeas hU (by positivity : 0 ≤ (N₁ : ℝ))
      (by positivity : 0 ≤ (N₂ : ℝ)) hsum
  have hp : 0 ≤ T ^ (-kappa₁) := Real.rpow_nonneg (by positivity) _
  have hlogTerm : 0 ≤ (Real.log T) ^ C₂ * S := by
    exact mul_nonneg (Real.rpow_nonneg (Real.log_nonneg hTone) _) hS
  have hpowRewrite :
      (Real.log T) ^ (Q + 1) = (Real.log T) ^ C₂ := by
    simp only [C₂, Real.rpow_natCast]
  have hCgeSix : 6 ≤ Cfinal := by
    dsimp [Cfinal]
    have hprod : 0 < Cextreme * Dextreme :=
      mul_pos hCextreme hDextreme
    nlinarith
  have hCgeExtreme : 16 * Cextreme * Dextreme ≤ Cfinal := by
    dsimp [Cfinal]
    linarith
  calc
    (∫ t in U,
        ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ) (onePlusIT t)‖ ^ 2 *
        ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ) (onePlusIT t)‖ ^ 2) ≤
        2 * (8 * Cextreme * Dextreme *
          (Real.log T) ^ (Q + 1) * S + 3 * T ^ (-kappa₁)) := hintegral
    _ = (16 * Cextreme * Dextreme) *
          ((Real.log T) ^ C₂ * S) + 6 * T ^ (-kappa₁) := by
      rw [hpowRewrite]
      ring
    _ ≤ Cfinal * ((Real.log T) ^ C₂ * S) +
          Cfinal * T ^ (-kappa₁) :=
      add_le_add
        (mul_le_mul_of_nonneg_right hCgeExtreme hlogTerm)
        (mul_le_mul_of_nonneg_right hCgeSix hp)
    _ = Cfinal * (T ^ (-kappa₁) + (Real.log T) ^ C₂ * S) := by ring

/-- Registry entry for the completed, fully quantified Type-II estimate. -/
def fullTypeIIEstimateModule : ProofModule :=
  { name := "TypeII.FullTypeIIEstimate"
    paperLocation := "Proposition 5.1"
    purpose :=
      "Combine the source-closed R₁, R₂, and R₃ finite estimates, absorb every fixed and logarithmic loss into a uniform power saving, and pass from all one-spaced sums to the Type-II integral."
    dependsOn := ["TypeII.MediumRegimeAssembly",
      "TypeII.ExtremeRegimeAssembly", "Hybrid.IntegralDiscretization"]
    status := .proved }

end
end TypeII
end ExactSemiprimes

