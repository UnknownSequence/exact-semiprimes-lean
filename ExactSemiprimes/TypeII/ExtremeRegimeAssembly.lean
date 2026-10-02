import ExactSemiprimes.TypeII.TypeIIEstimate

/-!
# Final discrete wrapper for the two extreme Type-II regimes

This module combines the source-closed weighted `R₁` theorem
with the source-closed `R₃` theorem on the actual deterministic finite
sets used by `TypeIIEstimate`.  It deliberately says nothing about `R₂`.
-/

namespace ExactSemiprimes
namespace TypeII

open Filter
open scoped BigOperators

noncomputable section

/-- Under the outer Type-II length hypotheses, the actual finite `R₁` and
`R₃` contributions satisfy the sum of the proved polylogarithmic and
power-saving bounds.  All constants and exponents are displayed.

The order cap is `mediumPowerOrderCap eps = ceil(5/eps)` and is produced
from the length geometry, rather than being assumed at the call site. -/
theorem eventually_actual_extreme_regimes_le
    (inputs : ExternalInputs) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B eps L : ℝ),
        0 ≤ B → 0 < eps → eps ≤ 7 / 1144 → 0 ≤ L →
        ∀ A₀ : ℝ, 1 ≤ A₀ →
          ∃ (D : ℝ) (Q : ℕ), 0 < D ∧
            ∀ᶠ T : ℝ in atTop,
              ∀ (a₁ a₂ : ℕ → ℂ) (N₁ N₂ : ℕ) (R : Finset ℝ)
                  (S : ℝ),
                1 ≤ N₁ → 1 ≤ N₂ →
                (Real.log T) ^ (-L) ≤
                  ((N₁ : ℝ) * (N₂ : ℝ)) / T →
                ((N₁ : ℝ) * (N₂ : ℝ)) / T ≤
                  (Real.log T) ^ L →
                T ^ (eps / 5) ≤ (N₁ : ℝ) →
                (N₁ : ℝ) ≤ T ^ (2 / 11 + eps) →
                IsDivisorBoundedByConstant B A₀ a₁ →
                IsDivisorBoundedByConstant B A₀ a₂ →
                (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
                IsOneSpaced (↑R : Set ℝ) →
                0 ≤ S →
                (∀ t ∈ R,
                  ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ) (onePlusIT t)‖ ^
                    (2 : ℕ) ≤ S) →
                (∑ t ∈
                    finiteLargeValueR1 R
                      (dyadicDirichletPolynomial a₁ (N₁ : ℝ))
                      (dyadicDirichletPolynomial a₂ (N₂ : ℝ))
                      (N₁ : ℝ) (N₂ : ℝ) eps,
                    ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ) (onePlusIT t) *
                      dyadicDirichletPolynomial a₂ (N₂ : ℝ) (onePlusIT t)‖ ^
                        (2 : ℕ)) +
                  (∑ t ∈
                    finiteLargeValueR3 R
                      (dyadicDirichletPolynomial a₁ (N₁ : ℝ))
                      (dyadicDirichletPolynomial a₂ (N₂ : ℝ))
                      (N₁ : ℝ) (N₂ : ℝ) T eps,
                    ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ) (onePlusIT t) *
                      dyadicDirichletPolynomial a₂ (N₂ : ℝ) (onePlusIT t)‖ ^
                        (2 : ℕ)) ≤
                  8 * C * D * (Real.log T) ^ (Q + 1) * S +
                    2 * T ^ (-1 / 2 : ℝ) := by
  obtain ⟨C, hC, hlarge⟩ :=
    eventually_weighted_extremePairPoints_le_polylog inputs
  refine ⟨C, hC, ?_⟩
  intro B eps L hB heps hepsSmall hL A₀ hA₀
  let K := mediumPowerOrderCap eps
  have hK : 1 ≤ K := by
    dsimp [K, mediumPowerOrderCap]
    rw [Nat.one_le_iff_ne_zero]
    exact (Nat.ceil_pos.mpr (by positivity : 0 < 5 / eps)).ne'
  obtain ⟨D, Q, hD, hlargeEventually⟩ :=
    hlarge B eps K hB heps hepsSmall hK A₀ hA₀
  refine ⟨D, Q, hD, ?_⟩
  have hsmallEventually :=
    eventually_sum_smallExtremeRange_divisorBounded
      (zero_lt_one.trans_le hA₀) hB
  have hproductEventually :=
    eventually_product_power_bounds L
      (show 0 < eps / 30 by positivity)
  filter_upwards [hlargeEventually, hsmallEventually, hproductEventually,
    eventually_gt_atTop (2 : ℝ)] with
      T hlargeT hsmallT hproductT hTtwo
  intro a₁ a₂ N₁ N₂ R S hN₁ hN₂ hprodLower hprodUpper
    hN₁lower hN₁upper ha₁ ha₂ hR hspaced hS hSbound
  have hTone : 1 < T := one_lt_two.trans hTtwo
  have hTpos : 0 < T := zero_lt_one.trans hTone
  have hN₁pos : 0 < (N₁ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN₁)
  have hN₂pos : 0 < (N₂ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN₂)
  have hproduct := hproductT (N₁ : ℝ) (N₂ : ℝ) hN₁pos
    hprodLower hprodUpper
  have hcomplement := complementaryLengthBounds hTone.le heps.le hN₁pos
    hproduct.1 hproduct.2 hN₁lower hN₁upper
  have hepsTenth : eps ≤ 1 / 10 := by
    norm_num at hepsSmall ⊢
    linarith
  have hN₁gt : 1 < (N₁ : ℝ) := by
    have hpow : 1 < T ^ (eps / 5) := by
      simpa only [Real.rpow_zero] using
        Real.rpow_lt_rpow_of_exponent_lt hTone (by positivity : 0 < eps / 5)
    exact hpow.trans_le hN₁lower
  have hN₂gt : 1 < (N₂ : ℝ) := by
    have hexp : 0 < 9 / 11 - 2 * eps := by
      norm_num at hepsSmall ⊢
      linarith
    have hpow : 1 < T ^ (9 / 11 - 2 * eps) := by
      simpa only [Real.rpow_zero] using
        Real.rpow_lt_rpow_of_exponent_lt hTone hexp
    exact hpow.trans_le hcomplement.1
  have hN₁T : (N₁ : ℝ) ≤ T := by
    calc
      (N₁ : ℝ) ≤ T ^ (2 / 11 + eps) := hN₁upper
      _ ≤ T ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hTone.le
        norm_num at hepsSmall ⊢
        linarith
      _ = T := Real.rpow_one T
  have hN₂T : (N₂ : ℝ) ≤ T := by
    calc
      (N₂ : ℝ) ≤ T ^ (1 - eps / 6) := hcomplement.2
      _ ≤ T ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hTone.le (by linarith)
      _ = T := Real.rpow_one T
  have hdata₁ := firstFactor_extremePower_data hTone heps hepsTenth
    hN₁lower hN₁upper
  have hdata₂ := secondFactor_extremePower_data hTone heps hepsTenth
    hcomplement.1 hcomplement.2
  have hell₁ : extremePowerExponent T (N₁ : ℝ) ≤ K := by
    simpa [K, mediumPowerOrderCap] using hdata₁.2.1
  have hell₂ : extremePowerExponent T (N₂ : ℝ) ≤ K := by
    simpa [K, mediumPowerOrderCap] using hdata₂.2.1
  have hR₁ :
      (∑ t ∈
          finiteLargeValueR1 R
            (dyadicDirichletPolynomial a₁ (N₁ : ℝ))
            (dyadicDirichletPolynomial a₂ (N₂ : ℝ))
            (N₁ : ℝ) (N₂ : ℝ) eps,
          ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ) (onePlusIT t) *
            dyadicDirichletPolynomial a₂ (N₂ : ℝ) (onePlusIT t)‖ ^
              (2 : ℕ)) ≤
        8 * C * D * (Real.log T) ^ (Q + 1) * S := by
    rw [finiteLargeValueR1_dyadic_eq_extremePairPoints]
    exact hlargeT a₁ a₂ (N₁ : ℝ) (N₂ : ℝ) R S
      hN₁gt hN₁T hN₂gt hN₂T hcomplement.1 hell₁ hell₂
      ha₁ ha₂ hR hspaced hS hSbound
  let R₃ := finiteLargeValueR3 R
    (dyadicDirichletPolynomial a₁ (N₁ : ℝ))
    (dyadicDirichletPolynomial a₂ (N₂ : ℝ))
    (N₁ : ℝ) (N₂ : ℝ) T eps
  have hR₃subset : (↑R₃ : Set ℝ) ⊆ (↑R : Set ℝ) := by
    intro t ht
    exact (mem_finiteLargeValueR3_iff.mp ht).1
  have hR₃small : ∀ t ∈ R₃,
      ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ) (onePlusIT t)‖ ≤ T⁻¹ ∨
      ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ) (onePlusIT t)‖ ≤ T⁻¹ := by
    intro t ht
    have htSet := (mem_finiteLargeValueR3_iff.mp ht).2
    have htTiny := (mem_largeValueR3_iff.mp htSet).2.2
    rcases htTiny with htTiny | htTiny
    · exact Or.inl (by simpa [typeIIMagnitude] using htTiny.le)
    · exact Or.inr (by simpa [typeIIMagnitude] using htTiny.le)
  have hR₃ :
      (∑ t ∈ R₃,
          ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ) (onePlusIT t) *
            dyadicDirichletPolynomial a₂ (N₂ : ℝ) (onePlusIT t)‖ ^
              (2 : ℕ)) ≤ 2 * T ^ (-1 / 2 : ℝ) := by
    exact hsmallT.2 a₁ a₂ (N₁ : ℝ) (N₂ : ℝ) R₃
      ha₁ ha₂ (by exact_mod_cast hN₁) hN₁T
      (by exact_mod_cast hN₂) hN₂T
      (fun t ht ↦ hR t (hR₃subset ht))
      (Set.Pairwise.mono hR₃subset hspaced) hR₃small
  change _ + (∑ t ∈ R₃, _) ≤ _
  exact add_le_add hR₁ hR₃

/-- Metadata for the actual finite extreme-regime assembly. -/
def extremeRegimeAssemblyModule : ProofModule :=
  { name := "TypeII.ExtremeRegimeAssembly"
    paperLocation :=
      "Proof of Proposition 5.1, final discrete R₁ and R₃ insertion"
    purpose :=
      "Derive the bounded extreme powering orders and complementary length range from the outer hypotheses, identify the actual deterministic R₁ set, and combine the source-closed weighted R₁ and tiny R₃ bounds."
    dependsOn := ["TypeII.TypeIIEstimate", "TypeII.WeightedExtremeRange", "TypeII.ExtremeSmallAssembly", "TypeII.OuterLengthGeometry"]
    status := .proved }

end

end TypeII
end ExactSemiprimes

