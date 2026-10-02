import ExactSemiprimes.Completion.ComponentAssembly

/-!
# Integral assembly of a finite component family

The decomposition is an identity of Dirichlet polynomials, while the target
is an integral of the squared norm.  Consequently the family-size loss is
quadratic after finite Cauchy--Schwarz.  This module proves that exact
inequality, includes the remainder term, and verifies that the source bound
`Cfamily * exp(y^5)` is still swallowed by a per-component
`exp(-2*y^6)` saving.
-/

namespace ExactSemiprimes
namespace Completion

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

/-- Finite Cauchy--Schwarz with one additional remainder term. -/
theorem norm_sum_add_sq_le_two_card_mul_sum_sq
    {ι : Type*} (components : Finset ι) (F : ι → ℂ) (r : ℂ) :
    ‖(∑ i ∈ components, F i) + r‖ ^ (2 : ℕ) ≤
      2 * ((components.card : ℝ) *
          (∑ i ∈ components, ‖F i‖ ^ (2 : ℕ)) +
        ‖r‖ ^ (2 : ℕ)) := by
  have hnorm :
      ‖(∑ i ∈ components, F i) + r‖ ≤
        (∑ i ∈ components, ‖F i‖) + ‖r‖ := by
    exact (norm_add_le _ _).trans
      (add_le_add (norm_sum_le components F) le_rfl)
  have hleftNonneg : 0 ≤ ‖(∑ i ∈ components, F i) + r‖ :=
    norm_nonneg _
  have hrightNonneg :
      0 ≤ (∑ i ∈ components, ‖F i‖) + ‖r‖ := by
    positivity
  have hsquare :
      ‖(∑ i ∈ components, F i) + r‖ ^ (2 : ℕ) ≤
        ((∑ i ∈ components, ‖F i‖) + ‖r‖) ^ (2 : ℕ) :=
    (sq_le_sq₀ hleftNonneg hrightNonneg).2 hnorm
  have hcauchy :
      (∑ i ∈ components, ‖F i‖) ^ (2 : ℕ) ≤
        (components.card : ℝ) *
          ∑ i ∈ components, ‖F i‖ ^ (2 : ℕ) :=
    sq_sum_le_card_mul_sum_sq
  calc
    ‖(∑ i ∈ components, F i) + r‖ ^ (2 : ℕ) ≤
        ((∑ i ∈ components, ‖F i‖) + ‖r‖) ^ (2 : ℕ) :=
      hsquare
    _ ≤ 2 * ((∑ i ∈ components, ‖F i‖) ^ (2 : ℕ) +
        ‖r‖ ^ (2 : ℕ)) := by
      nlinarith [sq_nonneg
        ((∑ i ∈ components, ‖F i‖) - ‖r‖)]
    _ ≤ 2 * ((components.card : ℝ) *
          (∑ i ∈ components, ‖F i‖ ^ (2 : ℕ)) +
        ‖r‖ ^ (2 : ℕ)) := by
      gcongr

/-- Integrated form of the exact finite-family inequality.  All regularity
hypotheses are explicit; for the application they follow from finite
Dirichlet polynomials. -/
theorem integral_norm_componentSum_add_remainder_sq_le
    {ι : Type*} (E : Set ℝ) (components : Finset ι)
    (F : ι → ℝ → ℂ) (r : ℝ → ℂ)
    (hE : MeasurableSet E)
    (hleft : IntegrableOn
      (fun t ↦ ‖(∑ i ∈ components, F i t) + r t‖ ^ (2 : ℕ)) E)
    (hcomponent : ∀ i ∈ components,
      IntegrableOn (fun t ↦ ‖F i t‖ ^ (2 : ℕ)) E)
    (hremainder : IntegrableOn (fun t ↦ ‖r t‖ ^ (2 : ℕ)) E) :
    (∫ t in E,
        ‖(∑ i ∈ components, F i t) + r t‖ ^ (2 : ℕ)) ≤
      2 * (components.card : ℝ) *
          (∑ i ∈ components,
            ∫ t in E, ‖F i t‖ ^ (2 : ℕ)) +
        2 * ∫ t in E, ‖r t‖ ^ (2 : ℕ) := by
  have hsum : IntegrableOn
      (fun t ↦ ∑ i ∈ components, ‖F i t‖ ^ (2 : ℕ)) E := by
    rw [IntegrableOn]
    exact (integrable_finsetSum' components hcomponent).congr
      (Filter.Eventually.of_forall fun t ↦ by simp)
  have hright : IntegrableOn
      (fun t ↦
        2 * ((components.card : ℝ) *
            (∑ i ∈ components, ‖F i t‖ ^ (2 : ℕ)) +
          ‖r t‖ ^ (2 : ℕ))) E :=
    ((hsum.const_mul (components.card : ℝ)).add hremainder).const_mul 2
  calc
    (∫ t in E,
        ‖(∑ i ∈ components, F i t) + r t‖ ^ (2 : ℕ)) ≤
        ∫ t in E,
          2 * ((components.card : ℝ) *
              (∑ i ∈ components, ‖F i t‖ ^ (2 : ℕ)) +
            ‖r t‖ ^ (2 : ℕ)) :=
      setIntegral_mono_on hleft hright hE fun t _ ↦
        norm_sum_add_sq_le_two_card_mul_sum_sq components
          (fun i ↦ F i t) (r t)
    _ = 2 * ∫ t in E,
          ((components.card : ℝ) *
              (∑ i ∈ components, ‖F i t‖ ^ (2 : ℕ)) +
            ‖r t‖ ^ (2 : ℕ)) := by
      rw [integral_const_mul]
    _ = 2 * ((∫ t in E,
          (components.card : ℝ) *
            (∑ i ∈ components, ‖F i t‖ ^ (2 : ℕ))) +
          ∫ t in E, ‖r t‖ ^ (2 : ℕ)) := by
      rw [integral_add (hsum.const_mul (components.card : ℝ))
        hremainder]
    _ = 2 * (components.card : ℝ) *
          (∑ i ∈ components,
            ∫ t in E, ‖F i t‖ ^ (2 : ℕ)) +
        2 * ∫ t in E, ‖r t‖ ^ (2 : ℕ) := by
      rw [integral_const_mul,
        integral_finsetSum components
          (fun i hi ↦ (hcomponent i hi).integrable)]
      ring

/-- If every component and the remainder have the same square-integral
majorant, the complete decomposition loses at most
`2 * (card^2 + 1)`. -/
theorem integral_componentFamily_le_cardSquared
    {ι : Type*} (E : Set ℝ) (components : Finset ι)
    (F : ι → ℝ → ℂ) (r : ℝ → ℂ) {V : ℝ}
    (hE : MeasurableSet E) (_hV : 0 ≤ V)
    (hleft : IntegrableOn
      (fun t ↦ ‖(∑ i ∈ components, F i t) + r t‖ ^ (2 : ℕ)) E)
    (hcomponent : ∀ i ∈ components,
      IntegrableOn (fun t ↦ ‖F i t‖ ^ (2 : ℕ)) E)
    (hremainder : IntegrableOn (fun t ↦ ‖r t‖ ^ (2 : ℕ)) E)
    (heach : ∀ i ∈ components,
      (∫ t in E, ‖F i t‖ ^ (2 : ℕ)) ≤ V)
    (hrem : (∫ t in E, ‖r t‖ ^ (2 : ℕ)) ≤ V) :
    (∫ t in E,
        ‖(∑ i ∈ components, F i t) + r t‖ ^ (2 : ℕ)) ≤
      2 * ((components.card : ℝ) ^ (2 : ℕ) + 1) * V := by
  have hmain := integral_norm_componentSum_add_remainder_sq_le
    E components F r hE hleft hcomponent hremainder
  calc
    _ ≤ 2 * (components.card : ℝ) *
          (∑ i ∈ components,
            ∫ t in E, ‖F i t‖ ^ (2 : ℕ)) +
        2 * ∫ t in E, ‖r t‖ ^ (2 : ℕ) := hmain
    _ ≤ 2 * (components.card : ℝ) *
          (∑ _i ∈ components, V) + 2 * V := by
      gcongr with i hi
      exact heach i hi
    _ = 2 * ((components.card : ℝ) ^ (2 : ℕ) + 1) * V := by
      simp [pow_two]
      ring

/-- The exact quadratic family loss is eventually absorbed by the same
per-component saving used in the component estimates. -/
theorem eventually_squared_component_loss_with_constant_absorbed
    {Cfamily : ℝ} (hCfamily : 0 < Cfamily) :
    ∀ᶠ y : ℝ in atTop,
      2 * ((Cfamily * Real.exp (y ^ (5 : ℕ))) ^ (2 : ℕ) + 1) *
          Real.exp (-2 * y ^ (6 : ℕ)) ≤
        Real.exp (-y ^ (6 : ℕ)) := by
  let K : ℝ := 2 * (Cfamily ^ (2 : ℕ) + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  filter_upwards [eventually_ge_atTop
    (max 4 (2 * Real.log K))] with y hy
  have hyFour : 4 ≤ y := (le_max_left _ _).trans hy
  have hlogK : 2 * Real.log K ≤ y :=
    (le_max_right _ _).trans hy
  have hyNonneg : 0 ≤ y := by linarith
  have hyFiveNonneg : 0 ≤ y ^ (5 : ℕ) := pow_nonneg hyNonneg 5
  have htwoFive : 2 * y ^ (5 : ℕ) ≤ y ^ (6 : ℕ) / 2 := by
    have hfourFive : 4 * y ^ (5 : ℕ) ≤ y * y ^ (5 : ℕ) :=
      mul_le_mul_of_nonneg_right hyFour hyFiveNonneg
    have hySix : y * y ^ (5 : ℕ) = y ^ (6 : ℕ) := by ring
    rw [hySix] at hfourFive
    linarith
  have honeFive : 1 ≤ y ^ (5 : ℕ) :=
    one_le_pow₀ (by linarith : 1 ≤ y)
  have hySixLower : y ≤ y ^ (6 : ℕ) := by
    calc
      y = y * 1 := by ring
      _ ≤ y * y ^ (5 : ℕ) :=
        mul_le_mul_of_nonneg_left honeFive hyNonneg
      _ = y ^ (6 : ℕ) := by ring
  have hlogHalf : Real.log K ≤ y ^ (6 : ℕ) / 2 := by
    linarith
  have hexponent :
      Real.log K + 2 * y ^ (5 : ℕ) ≤ y ^ (6 : ℕ) := by
    linarith
  have hexpOne : 1 ≤ Real.exp (2 * y ^ (5 : ℕ)) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  have hinside :
      2 * ((Cfamily * Real.exp (y ^ (5 : ℕ))) ^ (2 : ℕ) + 1) ≤
        K * Real.exp (2 * y ^ (5 : ℕ)) := by
    have hsqexp :
        (Real.exp (y ^ (5 : ℕ))) ^ (2 : ℕ) =
          Real.exp (2 * y ^ (5 : ℕ)) := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [mul_pow, hsqexp]
    dsimp [K]
    nlinarith [sq_nonneg Cfamily]
  calc
    2 * ((Cfamily * Real.exp (y ^ (5 : ℕ))) ^ (2 : ℕ) + 1) *
          Real.exp (-2 * y ^ (6 : ℕ)) ≤
        (K * Real.exp (2 * y ^ (5 : ℕ))) *
          Real.exp (-2 * y ^ (6 : ℕ)) :=
      mul_le_mul_of_nonneg_right hinside (Real.exp_pos _).le
    _ = (Real.exp (Real.log K) *
          Real.exp (2 * y ^ (5 : ℕ))) *
          Real.exp (-2 * y ^ (6 : ℕ)) := by
      rw [Real.exp_log hK]
    _ = Real.exp
          (Real.log K + 2 * y ^ (5 : ℕ) - 2 * y ^ (6 : ℕ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-y ^ (6 : ℕ)) := by
      apply Real.exp_le_exp.mpr
      linarith

/-- Fully assembled eventual scalar bound with the source family-count
constant and the correct quadratic Cauchy--Schwarz loss. -/
theorem eventually_componentFamily_integral_saving_with_constant
    {Cfamily : ℝ} (hCfamily : 0 < Cfamily) :
    ∀ᶠ X : ℝ in atTop,
      ∀ {cardinality value : ℝ},
        0 ≤ cardinality →
        0 ≤ value →
        cardinality ≤ Cfamily *
          Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ)) →
        value ≤
          2 * (cardinality ^ (2 : ℕ) + 1) *
            Real.exp (-2 * (Real.log (Real.log X)) ^ (6 : ℕ)) →
        value ≤
          Real.exp (-(Real.log (Real.log X)) ^ (6 : ℕ)) := by
  have hloglog :
      Tendsto (fun X : ℝ ↦ Real.log (Real.log X)) atTop atTop := by
    simpa [Function.comp_def] using
      Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have habsorb := hloglog.eventually
    (eventually_squared_component_loss_with_constant_absorbed hCfamily)
  filter_upwards [habsorb] with X hX
  intro cardinality value hcardNonneg _hvalue hcard hbound
  have hcardSq := pow_le_pow_left₀ hcardNonneg hcard 2
  have hfactor :
      2 * (cardinality ^ (2 : ℕ) + 1) ≤
        2 * ((Cfamily *
          Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ))) ^ (2 : ℕ) + 1) := by
    nlinarith
  exact hbound.trans <| (mul_le_mul_of_nonneg_right hfactor
    (Real.exp_pos _).le).trans hX

def componentIntegralAssemblyModule : ProofModule :=
  { name := "Completion.ComponentIntegralAssembly"
    paperLocation := "Proof of Proposition 7.1, squared component-family assembly"
    purpose :=
      "Pass from the exact global component identity to the squared-norm integral, include the remainder, account for the quadratic family-size loss, and absorb it into the exponential component saving."
    dependsOn :=
      ["Completion.ComponentAssembly",
        "Sparse.GlobalComponentCancellation"]
    status := .proved }

end
end Completion
end ExactSemiprimes
