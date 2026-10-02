import ExactSemiprimes.Completion.ComplementOfU
import ExactSemiprimes.Completion.TypeIClosure
import ExactSemiprimes.Completion.TypeIOverIIClosure
import ExactSemiprimes.Completion.TypeIIClosure
import ExactSemiprimes.Sparse.GlobalComponentCancellation

/-! # Assembly of the sieve-convolution components -/

namespace ExactSemiprimes
namespace Completion

open Filter
open scoped BigOperators

noncomputable section

/-- Summing a finite family of component upper bounds costs at most the
number of components. -/
theorem sum_components_le_card_mul
    {ι : Type*} (components : Finset ι) (value : ι → ℝ)
    {V : ℝ} (hvalue : ∀ i ∈ components, value i ≤ V) :
    ∑ i ∈ components, value i ≤ (components.card : ℝ) * V := by
  calc
    ∑ i ∈ components, value i ≤ ∑ _i ∈ components, V :=
      Finset.sum_le_sum hvalue
    _ = (components.card : ℝ) * V := by simp

/-- The paper's component count `exp((log log X)^5)` is swallowed by a
per-component saving `exp(-2(log log X)^6)` once `log log X≥1`. -/
theorem exponential_component_loss_absorbed
    {y : ℝ} (hy : 1 ≤ y) :
    Real.exp (y ^ (5 : ℕ)) * Real.exp (-2 * y ^ (6 : ℕ)) ≤
      Real.exp (-y ^ (6 : ℕ)) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hyNonneg : 0 ≤ y := zero_le_one.trans hy
  have hpowers : y ^ (5 : ℕ) ≤ y ^ (6 : ℕ) := by
    calc
      y ^ (5 : ℕ) = y ^ (5 : ℕ) * 1 := by ring
      _ ≤ y ^ (5 : ℕ) * y :=
        mul_le_mul_of_nonneg_left hy (pow_nonneg hyNonneg 5)
      _ = y ^ (6 : ℕ) := by ring
  linarith

/-- Exact finite assembly corresponding to the passage from the structured
convolution decomposition to `(component-target)`. -/
theorem component_family_total_saving
    {ι : Type*} (components : Finset ι) (value : ι → ℝ)
    {y : ℝ} (hy : 1 ≤ y)
    (hcard : (components.card : ℝ) ≤ Real.exp (y ^ (5 : ℕ)))
    (hvalue : ∀ i ∈ components,
      value i ≤ Real.exp (-2 * y ^ (6 : ℕ))) :
    ∑ i ∈ components, value i ≤ Real.exp (-y ^ (6 : ℕ)) := by
  have hVnonneg : 0 ≤ Real.exp (-2 * y ^ (6 : ℕ)) :=
    (Real.exp_pos _).le
  calc
    ∑ i ∈ components, value i ≤
        (components.card : ℝ) * Real.exp (-2 * y ^ (6 : ℕ)) :=
      sum_components_le_card_mul components value hvalue
    _ ≤ Real.exp (y ^ (5 : ℕ)) *
        Real.exp (-2 * y ^ (6 : ℕ)) :=
      mul_le_mul_of_nonneg_right hcard hVnonneg
    _ ≤ Real.exp (-y ^ (6 : ℕ)) :=
      exponential_component_loss_absorbed hy

/-!
## Absorbing the constant in the exact MT23 family bound

Proposition 2.2 supplies `Cfamily * exp((log log X)^5)`, rather than the
unit-constant bound used in the preceding convenient special case.  Since
`Cfamily` is chosen before `X`, it is fixed as `X → ∞`.  The next lemmas
make the resulting absorption completely explicit.
-/

/-- A fixed positive family constant is absorbed while retaining exactly
the same `-2 y⁶` per-component saving and `-y⁶` total saving.  The two
elementary size hypotheses say respectively that `y⁵ ≤ y⁶/2` and
`log Cfamily ≤ y⁶/2`. -/
theorem exponential_component_loss_with_constant_absorbed
    {Cfamily y : ℝ} (hCfamily : 0 < Cfamily) (hy : 2 ≤ y)
    (hlogCfamily : 2 * Real.log Cfamily ≤ y ^ (6 : ℕ)) :
    Cfamily * Real.exp (y ^ (5 : ℕ)) *
        Real.exp (-2 * y ^ (6 : ℕ)) ≤
      Real.exp (-y ^ (6 : ℕ)) := by
  have hyNonneg : 0 ≤ y := by linarith
  have hyFiveNonneg : 0 ≤ y ^ (5 : ℕ) := pow_nonneg hyNonneg 5
  have hyFive : 2 * y ^ (5 : ℕ) ≤ y ^ (6 : ℕ) := by
    calc
      2 * y ^ (5 : ℕ) ≤ y * y ^ (5 : ℕ) :=
        mul_le_mul_of_nonneg_right hy hyFiveNonneg
      _ = y ^ (6 : ℕ) := by ring
  have hexponent :
      Real.log Cfamily + y ^ (5 : ℕ) ≤ y ^ (6 : ℕ) := by
    linarith
  calc
    Cfamily * Real.exp (y ^ (5 : ℕ)) *
          Real.exp (-2 * y ^ (6 : ℕ)) =
        (Real.exp (Real.log Cfamily) * Real.exp (y ^ (5 : ℕ))) *
          Real.exp (-2 * y ^ (6 : ℕ)) := by
      rw [Real.exp_log hCfamily]
    _ =
        Real.exp (Real.log Cfamily + y ^ (5 : ℕ) -
          2 * y ^ (6 : ℕ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-y ^ (6 : ℕ)) := by
      apply Real.exp_le_exp.mpr
      linarith

/-- Exact finite-family theorem with the cardinality hypothesis delivered
by the fully quantified version of MT23, Proposition 2.2. -/
theorem component_family_total_saving_with_constant
    { ι : Type* } (components : Finset ι) (value : ι → ℝ)
    {Cfamily y : ℝ} (hCfamily : 0 < Cfamily) (hy : 2 ≤ y)
    (hlogCfamily : 2 * Real.log Cfamily ≤ y ^ (6 : ℕ))
    (hcard : (components.card : ℝ) ≤
      Cfamily * Real.exp (y ^ (5 : ℕ)))
    (hvalue : ∀ i ∈ components,
      value i ≤ Real.exp (-2 * y ^ (6 : ℕ))) :
    ∑ i ∈ components, value i ≤ Real.exp (-y ^ (6 : ℕ)) := by
  have hVnonneg : 0 ≤ Real.exp (-2 * y ^ (6 : ℕ)) :=
    (Real.exp_pos _).le
  calc
    ∑ i ∈ components, value i ≤
        (components.card : ℝ) * Real.exp (-2 * y ^ (6 : ℕ)) :=
      sum_components_le_card_mul components value hvalue
    _ ≤ (Cfamily * Real.exp (y ^ (5 : ℕ))) *
        Real.exp (-2 * y ^ (6 : ℕ)) :=
      mul_le_mul_of_nonneg_right hcard hVnonneg
    _ ≤ Real.exp (-y ^ (6 : ℕ)) :=
      exponential_component_loss_with_constant_absorbed
        hCfamily hy hlogCfamily

/-- For every fixed positive `Cfamily`, the two explicit hypotheses in
`exponential_component_loss_with_constant_absorbed` eventually hold. -/
theorem eventually_exponential_component_loss_with_constant_absorbed
    {Cfamily : ℝ} (hCfamily : 0 < Cfamily) :
    ∀ᶠ y : ℝ in atTop,
      Cfamily * Real.exp (y ^ (5 : ℕ)) *
          Real.exp (-2 * y ^ (6 : ℕ)) ≤
        Real.exp (-y ^ (6 : ℕ)) := by
  filter_upwards [eventually_ge_atTop
    (max 2 (2 * Real.log Cfamily))] with y hy
  have hyTwo : 2 ≤ y := (le_max_left _ _).trans hy
  have hlogCy : 2 * Real.log Cfamily ≤ y :=
    (le_max_right _ _).trans hy
  have hyNonneg : 0 ≤ y := by linarith
  have hone : 1 ≤ y ^ (5 : ℕ) := one_le_pow₀ (by linarith : 1 ≤ y)
  have hy_le_six : y ≤ y ^ (6 : ℕ) := by
    calc
      y = y * 1 := by ring
      _ ≤ y * y ^ (5 : ℕ) :=
        mul_le_mul_of_nonneg_left hone hyNonneg
      _ = y ^ (6 : ℕ) := by ring
  exact exponential_component_loss_with_constant_absorbed hCfamily hyTwo
    (hlogCy.trans hy_le_six)

/-- The exact MT23 component-count loss is therefore absorbed at the paper's
scale `y = log log X` for all sufficiently large `X`. -/
theorem eventually_loglog_component_loss_with_constant_absorbed
    {Cfamily : ℝ} (hCfamily : 0 < Cfamily) :
    ∀ᶠ X : ℝ in atTop,
      Cfamily *
          Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ)) *
          Real.exp (-2 * (Real.log (Real.log X)) ^ (6 : ℕ)) ≤
        Real.exp (-(Real.log (Real.log X)) ^ (6 : ℕ)) := by
  have hloglog :
      Tendsto (fun X : ℝ ↦ Real.log (Real.log X)) atTop atTop := by
    simpa [Function.comp_def] using
      Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  exact hloglog.eventually
    (eventually_exponential_component_loss_with_constant_absorbed hCfamily)

/-- Uniform eventual assembly for any component family and component values
satisfying the exact MT23 cardinality bound and the required per-component
saving.  The type of components and the constant are fixed outside the
`X`-limit, matching the quantifier order of Proposition 2.2. -/
theorem eventually_component_family_total_saving_with_constant
    {ι : Type*} {Cfamily : ℝ} (hCfamily : 0 < Cfamily) :
    ∀ᶠ X : ℝ in atTop, ∀ (components : Finset ι) (value : ι → ℝ),
      (components.card : ℝ) ≤ Cfamily *
          Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ)) →
      (∀ i ∈ components,
        value i ≤ Real.exp
          (-2 * (Real.log (Real.log X)) ^ (6 : ℕ))) →
      ∑ i ∈ components, value i ≤
        Real.exp (-(Real.log (Real.log X)) ^ (6 : ℕ)) := by
  filter_upwards
      [eventually_loglog_component_loss_with_constant_absorbed hCfamily]
      with X hX
  intro components value hcard hvalue
  have hVnonneg :
      0 ≤ Real.exp (-2 * (Real.log (Real.log X)) ^ (6 : ℕ)) :=
    (Real.exp_pos _).le
  calc
    ∑ i ∈ components, value i ≤
        (components.card : ℝ) *
          Real.exp (-2 * (Real.log (Real.log X)) ^ (6 : ℕ)) :=
      sum_components_le_card_mul components value hvalue
    _ ≤ (Cfamily *
          Real.exp ((Real.log (Real.log X)) ^ (5 : ℕ))) *
          Real.exp (-2 * (Real.log (Real.log X)) ^ (6 : ℕ)) :=
      mul_le_mul_of_nonneg_right hcard hVnonneg
    _ ≤ Real.exp (-(Real.log (Real.log X)) ^ (6 : ℕ)) := hX

def componentAssemblyModule : ProofModule :=
  { name := "Completion.ComponentAssembly"
    paperLocation := "Proof of Proposition 7.1, component target and summation"
    purpose :=
      "Prove that the exact Cfamily*exp((log log X)^5) component count is eventually absorbed by the per-component saving. The assembly used by the main theorem is Final/DirichletTarget.lean."
    dependsOn :=
      [ "Completion.ComplementOfU",
        "Completion.TypeIClosure",
        "Completion.TypeIOverIIClosure",
        "Completion.TypeIIClosure",
        "Assumptions.matomakiTeravainenPropositionTwoTwo" ]
    status := .superseded }

end

end Completion
end ExactSemiprimes
