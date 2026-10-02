import ExactSemiprimes.Completion.ComplementOfU

/-!
# Consequences of a cumulative Perron mean-square bound

The Dirichlet-polynomial target is stated for the cumulative integral from
`T₀ = X^(1/1000)` to every upper height.  A Parseval reduction uses both the
integral up to `X / h` and dyadic tail integrals over `[T,2T]`.  This file
proves the passage between those normalizations.  It is elementary and uses
no external analytic input.
-/

namespace ExactSemiprimes
namespace Completion

open MeasureTheory

noncomputable section

/-- The Perron-product energy is continuous, hence integrable on every
compact interval. -/
theorem continuous_perronProduct_energy
    (weight : ℕ → ℝ) (X P : ℝ) :
    Continuous (fun t : ℝ ↦ ‖perronProduct weight X P t‖ ^ (2 : ℕ)) := by
  have hprime := continuous_primeDirichletPolynomial_onePlusIT_completion P
  have hminor :=
    continuous_perronMinorantPolynomial_onePlusIT_completion weight X P
  exact (hprime.mul hminor).norm.pow 2

/-- A dyadic tail is bounded by the cumulative Perron integral ending at
`2T`, provided the common lower cutoff lies below `T`. -/
theorem perron_dyadicIntegral_le_cumulative
    (weight : ℕ → ℝ) {X P T₀ T : ℝ} (hcutoff : T₀ ≤ T) :
    (∫ t in Set.Ioc T (2 * T), ‖perronProduct weight X P t‖ ^ (2 : ℕ)) ≤
      ∫ t in Set.Ioc T₀ (2 * T),
        ‖perronProduct weight X P t‖ ^ (2 : ℕ) := by
  have hsubset : Set.Ioc T (2 * T) ⊆ Set.Ioc T₀ (2 * T) := by
    intro t ht
    exact ⟨hcutoff.trans_lt ht.1, ht.2⟩
  have hintegrable : IntegrableOn
      (fun t : ℝ ↦ ‖perronProduct weight X P t‖ ^ (2 : ℕ))
      (Set.Ioc T₀ (2 * T)) :=
    (continuous_perronProduct_energy weight X P).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  exact setIntegral_mono_set hintegrable
    (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
    (Filter.Eventually.of_forall hsubset)

/-- The cumulative target at `X/h` has no residual height factor: its ratio
to the base height is exactly one. -/
theorem perron_middleIntegral_le_of_cumulative
    (weight : ℕ → ℝ) {X P h C L : ℝ}
    (hX : 0 < X) (hh : 0 < h)
    (hcumulative : ∀ U : ℝ, X / h ≤ U →
      perronProductIntegral weight X P U ≤
        C * (U / (X / h)) / L) :
    perronProductIntegral weight X P (X / h) ≤ C / L := by
  have hbase : X / h ≠ 0 := div_ne_zero hX.ne' hh.ne'
  simpa [hbase] using hcumulative (X / h) le_rfl

/-- A cumulative target with linear growth in the upper height gives the
uniform dyadic-tail term required by Parseval.  The factor `2` is the exact
cost of evaluating the cumulative estimate at `2T`. -/
theorem perron_normalizedDyadicTail_le_of_cumulative
    (weight : ℕ → ℝ) {X P h T₀ T C L : ℝ}
    (hX : 0 < X) (hh : 0 < h) (hT : X / h ≤ T)
    (hcutoff : T₀ ≤ X / h) (hL : 0 < L)
    (hcumulative : ∀ U : ℝ, X / h ≤ U →
      (∫ t in Set.Ioc T₀ U,
        ‖perronProduct weight X P t‖ ^ (2 : ℕ)) ≤
          C * (U / (X / h)) / L) :
    X / (T * h) *
        (∫ t in Set.Ioc T (2 * T),
          ‖perronProduct weight X P t‖ ^ (2 : ℕ)) ≤
      2 * C / L := by
  have hbase : 0 < X / h := div_pos hX hh
  have hTpos : 0 < T := hbase.trans_le hT
  have htwoT : X / h ≤ 2 * T := by linarith
  have htail :
      (∫ t in Set.Ioc T (2 * T),
          ‖perronProduct weight X P t‖ ^ (2 : ℕ)) ≤
        C * ((2 * T) / (X / h)) / L := by
    calc
      (∫ t in Set.Ioc T (2 * T),
          ‖perronProduct weight X P t‖ ^ (2 : ℕ)) ≤
          ∫ t in Set.Ioc T₀ (2 * T),
            ‖perronProduct weight X P t‖ ^ (2 : ℕ) :=
        perron_dyadicIntegral_le_cumulative weight (hcutoff.trans hT)
      _ ≤ C * ((2 * T) / (X / h)) / L :=
        hcumulative (2 * T) htwoT
  have hfactor : 0 ≤ X / (T * h) := by positivity
  calc
    X / (T * h) *
          (∫ t in Set.Ioc T (2 * T),
            ‖perronProduct weight X P t‖ ^ (2 : ℕ)) ≤
        X / (T * h) * (C * ((2 * T) / (X / h)) / L) :=
      mul_le_mul_of_nonneg_left htail hfactor
    _ = 2 * C / L := by
      field_simp [hX.ne', hh.ne', hTpos.ne', hL.ne']

def perronCumulativeBoundsModule : ProofModule :=
  { name := "Completion.PerronCumulativeBounds"
    paperLocation :=
      "Teräväinen 2016, Lemma 1: conversion of cumulative mean squares to its middle and dyadic-tail terms"
    purpose :=
      "Derive the exact middle-height and normalized dyadic-tail estimates from the fully cumulative Perron target."
    dependsOn := ["Completion.PerronTarget"]
    status := .proved }

end

end Completion
end ExactSemiprimes
