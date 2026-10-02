import ExactSemiprimes.TypeII.PoweredMeanValue
import ExactSemiprimes.Sparse.GlobalComponentCancellation

/-!
# The Type-I first-factor fourth moment

This file applies the standard mean-value theorem in exactly the form
recorded as MT23, Lemma 3.2.  Squaring a dyadic polynomial on the line
`Re(s)=1` and using the collected coefficient sequence from
`TypeII.PoweredMeanValue` turns its fourth moment into the source's second
moment on the zero line.

The first theorem keeps the resulting coefficient energy exact.  The
second combines it with the already proved uniform divisor-subpower bound.
No new analytic assumption is introduced.
-/

namespace ExactSemiprimes
namespace Completion

open MeasureTheory

noncomputable section

/-- MT23, Lemma 3.2 applied to the square of a dyadic polynomial.  The
source interval `[-2T,2T]` contains the block `[T,2T]`, and the factor
`4T` is the source main term `2(2T)`. -/
theorem typeI_longFourthMoment_le_of_matomakiTeravainen
    (hMV : MatomakiTeravainenLemmaThreeTwoStatement) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (alpha : ℕ → ℂ) (M T : ℝ),
        1 ≤ M → 1 ≤ T →
        (∫ t in Set.Icc T (2 * T),
            ‖dyadicDirichletPolynomial alpha M (onePlusIT t)‖ ^
              (4 : ℕ)) ≤
          (4 * T + C * (2 * M) ^ (2 : ℕ)) *
            TypeII.poweredLineOneEnergy alpha M 2 := by
  obtain ⟨C, hC, hsource⟩ := hMV
  refine ⟨C, hC, ?_⟩
  intro alpha M T hM hT
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hlength : 1 ≤ (2 * M) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (2 * M - 1)]
  have hheight : 1 ≤ 2 * T := by linarith
  let coeff : ℕ → ℂ :=
    TypeII.poweredLineOneCoefficient alpha (dyadicInterval M) 2
  let energy : ℝ := TypeII.poweredLineOneEnergy alpha M 2
  let whole : ℝ :=
    ∫ t in Set.Icc (-(2 * T)) (2 * T),
      ‖matomakiTeravainenInitialDirichletPolynomial coeff
          ((2 * M) ^ (2 : ℕ)) ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)
  have hraw := hsource ((2 * M) ^ (2 : ℕ)) (2 * T) coeff
    hlength hheight
  have hsourceUpper :
      whole ≤ (4 * T + C * (2 * M) ^ (2 : ℕ)) * energy := by
    have hupper := (abs_le.mp hraw).2
    dsimp only [whole, energy, coeff] at hupper ⊢
    rw [TypeII.poweredLineOneEnergy]
    nlinarith
  let integrand : ℝ → ℝ := fun t ↦
    ‖dyadicDirichletPolynomial alpha M (onePlusIT t)‖ ^ (4 : ℕ)
  have hintegrandCont : Continuous integrand :=
    (Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
      alpha M).norm.pow 4
  have hsubset : Set.Icc T (2 * T) ⊆ Set.Icc (-(2 * T)) (2 * T) := by
    intro t ht
    constructor
    · linarith [ht.1]
    · exact ht.2
  have hrestrict :
      (∫ t in Set.Icc T (2 * T), integrand t) ≤
        ∫ t in Set.Icc (-(2 * T)) (2 * T), integrand t := by
    apply setIntegral_mono_set hintegrandCont.integrableOn_Icc
    · exact Filter.Eventually.of_forall (fun t ↦ pow_nonneg (norm_nonneg _) 4)
    · exact Filter.Eventually.of_forall hsubset
  have hwholeIdentity :
      (∫ t in Set.Icc (-(2 * T)) (2 * T), integrand t) = whole := by
    apply integral_congr_ae
    filter_upwards with t
    rw [show integrand t =
        ‖dyadicDirichletPolynomial alpha M (onePlusIT t) ^ (2 : ℕ)‖ ^
          (2 : ℕ) by
      simp only [integrand, norm_pow]
      ring]
    rw [← TypeII.initialPoweredLineOnePolynomial_eq alpha hMpos 2 t]
  change (∫ t in Set.Icc T (2 * T), integrand t) ≤ _
  exact hrestrict.trans (hwholeIdentity.le.trans hsourceUpper)

/-- Uniform divisor-bounded version of the preceding fourth-moment bound.
The constants `C` and `D` are selected before the coefficient sequence and
all dyadic/height parameters. -/
theorem typeI_longFourthMoment_le_of_divisorBounded
    (hMV : MatomakiTeravainenLemmaThreeTwoStatement)
    {B₀ rho : ℝ} (hB₀ : 0 ≤ B₀) (hrho : 0 < rho) :
    ∃ C D : ℝ, 0 < C ∧ 1 ≤ D ∧
      ∀ (alpha : ℕ → ℂ) (M T A₀ : ℝ),
        1 ≤ M → 1 ≤ T →
        IsDivisorBoundedByConstant B₀ A₀ alpha →
        (∫ t in Set.Icc T (2 * T),
            ‖dyadicDirichletPolynomial alpha M (onePlusIT t)‖ ^
              (4 : ℕ)) ≤
          (4 * T + C * (2 * M) ^ (2 : ℕ)) *
            ((2 * M) ^ (2 : ℕ) *
              ((A₀ ^ (2 : ℕ) * D *
                  ((2 * M) ^ (2 : ℕ)) ^ rho) /
                M ^ (2 : ℕ)) ^ (2 : ℕ)) := by
  obtain ⟨C, hC, hfourth⟩ :=
    typeI_longFourthMoment_le_of_matomakiTeravainen hMV
  obtain ⟨D, hD, hcoeff⟩ :=
    TypeII.exists_uniform_powerConvolution_bound_subpower
      hB₀ (ell := 2) (by norm_num) hrho
  refine ⟨C, D, hC, hD, ?_⟩
  intro alpha M T A₀ hM hT halpha
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hA₀ : 0 ≤ A₀ := halpha.2.1.le
  have hDnonneg : 0 ≤ D := zero_le_one.trans hD
  have hscale : 0 ≤ ((2 * M) ^ (2 : ℕ)) ^ rho :=
    Real.rpow_nonneg (sq_nonneg (2 * M)) _
  have hB : 0 ≤ A₀ ^ (2 : ℕ) * D *
      ((2 * M) ^ (2 : ℕ)) ^ rho := by positivity
  have henergy := TypeII.poweredLineOneEnergy_le_of_convolution_bound
    hMpos hB (hcoeff alpha M A₀ hMpos halpha)
  have hprefactor : 0 ≤ 4 * T + C * (2 * M) ^ (2 : ℕ) := by positivity
  exact (hfourth alpha M T hM hT).trans
    (mul_le_mul_of_nonneg_left henergy hprefactor)

def typeIFirstFactorMomentModule : ProofModule :=
  { name := "Completion.TypeIFirstFactorMoment"
    paperLocation := "MT23 Section 5.1; Lemma 3.2"
    purpose :=
      "Apply the cited mean-value theorem to the squared Type-I first factor, retaining exact powered coefficient energy and deriving its uniform divisor-subpower corollary."
    dependsOn :=
      [ "TypeII.PoweredMeanValue",
        "Assumptions.matomakiTeravainenLemmaThreeTwo" ]
    status := .proved }

end

end Completion
end ExactSemiprimes
