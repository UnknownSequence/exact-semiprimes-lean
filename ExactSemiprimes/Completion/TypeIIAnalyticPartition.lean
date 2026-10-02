import ExactSemiprimes.Completion.TypeIIInstantiation

/-!
# The outer analytic partition for a naturalized Type-II product

This file is the measure-theoretic assembly used after the real source
scales have been naturalized.  The outer threshold is written as `sigma`;
the existing `largeValueR1/R2/R3` partition is reused with parameter
`sigma / 10`, so its threshold `N^(-10 epsilon)` is definitionally the
desired `N^(-sigma)`.

The two non-source-dependent estimates are proved here.  On the tiny piece
the integrand is at most `X⁻²`.  On each unit logarithmic medium bin, a
measure estimate with the standard sparse-propagation scale cancels exactly
against the two upper magnitude bounds, with only the fixed `exp 4` loss.
-/

namespace ExactSemiprimes
namespace Completion

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

/-- The parameter which makes the existing `R1/R2/R3` threshold equal to
`N^(-sigma)`. -/
def outerPartitionEpsilon (sigma : ℝ) : ℝ := sigma / 10

theorem outerPartition_threshold (sigma : ℝ) :
    -10 * outerPartitionEpsilon sigma = -sigma := by
  simp [outerPartitionEpsilon]
  ring

/-- The existing deterministic partition, specialized to an arbitrary
outer exponent `sigma`. -/
theorem outerTypeII_partition (E : Set ℝ) (F₁ F₂ : ℂ → ℂ)
    (N₁ N₂ X sigma : ℝ) :
    TypeII.largeValueR1 E F₁ F₂ N₁ N₂
          (outerPartitionEpsilon sigma) ∪
      TypeII.largeValueR2 E F₁ F₂ N₁ N₂ X
          (outerPartitionEpsilon sigma) ∪
      TypeII.largeValueR3 E F₁ F₂ N₁ N₂ X
          (outerPartitionEpsilon sigma) = E :=
  TypeII.largeValue_partition E F₁ F₂ N₁ N₂ X
    (outerPartitionEpsilon sigma)

/-! ## The outer-large piece -/

/-- Naturalized source-scale form of the full Type-II estimate, with its
large-value set chosen to be the literal outer `R₁` piece.  Compared with
`NaturalizedSourceTypeIIEstimateStatement`, the caller no longer supplies
measurability, interval containment, or the pointwise large-value
disjunction: all three follow from the deterministic partition. -/
def OuterR1NaturalizedTypeIIEstimateStatement : Prop :=
  ∃ C₁ epsilon₀ : ℝ, 0 < C₁ ∧ 0 < epsilon₀ ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
      ∀ B : ℝ, 0 ≤ B →
        ∃ kappa₁ : ℝ, 0 < kappa₁ ∧
          ∀ A₀ a : ℝ, 1 ≤ A₀ → 0 ≤ a →
            ∃ C₂ C X₀ : ℝ,
              0 < C₂ ∧ 0 < C ∧ 1 ≤ X₀ ∧
                ∀ (X M₁ M₂ delta : ℝ) (R N₂ : ℕ)
                    (alpha gamma : ℕ → ℂ) (E : Set ℝ) (S : ℝ),
                  X₀ ≤ X → 1 < X → 4 ≤ Real.log X →
                  2 ≤ M₁ → 2 ≤ M₂ →
                  X ^ (epsilon / 2) ≤ M₁ →
                  M₁ ≤ X ^ (2 / 11 : ℝ) →
                  2 * X ^ (epsilon / 5) ≤ X ^ (epsilon / 2) →
                  X / (2 * (Real.log X) ^ a) < M₁ * M₂ →
                  M₁ * M₂ ≤ 4 * X / (Real.log X) ^ a →
                  (N₂ = TypeII.naturalDyadicCoreScale M₂ ∨
                    N₂ = TypeII.naturalDyadicBoundaryScale M₂) →
                  IsDivisorBoundedByConstant B A₀ alpha →
                  IsDivisorBoundedByConstant B A₀ gamma →
                  MeasurableSet E → E ⊆ Set.Icc (0 : ℝ) X →
                  0 ≤ S →
                  (∀ t ∈ E,
                    ‖dyadicDirichletPolynomial
                      (supportedTypeIIFirstCoefficient delta M₁ R alpha)
                      (TypeII.naturalDyadicCoreScale M₁ : ℝ)
                      (onePlusIT t)‖ ^ (2 : ℕ) ≤ S) →
                  (∫ t in TypeII.largeValueR1 E
                      (dyadicDirichletPolynomial
                        (supportedTypeIIFirstCoefficient delta M₁ R alpha)
                        (TypeII.naturalDyadicCoreScale M₁ : ℝ))
                      (dyadicDirichletPolynomial gamma (N₂ : ℝ))
                      (TypeII.naturalDyadicCoreScale M₁ : ℝ) (N₂ : ℝ)
                      (outerPartitionEpsilon
                        (17 / 70 - C₁ * epsilon)),
                    ‖dyadicDirichletPolynomial
                      (supportedTypeIIFirstCoefficient delta M₁ R alpha)
                      (TypeII.naturalDyadicCoreScale M₁ : ℝ)
                      (onePlusIT t)‖ ^ (2 : ℕ) *
                    ‖dyadicDirichletPolynomial gamma (N₂ : ℝ)
                      (onePlusIT t)‖ ^ (2 : ℕ)) ≤
                    C * (X ^ (-kappa₁) + (Real.log X) ^ C₂ * S)

/-- `FullTypeIIEstimate` feeds the literal outer-large set without any
additional analytic hypothesis. -/
theorem outerR1NaturalizedTypeIIEstimate_of_source
    (hsource : NaturalizedSourceTypeIIEstimateStatement) :
    OuterR1NaturalizedTypeIIEstimateStatement := by
  rcases hsource with ⟨C₁, epsilon₀, hC₁, hepsilon₀, hsource⟩
  refine ⟨C₁, epsilon₀, hC₁, hepsilon₀, ?_⟩
  intro epsilon hepsilon hepsilonUpper B hB
  obtain ⟨kappa₁, hkappa₁, hsource⟩ :=
    hsource epsilon hepsilon hepsilonUpper B hB
  refine ⟨kappa₁, hkappa₁, ?_⟩
  intro A₀ a hA₀ ha
  obtain ⟨C₂, C, X₀, hC₂, hC, hX₀, hsource⟩ :=
    hsource A₀ a hA₀ ha
  refine ⟨C₂, C, X₀, hC₂, hC, hX₀, ?_⟩
  intro X M₁ M₂ delta R N₂ alpha gamma E S hX₀ hX hlog
    hM₁ hM₂ hM₁lower hM₁upper hfloor hprodLower hprodUpper hN₂
    halpha hgamma hE hEsub hS hSbound
  let F₁ : ℂ → ℂ :=
    dyadicDirichletPolynomial
      (supportedTypeIIFirstCoefficient delta M₁ R alpha)
      (TypeII.naturalDyadicCoreScale M₁ : ℝ)
  let F₂ : ℂ → ℂ := dyadicDirichletPolynomial gamma (N₂ : ℝ)
  have hF₁cont : Continuous (fun t : ℝ ↦ F₁ (onePlusIT t)) :=
    Sparse.continuous_dirichletPolynomial_onePlusIT_sparse _ _
  have hF₂cont : Continuous (fun t : ℝ ↦ F₂ (onePlusIT t)) :=
    Sparse.continuous_dirichletPolynomial_onePlusIT_sparse _ _
  let U := TypeII.largeValueR1 E F₁ F₂
    (TypeII.naturalDyadicCoreScale M₁ : ℝ) (N₂ : ℝ)
    (outerPartitionEpsilon (17 / 70 - C₁ * epsilon))
  have hUmeas : MeasurableSet U :=
    TypeII.measurableSet_largeValueR1 hE hF₁cont.norm.measurable
      hF₂cont.norm.measurable
  have hUsub : U ⊆ Set.Icc (0 : ℝ) X := by
    intro t ht
    exact hEsub ht.1
  have hlarge : ∀ t ∈ U,
      (TypeII.naturalDyadicCoreScale M₁ : ℝ) ^
          (-(17 / 70 - C₁ * epsilon)) ≤ ‖F₁ (onePlusIT t)‖ ∨
        (N₂ : ℝ) ^ (-(17 / 70 - C₁ * epsilon)) ≤
          ‖F₂ (onePlusIT t)‖ := by
    intro t ht
    have ht' := (TypeII.mem_largeValueR1_iff.mp ht).2
    simpa only [outerPartition_threshold, TypeII.typeIIMagnitude] using ht'
  have hSboundU : ∀ t ∈ U, ‖F₁ (onePlusIT t)‖ ^ (2 : ℕ) ≤ S := by
    intro t ht
    exact hSbound t ht.1
  exact hsource X M₁ M₂ delta R N₂ alpha gamma U S hX₀ hX hlog
    hM₁ hM₂ hM₁lower hM₁upper hfloor hprodLower hprodUpper hN₂
    halpha hgamma hUmeas hUsub hlarge hS hSboundU

/-- Fully cited outer-large specialization. -/
theorem outerR1NaturalizedTypeIIEstimate_of_externalInputs
    (inputs : ExternalInputs) : OuterR1NaturalizedTypeIIEstimateStatement :=
  outerR1NaturalizedTypeIIEstimate_of_source
    (naturalizedSourceTypeIIEstimate_of_externalInputs inputs)

/-- On the tiny outer piece both factors are below one and at least one is
below `X⁻¹`; hence their squared product is at most `X⁻²`. -/
theorem typeIIWeight_le_inv_sq_of_mem_outerR3
    {E : Set ℝ} {F₁ F₂ : ℂ → ℂ} {N₁ N₂ X sigma t : ℝ}
    (hX : 0 < X) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂)
    (hsigma : 0 ≤ sigma)
    (ht : t ∈ TypeII.largeValueR3 E F₁ F₂ N₁ N₂ X
      (outerPartitionEpsilon sigma)) :
    TypeII.typeIIMagnitude F₁ t ^ (2 : ℕ) *
        TypeII.typeIIMagnitude F₂ t ^ (2 : ℕ) ≤
      (X⁻¹) ^ (2 : ℕ) := by
  have ht' := TypeII.mem_largeValueR3_iff.mp ht
  have hnot := ht'.2.1
  have htiny := ht'.2.2
  simp only [not_or, not_le] at hnot
  have hsmall₁ : TypeII.typeIIMagnitude F₁ t < N₁ ^ (-sigma) := by
    simpa only [outerPartition_threshold] using hnot.1
  have hsmall₂ : TypeII.typeIIMagnitude F₂ t < N₂ ^ (-sigma) := by
    simpa only [outerPartition_threshold] using hnot.2
  have hpow₁ : N₁ ^ (-sigma) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN₁ (by linarith)
  have hpow₂ : N₂ ^ (-sigma) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN₂ (by linarith)
  have hmag₁ : TypeII.typeIIMagnitude F₁ t ≤ 1 := hsmall₁.le.trans hpow₁
  have hmag₂ : TypeII.typeIIMagnitude F₂ t ≤ 1 := hsmall₂.le.trans hpow₂
  have hinv : 0 ≤ X⁻¹ := (inv_pos.mpr hX).le
  have hprod : TypeII.typeIIMagnitude F₁ t *
      TypeII.typeIIMagnitude F₂ t ≤ X⁻¹ := by
    rcases htiny with htiny₁ | htiny₂
    · calc
        TypeII.typeIIMagnitude F₁ t * TypeII.typeIIMagnitude F₂ t ≤
            X⁻¹ * 1 :=
          mul_le_mul htiny₁.le hmag₂ (norm_nonneg _) hinv
        _ = X⁻¹ := mul_one _
    · calc
        TypeII.typeIIMagnitude F₁ t * TypeII.typeIIMagnitude F₂ t ≤
            1 * X⁻¹ :=
          mul_le_mul hmag₁ htiny₂.le (norm_nonneg _) (by positivity)
        _ = X⁻¹ := one_mul _
  calc
    TypeII.typeIIMagnitude F₁ t ^ (2 : ℕ) *
          TypeII.typeIIMagnitude F₂ t ^ (2 : ℕ) =
        (TypeII.typeIIMagnitude F₁ t *
          TypeII.typeIIMagnitude F₂ t) ^ (2 : ℕ) := by ring
    _ ≤ (X⁻¹) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hprod 2

/-- Integrated trivial estimate for the tiny piece.  Keeping its measure
explicit avoids any endpoint normalization convention. -/
theorem integral_outerR3_le_measure_mul_inv_sq
    {E : Set ℝ} {F₁ F₂ : ℂ → ℂ} {N₁ N₂ X sigma : ℝ}
    (hX : 0 < X) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂)
    (hsigma : 0 ≤ sigma)
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc (-X) X)
    (hF₁ : Continuous (fun t : ℝ ↦ F₁ (onePlusIT t)))
    (hF₂ : Continuous (fun t : ℝ ↦ F₂ (onePlusIT t))) :
    (∫ t in TypeII.largeValueR3 E F₁ F₂ N₁ N₂ X
        (outerPartitionEpsilon sigma),
        TypeII.typeIIMagnitude F₁ t ^ (2 : ℕ) *
          TypeII.typeIIMagnitude F₂ t ^ (2 : ℕ)) ≤
      volume.real (TypeII.largeValueR3 E F₁ F₂ N₁ N₂ X
        (outerPartitionEpsilon sigma)) * (X⁻¹) ^ (2 : ℕ) := by
  let E₃ := TypeII.largeValueR3 E F₁ F₂ N₁ N₂ X
    (outerPartitionEpsilon sigma)
  let f : ℝ → ℝ := fun t ↦
    TypeII.typeIIMagnitude F₁ t ^ (2 : ℕ) *
      TypeII.typeIIMagnitude F₂ t ^ (2 : ℕ)
  have hmag₁ : Measurable (TypeII.typeIIMagnitude F₁) := hF₁.norm.measurable
  have hmag₂ : Measurable (TypeII.typeIIMagnitude F₂) := hF₂.norm.measurable
  have hE₃meas : MeasurableSet E₃ :=
    TypeII.measurableSet_largeValueR3 hE hmag₁ hmag₂
  have hE₃sub : E₃ ⊆ Set.Icc (-X) X := by
    intro t ht
    exact hEsub ht.1.1
  have hfcont : Continuous f := (hF₁.norm.pow 2).mul (hF₂.norm.pow 2)
  have hfint : IntegrableOn f E₃ :=
    hfcont.integrableOn_Icc.mono_set hE₃sub
  have hcint : IntegrableOn (fun _ : ℝ ↦ (X⁻¹) ^ (2 : ℕ)) E₃ :=
    continuous_const.integrableOn_Icc.mono_set hE₃sub
  calc
    (∫ t in E₃, f t) ≤ ∫ _t in E₃, (X⁻¹) ^ (2 : ℕ) := by
      apply setIntegral_mono_on hfint hcint hE₃meas
      intro t ht
      exact typeIIWeight_le_inv_sq_of_mem_outerR3 hX hN₁ hN₂ hsigma ht
    _ = volume.real E₃ * (X⁻¹) ^ (2 : ℕ) := by
      rw [setIntegral_const]
      simp

/-- The sparse-propagation scale and the reciprocal bin weight cancel
exactly. -/
theorem sparseScaleTarget_mul_reciprocalWeight
    {N₁ N₂ sigma₁ sigma₂ : ℝ}
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) :
    Sparse.sparsePropagationScaleTarget N₁ N₂ sigma₁ sigma₂ *
        (N₁ ^ (-2 * sigma₁) * N₂ ^ (-2 * sigma₂)) = 1 := by
  unfold Sparse.sparsePropagationScaleTarget
  rw [mul_assoc, mul_left_comm (N₂ ^ (2 * sigma₂)),
    ← mul_assoc, ← Real.rpow_add hN₁, ← Real.rpow_add hN₂]
  norm_num

/-- A sparse-propagation measure bound on one unit log bin gives the
corresponding weighted integral bound, with the exact fixed `exp 4` loss.
All magnitude lower and upper bounds are supplied by bin membership itself. -/
theorem integral_mediumLogBin_le_of_sparseMeasure
    {E : Set ℝ} {F₁ F₂ : ℂ → ℂ}
    {N₁ N₂ X eps K saving : ℝ} {k : ℤ × ℤ}
    (hX : 0 < X) (hN₁ : 1 < N₁) (hN₂ : 1 < N₂)
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc (-X) X)
    (hF₁ : Continuous (fun t : ℝ ↦ F₁ (onePlusIT t)))
    (hF₂ : Continuous (fun t : ℝ ↦ F₂ (onePlusIT t)))
    (hmeasure :
      volume.real (TypeII.mediumLogMagnitudeBinSet E F₁ F₂
        N₁ N₂ X eps k) ≤
        K * Sparse.sparsePropagationScaleTarget N₁ N₂
          (TypeII.upperBinExponent N₁ k.1)
          (TypeII.upperBinExponent N₂ k.2) * saving) :
    (∫ t in TypeII.mediumLogMagnitudeBinSet E F₁ F₂
        N₁ N₂ X eps k,
        TypeII.typeIIMagnitude F₁ t ^ (2 : ℕ) *
          TypeII.typeIIMagnitude F₂ t ^ (2 : ℕ)) ≤
      Real.exp 4 * K * saving := by
  let V := TypeII.mediumLogMagnitudeBinSet E F₁ F₂
    N₁ N₂ X eps k
  let f : ℝ → ℝ := fun t ↦
    TypeII.typeIIMagnitude F₁ t ^ (2 : ℕ) *
      TypeII.typeIIMagnitude F₂ t ^ (2 : ℕ)
  let W : ℝ := Real.exp 4 *
    (N₁ ^ (-2 * TypeII.upperBinExponent N₁ k.1) *
      N₂ ^ (-2 * TypeII.upperBinExponent N₂ k.2))
  have hmag₁ : Measurable (TypeII.typeIIMagnitude F₁) := hF₁.norm.measurable
  have hmag₂ : Measurable (TypeII.typeIIMagnitude F₂) := hF₂.norm.measurable
  have hVmeas : MeasurableSet V :=
    TypeII.measurableSet_mediumLogMagnitudeBinSet hE hmag₁ hmag₂
  have hVsub : V ⊆ Set.Icc (-X) X := by
    intro t ht
    exact hEsub ht.1.1
  have hfcont : Continuous f := (hF₁.norm.pow 2).mul (hF₂.norm.pow 2)
  have hfint : IntegrableOn f V := hfcont.integrableOn_Icc.mono_set hVsub
  have hWint : IntegrableOn (fun _ : ℝ ↦ W) V :=
    continuous_const.integrableOn_Icc.mono_set hVsub
  have hpoint : ∀ t ∈ V, f t ≤ W := by
    intro t ht
    have hpos := TypeII.typeIIMagnitudes_pos_of_mem_largeValueR2
      (by positivity : 0 < X) ht.1
    have hsum := TypeII.sum_typeIIWeight_logMagnitudePairBin_le_expFour_cardWeight
      hN₁ hN₂ ({t} : Finset ℝ)
      (by
        intro u hu
        simp only [Finset.mem_singleton] at hu
        subst u
        exact ht.2)
      (by
        intro u hu
        simp only [Finset.mem_singleton] at hu
        subst u
        exact hpos.1)
      (by
        intro u hu
        simp only [Finset.mem_singleton] at hu
        subst u
        exact hpos.2)
    simpa [f, W] using hsum
  have hconst : (∫ _t in V, W) = volume.real V * W := by
    rw [setIntegral_const]
    simp
  have hscaleCancel := sparseScaleTarget_mul_reciprocalWeight
    (zero_lt_one.trans hN₁) (zero_lt_one.trans hN₂)
    (sigma₁ := TypeII.upperBinExponent N₁ k.1)
    (sigma₂ := TypeII.upperBinExponent N₂ k.2)
  calc
    (∫ t in V, f t) ≤ ∫ _t in V, W :=
      setIntegral_mono_on hfint hWint hVmeas hpoint
    _ = volume.real V * W := hconst
    _ ≤ (K * Sparse.sparsePropagationScaleTarget N₁ N₂
          (TypeII.upperBinExponent N₁ k.1)
          (TypeII.upperBinExponent N₂ k.2) * saving) * W :=
      mul_le_mul_of_nonneg_right hmeasure (by dsimp [W]; positivity)
    _ = (Real.exp 4 * K * saving) *
          (Sparse.sparsePropagationScaleTarget N₁ N₂
            (TypeII.upperBinExponent N₁ k.1)
            (TypeII.upperBinExponent N₂ k.2) *
          (N₁ ^ (-2 * TypeII.upperBinExponent N₁ k.1) *
            N₂ ^ (-2 * TypeII.upperBinExponent N₂ k.2))) := by
      dsimp [W]
      ring
    _ = Real.exp 4 * K * saving := by rw [hscaleCancel, mul_one]

/-! ## Direct insertion of the sparse-propagation package -/

/-- The non-bin-specific parameter data needed by the moving sparse
propagation theorem.  The two magnitude lower bounds, measurability of the
actual bin, and its containment in `[-X,X]` are intentionally absent: the
next theorem proves all of them from `bin` and `ambient`.

This structure is also the precise residual interface at the current
source boundary.  Its fields are elementary moving-scale facts, support
facts, and the defining large-prime condition; it contains no new analytic
estimate. -/
structure SparsePropagationMediumBinData
    (X epsilon B : ℝ) where
  (P M M1 M2 A0 a theta phi mu : ℝ)
  (scaleError firstError residualError keyError : ℝ)
  k : ℕ
  beta : ℕ → ℂ
  b : ℕ → ℝ
  ambient : Set ℝ
  partitionEpsilon : ℝ
  bin : ℤ × ℤ
  hpartitionEpsilon : 0 ≤ partitionEpsilon
  hX : 1 < X
  hPdef : P = (Real.log X) ^ a
  ha : 1 < a
  hk : k = ⌊Real.log X / Real.log (2 * P)⌋₊
  hden : 1 ≤ Real.log (2 * P)
  hMdef : M = P ^ k
  hM : 1 ≤ M
  hMX : M ≤ X
  hM1 : 0 < M1
  hM2 : 2 ≤ M2
  hM1lower : X ^ (epsilon / 2) ≤ M1
  hsigmaStrong :
    1 / 5 + 2 * epsilon ≤ TypeII.upperBinExponent M1 bin.1
  hsupport : ∀ m ∈ Sparse.primePowerSupport (dyadicPrimes P) k,
    M ≤ (m : ℝ) ∧ (m : ℝ) ≤ X
  hcard : ((Sparse.primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
    X ^ (1 / 3 : ℝ)
  hb : IsDivisorBoundedByConstant B A0 (fun n ↦ (b n : ℂ))
  hblocks : ∀ j ∈ Finset.range 5, 2 ≤ (2 : ℝ) ^ j * M1 ^ (5 : ℕ)
  hambient : MeasurableSet ambient
  hambientSub : ambient ⊆ Set.Icc (-X) X
  hprime : ∀ t ∈ ambient,
    P ^ (-epsilon / 10) ≤
      ‖Sparse.primeBasePolynomial (dyadicPrimes P) (onePlusIT t)‖
  htheta : Real.log M1 / Real.log X = theta
  hMExponent : 1 - scaleError ≤ Real.log M / Real.log X
  htheta0 : 0 ≤ theta
  htheta1 : theta ≤ 1
  hresidualError :
    residualError = firstError + scaleError * (1 - 1 / a)
  hkey :
    1 - 1 / a - residualError ≤
        theta * (1 - 2 * TypeII.upperBinExponent M1 bin.1) →
      1 / a + keyError <
        Sparse.secondBranchKeyExponent theta
          (TypeII.upperBinExponent M1 bin.1) (TypeII.upperBinExponent M2 bin.2)
  hMcoord : M = X ^ mu
  hM1coord : M1 = X ^ theta
  hM2coord : M2 = X ^ phi
  hRboundFirst :
    ((Sparse.primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
      M ^ (1 - 1 / a + epsilon ^ 2 / 100)
  hRboundSecond :
    ((Sparse.primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
      M ^ (1 - 1 / a + epsilon / 100)
  haLower : 12 / 11 ≤ a
  haUpper : a ≤ 11 / 10
  hmuLower : 1 - epsilon / 100 ≤ mu
  hmuUpper : mu ≤ 1
  hthetaLower : epsilon / 2 ≤ theta
  hthetaUpper : theta ≤ 2 / 11
  hphiUpper : phi ≤ 1
  hproductLoss : 1 - theta - phi ≤ epsilon ^ 2 / 100
  hfirstReserve : epsilon / 3 ≤ firstError
  hsecondReserve :
    4 * epsilon +
      2 * TypeII.upperBinExponent M2 bin.2 * (epsilon ^ 2 / 100) ≤ keyError

/-- The literal logarithmic bin associated with sparse-propagation data. -/
def sparsePropagationMediumLogBin
    {X epsilon B : ℝ} (d : SparsePropagationMediumBinData X epsilon B) :
    Set ℝ :=
  TypeII.mediumLogMagnitudeBinSet d.ambient
    (dyadicDirichletPolynomial (fun n ↦ (d.b n : ℂ)) d.M1)
    (dyadicDirichletPolynomial d.beta d.M2)
    d.M1 d.M2 X d.partitionEpsilon d.bin

/-- The implication returned by
`sparsePropagation_uniformConstants_powerSaving_package` applies directly
to a literal medium log bin.  In particular, the log-bin lower edges are
exactly the `sigma1,sigma2` lower bounds expected by that theorem. -/
theorem sparsePropagation_uniformPackage_on_mediumLogBin
    {X epsilon B CRe CIm C D : ℝ}
    (hpackage :
      ∀ {X P M M1 M2 A0 a theta phi mu sigma1 sigma2
          scaleError firstError residualError keyError : ℝ}
          {k : ℕ} {beta : ℕ → ℂ} {b : ℕ → ℝ} {E : Set ℝ},
        1 < X → P = (Real.log X) ^ a → 1 < a →
        k = ⌊Real.log X / Real.log (2 * P)⌋₊ →
        1 ≤ Real.log (2 * P) → M = P ^ k →
        1 ≤ M → M ≤ X → 0 < M1 → 2 ≤ M2 →
        X ^ (epsilon / 2) ≤ M1 →
        1 / 5 + 2 * epsilon ≤ sigma1 →
        (∀ m ∈ Sparse.primePowerSupport (dyadicPrimes P) k,
          M ≤ (m : ℝ) ∧ (m : ℝ) ≤ X) →
        ((Sparse.primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
          X ^ (1 / 3 : ℝ) →
        IsDivisorBoundedByConstant B A0 (fun n ↦ (b n : ℂ)) →
        (∀ j ∈ Finset.range 5, 2 ≤ (2 : ℝ) ^ j * M1 ^ (5 : ℕ)) →
        MeasurableSet E → E ⊆ Set.Icc (-X) X →
        (∀ t ∈ E, P ^ (-epsilon / 10) ≤
          ‖Sparse.primeBasePolynomial (dyadicPrimes P) (onePlusIT t)‖) →
        (∀ t ∈ E, M1 ^ (-sigma1) ≤
          ‖dyadicDirichletPolynomial (fun n ↦ (b n : ℂ)) M1
            (onePlusIT t)‖) →
        (∀ t ∈ E, M2 ^ (-sigma2) ≤
          ‖dyadicDirichletPolynomial beta M2 (onePlusIT t)‖) →
        Real.log M1 / Real.log X = theta →
        1 - scaleError ≤ Real.log M / Real.log X →
        0 ≤ theta → theta ≤ 1 →
        residualError = firstError + scaleError * (1 - 1 / a) →
        (1 - 1 / a - residualError ≤ theta * (1 - 2 * sigma1) →
          1 / a + keyError < Sparse.secondBranchKeyExponent theta sigma1 sigma2) →
        M = X ^ mu → M1 = X ^ theta → M2 = X ^ phi →
        ((Sparse.primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
          M ^ (1 - 1 / a + epsilon ^ 2 / 100) →
        ((Sparse.primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
          M ^ (1 - 1 / a + epsilon / 100) →
        12 / 11 ≤ a → a ≤ 11 / 10 →
        1 - epsilon / 100 ≤ mu → mu ≤ 1 →
        epsilon / 2 ≤ theta → theta ≤ 2 / 11 → phi ≤ 1 →
        1 - theta - phi ≤ epsilon ^ 2 / 100 →
        (M1 ^ (1 - 2 * sigma1) ≤
              X ^ (-firstError) * M ^ (1 - 1 / a) →
            theta * (1 - 2 * sigma1) ≤
              -epsilon / 3 + mu * (1 - 1 / a)) →
        (X ^ (1 / a + keyError) ≤
              (X ^ theta) ^ (5 - 8 * sigma1) *
                (X ^ (1 - theta)) ^ (2 * sigma2) →
            1 / a + 4 * epsilon ≤
              (5 - 8 * sigma1) * theta + 2 * sigma2 * phi) →
        4 * (CRe *
                (dyadicRealCoefficientSup
                  (fun n ↦ (beta n).re) M2) ^ (2 : ℕ) +
              CIm *
                (dyadicRealCoefficientSup
                  (fun n ↦ (beta n).im) M2) ^ (2 : ℕ)) ≤
            X ^ (epsilon ^ 2 / 100) →
        (volume.real E ≤
            2 * Sparse.sparsePropagationScaleTarget M1 M2 sigma1 sigma2 *
              X ^ (-epsilon ^ 2) ∨
          volume.real E ≤
            Sparse.secondBranchPowerConstant C D A0 epsilon *
              Sparse.sparsePropagationScaleTarget M1 M2 sigma1 sigma2 *
              X ^ (-3 * epsilon)))
    (d : SparsePropagationMediumBinData X epsilon B)
    (hepsilon : 0 < epsilon)
    (hcoefficientLoss :
      4 * (CRe *
              (dyadicRealCoefficientSup
                (fun n ↦ (d.beta n).re) d.M2) ^ (2 : ℕ) +
            CIm *
              (dyadicRealCoefficientSup
                (fun n ↦ (d.beta n).im) d.M2) ^ (2 : ℕ)) ≤
        X ^ (epsilon ^ 2 / 100)) :
    volume.real (sparsePropagationMediumLogBin d) ≤
        2 * Sparse.sparsePropagationScaleTarget d.M1 d.M2
          (TypeII.upperBinExponent d.M1 d.bin.1)
          (TypeII.upperBinExponent d.M2 d.bin.2) *
          X ^ (-epsilon ^ 2) ∨
      volume.real (sparsePropagationMediumLogBin d) ≤
        Sparse.secondBranchPowerConstant C D d.A0 epsilon *
          Sparse.sparsePropagationScaleTarget d.M1 d.M2
            (TypeII.upperBinExponent d.M1 d.bin.1)
            (TypeII.upperBinExponent d.M2 d.bin.2) *
          X ^ (-3 * epsilon) := by
  let F₁ : ℂ → ℂ :=
    dyadicDirichletPolynomial (fun n ↦ (d.b n : ℂ)) d.M1
  let F₂ : ℂ → ℂ := dyadicDirichletPolynomial d.beta d.M2
  let V : Set ℝ := sparsePropagationMediumLogBin d
  have hM1one : 1 < d.M1 := by
    have hpow : 1 < X ^ (epsilon / 2) :=
      Real.one_lt_rpow d.hX (by positivity)
    exact hpow.trans_le d.hM1lower
  have hM2one : 1 < d.M2 := lt_of_lt_of_le (by norm_num) d.hM2
  have hF₁cont : Continuous (fun t : ℝ ↦ F₁ (onePlusIT t)) :=
    Sparse.continuous_dirichletPolynomial_onePlusIT_sparse _ _
  have hF₂cont : Continuous (fun t : ℝ ↦ F₂ (onePlusIT t)) :=
    Sparse.continuous_dirichletPolynomial_onePlusIT_sparse _ _
  have hVmeas : MeasurableSet V :=
    TypeII.measurableSet_mediumLogMagnitudeBinSet d.hambient
      hF₁cont.norm.measurable hF₂cont.norm.measurable
  have hVsubAmbient : V ⊆ d.ambient := fun _ ht ↦ ht.1.1
  have hVsub : V ⊆ Set.Icc (-X) X := hVsubAmbient.trans d.hambientSub
  by_cases hVnonempty : V.Nonempty
  swap
  · have hVempty : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hVnonempty
    left
    rw [show sparsePropagationMediumLogBin d = V from rfl, hVempty]
    simp only [measureReal_empty]
    unfold Sparse.sparsePropagationScaleTarget
    have hM1pos : 0 < d.M1 := d.hM1
    have hM2pos : 0 < d.M2 := lt_of_lt_of_le (by norm_num) d.hM2
    have hXpos : 0 < X := lt_trans zero_lt_one d.hX
    positivity
  have hpos : ∀ t ∈ V,
      0 < TypeII.typeIIMagnitude F₁ t ∧
        0 < TypeII.typeIIMagnitude F₂ t := by
    intro t ht
    exact TypeII.typeIIMagnitudes_pos_of_mem_largeValueR2
      (zero_lt_one.trans d.hX) ht.1
  have hlower₁ : ∀ t ∈ V,
      d.M1 ^ (-TypeII.upperBinExponent d.M1 d.bin.1) ≤
        ‖F₁ (onePlusIT t)‖ := by
    intro t ht
    exact (TypeII.magnitude_bounds_of_mem_logMagnitudeBin_upperExponent
      hM1one ht.2.1 (hpos t ht).1).1.le
  have hlower₂ : ∀ t ∈ V,
      d.M2 ^ (-TypeII.upperBinExponent d.M2 d.bin.2) ≤
        ‖F₂ (onePlusIT t)‖ := by
    intro t ht
    exact (TypeII.magnitude_bounds_of_mem_logMagnitudeBin_upperExponent
      hM2one ht.2.2 (hpos t ht).2).1.le
  obtain ⟨t₀, ht₀⟩ := hVnonempty
  have ht₀R2 := TypeII.mem_largeValueR2_iff.mp ht₀.1
  have hsigma2pos :
      0 < TypeII.upperBinExponent d.M2 d.bin.2 := by
    have hstrict := TypeII.lt_upperBinExponent_of_magnitude_lt_rpow
      hM2one ht₀.2.2 (hpos t₀ ht₀).2
      (by simpa only [neg_mul] using ht₀R2.2.2.1)
    have := d.hpartitionEpsilon
    linarith
  have htransfers := Sparse.sparseCoordinateTransfers_of_paperReserves
    (sigma1 := TypeII.upperBinExponent d.M1 d.bin.1) (a := d.a)
    d.hX d.hMcoord d.hM1coord d.hfirstReserve hsigma2pos.le
    d.hproductLoss d.hsecondReserve
  exact hpackage d.hX d.hPdef d.ha d.hk d.hden d.hMdef d.hM d.hMX
    d.hM1 d.hM2 d.hM1lower d.hsigmaStrong d.hsupport d.hcard d.hb
    d.hblocks hVmeas hVsub (fun t ht ↦ d.hprime t (hVsubAmbient ht))
    hlower₁ hlower₂ d.htheta d.hMExponent d.htheta0 d.htheta1
    d.hresidualError d.hkey d.hMcoord d.hM1coord
    d.hM2coord d.hRboundFirst d.hRboundSecond d.haLower d.haUpper
    d.hmuLower d.hmuUpper d.hthetaLower d.hthetaUpper d.hphiUpper
    d.hproductLoss htransfers.1 htransfers.2 hcoefficientLoss

/-- Complete deterministic outer assembly.  The only inputs are the bound
on the full-estimate piece and the already-normalized sparse measure bound
for every medium logarithmic bin; the tiny range and all bin summation are
discharged internally. -/
theorem integral_typeII_outerPartition_le
    {E : Set ℝ} {F₁ F₂ : ℂ → ℂ}
    {N₁ N₂ X sigma E₁ K saving : ℝ}
    (hX : 0 < X) (hN₁ : 1 < N₁) (hN₂ : 1 < N₂)
    (hsigma : 0 ≤ sigma)
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc (-X) X)
    (hF₁ : Continuous (fun t : ℝ ↦ F₁ (onePlusIT t)))
    (hF₂ : Continuous (fun t : ℝ ↦ F₂ (onePlusIT t)))
    (hlarge :
      (∫ t in TypeII.largeValueR1 E F₁ F₂ N₁ N₂
          (outerPartitionEpsilon sigma),
          TypeII.typeIIMagnitude F₁ t ^ (2 : ℕ) *
            TypeII.typeIIMagnitude F₂ t ^ (2 : ℕ)) ≤ E₁)
    (hbins : ∀ k ∈ TypeII.logMagnitudePairIndexRange X,
      volume.real (TypeII.mediumLogMagnitudeBinSet E F₁ F₂
        N₁ N₂ X (outerPartitionEpsilon sigma) k) ≤
        K * Sparse.sparsePropagationScaleTarget N₁ N₂
          (TypeII.upperBinExponent N₁ k.1)
          (TypeII.upperBinExponent N₂ k.2) * saving) :
    (∫ t in E,
        TypeII.typeIIMagnitude F₁ t ^ (2 : ℕ) *
          TypeII.typeIIMagnitude F₂ t ^ (2 : ℕ)) ≤
      E₁ +
        ((((⌊Real.log X⌋ + 1).toNat) ^ 2 : ℕ) : ℝ) *
          (Real.exp 4 * K * saving) +
        volume.real (TypeII.largeValueR3 E F₁ F₂ N₁ N₂ X
          (outerPartitionEpsilon sigma)) * (X⁻¹) ^ (2 : ℕ) := by
  let f : ℝ → ℝ := fun t ↦
    TypeII.typeIIMagnitude F₁ t ^ (2 : ℕ) *
      TypeII.typeIIMagnitude F₂ t ^ (2 : ℕ)
  have hmag₁ : Measurable (TypeII.typeIIMagnitude F₁) := hF₁.norm.measurable
  have hmag₂ : Measurable (TypeII.typeIIMagnitude F₂) := hF₂.norm.measurable
  have hfcont : Continuous f := (hF₁.norm.pow 2).mul (hF₂.norm.pow 2)
  have hfint : IntegrableOn f E := hfcont.integrableOn_Icc.mono_set hEsub
  apply TypeII.integral_typeII_le_of_extremes_and_medium_bins
    hE hmag₁ hmag₂ hfint hX
    hN₁.le hN₂.le (by dsimp [outerPartitionEpsilon]; positivity) hlarge
  · exact integral_outerR3_le_measure_mul_inv_sq hX hN₁.le hN₂.le
      hsigma hE hEsub hF₁ hF₂
  · intro k hk
    exact integral_mediumLogBin_le_of_sparseMeasure hX hN₁ hN₂
      hE hEsub hF₁ hF₂ (hbins k hk)

/-- Registry entry for the completed deterministic analytic partition. -/
def typeIIAnalyticPartitionModule : ProofModule :=
  { name := "Completion.TypeIIAnalyticPartition"
    paperLocation := "Proof of Proposition 7.1, outer Type-II partition"
    purpose :=
      "Partition each naturalized Type-II product at an arbitrary outer threshold, prove the tiny-range integral estimate, cancel sparse magnitude-bin weights against their measure scale, and sum every logarithmic bin."
    dependsOn := ["Completion.TypeIIInstantiation",
      "TypeII.TypeIIEstimate", "Sparse.PropagationParameters"]
    status := .proved }

end
end Completion
end ExactSemiprimes
