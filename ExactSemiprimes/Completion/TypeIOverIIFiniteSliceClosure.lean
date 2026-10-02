import ExactSemiprimes.Completion.FiniteSliceInsertedCauchy
import ExactSemiprimes.Completion.TypeIOverIICompositeMeanValue

/-!
# Type-I/II finite-slice closure

This file performs the quantifier-correct prime-power insertion in a
Type-I/II component.  Watt's cited fourth-moment estimate is applied once;
the other Cauchy moment becomes a finite sum of literal slice moments with
the exact factor `k`.

The collected product is normalized and fed to MT23, Lemma 3.2 in
`TypeIOverIICompositeMeanValue`; the displayed zero-line coefficient energy
is then bounded by explicit divisor propagation.  Thus the local finite-slice
step is closed here.  Any later `X`-power saving still requires the global
component-scale relations and the paper's choice of the integer power `k`.
-/

namespace ExactSemiprimes
namespace Completion

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Type-I/II component assembly from explicit per-slice bounds for the
ordinary mean-value moment. -/
theorem typeIOverII_primePower_finiteSliceAssembly_of_moments
    (hWatt : MatomakiTeravainenLemmaThreeFivePartOneStatement)
    {eta epsilon P M₁ M₂ N N' T : ℝ} {k : ℕ}
    {alpha beta : ℕ → ℂ} {E : Set ℝ} {R : ℕ → ℝ}
    (heta : 0 < eta) (hP : 1 ≤ P) (hk : 1 ≤ k)
    (hM₂ : 1 ≤ M₂) (hN : 1 ≤ N) (hN' : 1 ≤ N')
    (hT : 1 ≤ T) (hNN' : N < N') (hN'two : N' ≤ 2 * N)
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc T (2 * T))
    (hlarge : ∀ t ∈ E,
      P ^ (-epsilon / 10) ≤
        ‖primeDirichletPolynomial P (onePlusIT t)‖)
    (hsliceMoment : ∀ j ∈ Finset.range k,
      (∫ t in E,
        ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (4 : ℕ) *
          ‖dyadicDirichletPolynomial beta M₂ (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖dyadicDirichletPolynomial
            (rawPrimePowerCoefficient (dyadicPrimes P) k)
            ((2 : ℝ) ^ j * P ^ k) (onePlusIT t)‖ ^ (2 : ℕ)) ≤
        R j) :
    ∃ C_Watt : ℝ, 0 < C_Watt ∧
      (∫ t in E,
        ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖dyadicDirichletPolynomial beta M₂ (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖matomakiTeravainenZetaSegmentPolynomial N N'
            (onePlusIT t)‖ ^ (2 : ℕ)) ≤
        ((P ^ (-epsilon / 10)) ^ k)⁻¹ *
          ((typeIOverIIWattMajorant C_Watt eta M₂ N N' T beta) ^
              (1 / 2 : ℝ) *
            (((k : ℝ) * ∑ j ∈ Finset.range k, R j) ^
              (1 / 2 : ℝ))) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  obtain ⟨C_Watt, hC_Watt, hWattFull⟩ :=
    typeIOverII_twistedFourthMoment_le_of_matomakiTeravainen hWatt
      heta hM₂ hN hN' hT hNN' hN'two
  let A₁ : ℝ → ℝ := fun t ↦
    ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖
  let A₂ : ℝ → ℝ := fun t ↦
    ‖dyadicDirichletPolynomial beta M₂ (onePlusIT t)‖
  let A₃ : ℝ → ℝ := fun t ↦
    ‖matomakiTeravainenZetaSegmentPolynomial N N' (onePlusIT t)‖
  let Slice : ℕ → ℝ → ℝ := fun j t ↦
    ‖dyadicDirichletPolynomial
      (rawPrimePowerCoefficient (dyadicPrimes P) k)
      ((2 : ℝ) ^ j * P ^ k) (onePlusIT t)‖
  let K : ℝ := ((P ^ (-epsilon / 10)) ^ k)⁻¹
  let W : ℝ := typeIOverIIWattMajorant
    C_Watt eta M₂ N N' T beta
  have hA₁cont : Continuous A₁ :=
    (Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
      alpha M₁).norm
  have hA₂cont : Continuous A₂ :=
    (Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
      beta M₂).norm
  have hA₃cont : Continuous A₃ := by
    dsimp [A₃]
    exact (Sparse.continuous_dirichletPolynomial_onePlusIT_sparse
      (fun _ ↦ 1) (natOpenClosedInterval N N')).norm
  have hSliceCont : ∀ j ∈ Finset.range k, Continuous (Slice j) := by
    intro j hj
    exact (Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
      (rawPrimePowerCoefficient (dyadicPrimes P) k)
      ((2 : ℝ) ^ j * P ^ k)).norm
  have hA₂nonneg : ∀ t ∈ E, 0 ≤ A₂ t := by
    intro t ht
    exact norm_nonneg _
  have hSliceNonneg : ∀ j ∈ Finset.range k, ∀ t ∈ E,
      0 ≤ Slice j t := by
    intro j hj t ht
    exact norm_nonneg _
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    exact inv_nonneg.mpr (pow_nonneg (Real.rpow_nonneg hPpos.le _) k)
  have hinsert : ∀ t ∈ E,
      1 ≤ K * ∑ j ∈ Finset.range k, Slice j t := by
    intro t ht
    simpa [K, Slice] using
      (typeI_primePower_dyadicSum_insertion hPpos hk t (hlarge t ht))
  have hWattCont : Continuous (fun t ↦
      A₃ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ)) :=
    (hA₃cont.pow 4).mul (hA₂cont.pow 2)
  have hWattRestrict :
      (∫ t in E, A₃ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ)) ≤
        ∫ t in Set.Icc T (2 * T),
          A₃ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ) := by
    apply setIntegral_mono_set hWattCont.integrableOn_Icc
    · exact Filter.Eventually.of_forall fun t ↦ by positivity
    · exact Filter.Eventually.of_forall hEsub
  have hWattMoment :
      (∫ t in E, A₃ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ)) ≤ W := by
    refine hWattRestrict.trans ?_
    simpa [A₃, A₂, W] using hWattFull
  have hsliceMoment' : ∀ j ∈ Finset.range k,
      (∫ t in E,
        A₁ t ^ (4 : ℕ) * A₂ t ^ (2 : ℕ) *
          Slice j t ^ (2 : ℕ)) ≤ R j := by
    intro j hj
    simpa [A₁, A₂, Slice] using hsliceMoment j hj
  have hassembled := finiteSlice_typeIOverII_inserted_cauchy
    (Finset.range k) hE hEsub hKnonneg hA₁cont hA₂cont hA₃cont
    hSliceCont hA₂nonneg hSliceNonneg hinsert hWattMoment hsliceMoment'
  refine ⟨C_Watt, hC_Watt, ?_⟩
  simpa [A₁, A₂, A₃, Slice, K, W] using hassembled

/-- The literal Lemma 3.2 majorant for slice `j`, with the canonical
collected zero-line coefficient and its exact energy. -/
def typeIOverIICompositePrimeSliceMeanMajorant
    (C_MV : ℝ) (alpha beta : ℕ → ℂ)
    (P M₁ M₂ T : ℝ) (k j : ℕ) : ℝ :=
  let Q : ℝ := (2 : ℝ) ^ j * P ^ k
  typeIOverIIMeanSquareMajorant C_MV
    (typeIOverIICompositeSliceLength M₁ M₂ Q) T
    (typeIOverIICompositeSliceLineZeroCoefficient alpha beta
      (rawPrimePowerCoefficient (dyadicPrimes P) k) M₁ M₂ Q)

/-- Complete source-closed Type-I/II finite-slice bound.  Both Watt and
MT23, Lemma 3.2 are now instantiated, and the latter appears through its
actual collected coefficient energy rather than an arbitrary placeholder. -/
theorem typeIOverII_primePower_finiteSliceAssembly
    (hWatt : MatomakiTeravainenLemmaThreeFivePartOneStatement)
    (hMV : MatomakiTeravainenLemmaThreeTwoStatement)
    {eta epsilon P M₁ M₂ N N' T : ℝ} {k : ℕ}
    {alpha beta : ℕ → ℂ} {E : Set ℝ}
    (heta : 0 < eta) (hP : 1 ≤ P) (hk : 1 ≤ k)
    (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (hN : 1 ≤ N) (hN' : 1 ≤ N')
    (hT : 1 ≤ T) (hNN' : N < N') (hN'two : N' ≤ 2 * N)
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc T (2 * T))
    (hlarge : ∀ t ∈ E,
      P ^ (-epsilon / 10) ≤
        ‖primeDirichletPolynomial P (onePlusIT t)‖) :
    ∃ C_Watt C_MV : ℝ, 0 < C_Watt ∧ 0 < C_MV ∧
      (∫ t in E,
        ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖dyadicDirichletPolynomial beta M₂ (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖matomakiTeravainenZetaSegmentPolynomial N N'
            (onePlusIT t)‖ ^ (2 : ℕ)) ≤
        ((P ^ (-epsilon / 10)) ^ k)⁻¹ *
          ((typeIOverIIWattMajorant C_Watt eta M₂ N N' T beta) ^
              (1 / 2 : ℝ) *
            (((k : ℝ) * ∑ j ∈ Finset.range k,
              typeIOverIICompositePrimeSliceMeanMajorant
                C_MV alpha beta P M₁ M₂ T k j) ^
              (1 / 2 : ℝ))) := by
  obtain ⟨C_MV, hC_MV, hmean⟩ :=
    typeIOverII_compositeSliceMeanValue_le_of_matomakiTeravainen hMV
  let R : ℕ → ℝ := fun j ↦
    typeIOverIICompositePrimeSliceMeanMajorant
      C_MV alpha beta P M₁ M₂ T k j
  have hscaleOne : ∀ j ∈ Finset.range k,
      1 ≤ (2 : ℝ) ^ j * P ^ k := by
    intro j hj
    have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hPpow : (1 : ℝ) ≤ P ^ k := one_le_pow₀ hP
    nlinarith [mul_le_mul htwo hPpow (by positivity) (by positivity)]
  have hsliceMoment : ∀ j ∈ Finset.range k,
      (∫ t in E,
        ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (4 : ℕ) *
          ‖dyadicDirichletPolynomial beta M₂ (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖dyadicDirichletPolynomial
            (rawPrimePowerCoefficient (dyadicPrimes P) k)
            ((2 : ℝ) ^ j * P ^ k) (onePlusIT t)‖ ^ (2 : ℕ)) ≤
        R j := by
    intro j hj
    let q : ℕ → ℂ := rawPrimePowerCoefficient (dyadicPrimes P) k
    let Q : ℝ := (2 : ℝ) ^ j * P ^ k
    let weight : ℝ → ℝ := fun t ↦
      ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (4 : ℕ) *
        ‖dyadicDirichletPolynomial beta M₂ (onePlusIT t)‖ ^ (2 : ℕ) *
        ‖dyadicDirichletPolynomial q Q (onePlusIT t)‖ ^ (2 : ℕ)
    have hweightCont : Continuous weight :=
      ((((Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
        alpha M₁).norm.pow 4).mul
        ((Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
          beta M₂).norm.pow 2)).mul
        ((Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
          q Q).norm.pow 2))
    have hrestrict :
        (∫ t in E, weight t) ≤ ∫ t in Set.Icc T (2 * T), weight t := by
      apply setIntegral_mono_set hweightCont.integrableOn_Icc
      · exact Filter.Eventually.of_forall fun t ↦ by positivity
      · exact Filter.Eventually.of_forall hEsub
    have hfull := hmean alpha beta q M₁ M₂ Q T
      hM₁ hM₂ (by simpa [Q] using hscaleOne j hj) hT
    change (∫ t in E, weight t) ≤ R j
    refine hrestrict.trans ?_
    simpa [weight, q, Q, R, typeIOverIICompositePrimeSliceMeanMajorant]
      using hfull
  obtain ⟨C_Watt, hC_Watt, hassembled⟩ :=
    typeIOverII_primePower_finiteSliceAssembly_of_moments hWatt
      heta hP hk hM₂ hN hN' hT hNN' hN'two hE hEsub hlarge hsliceMoment
  exact ⟨C_Watt, C_MV, hC_Watt, hC_MV, by simpa [R] using hassembled⟩

/-- Concrete non-vacuous coefficient-energy estimate.  Its
right-hand side is the elementary support length times the square of a
uniform divisor-subpower coefficient bound, divided by the square of the
minimum product scale. -/
def TypeIOverIICompositeSliceEnergyEnvelopeStatement : Prop :=
  ∀ B₀ rho : ℝ, ∀ k : ℕ,
    0 ≤ B₀ → 0 < rho → 1 ≤ k →
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ (alpha beta : ℕ → ℂ) (A₀ M₁ M₂ P : ℝ) (j : ℕ),
        1 ≤ A₀ → 1 ≤ M₁ → 1 ≤ M₂ → 1 ≤ P →
        IsDivisorBoundedByConstant B₀ A₀ alpha →
        IsDivisorBoundedByConstant B₀ A₀ beta →
        let Q : ℝ := (2 : ℝ) ^ j * P ^ k
        let length : ℝ := typeIOverIICompositeSliceLength M₁ M₂ Q
        typeIOverIICompositeSliceEnergy alpha beta
            (rawPrimePowerCoefficient (dyadicPrimes P) k) M₁ M₂ Q ≤
          length *
            ((A₀ ^ (3 : ℕ) * (k.factorial : ℝ) * D * length ^ rho) /
              (M₁ ^ (2 : ℕ) * M₂ * Q)) ^ (2 : ℕ)

/-- The residual energy envelope is elementary once the nested convolution
coefficient has been given its explicit divisor bound.  In particular, the
constant `D` constructed here depends only on the displayed divisor exponent
and `rho`, never on `k`, either coefficient sequence, or a scale. -/
theorem typeIOverIICompositeSliceEnergyEnvelope :
    TypeIOverIICompositeSliceEnergyEnvelopeStatement := by
  intro B₀ rho k hB₀ hrho hk
  obtain ⟨D, hD, hcoefficient⟩ :=
    exists_uniform_typeIOverIICompositeSliceCoefficient_bound_subpower
      (k := k) hB₀ hrho
  refine ⟨D, hD, ?_⟩
  intro alpha beta A₀ M₁ M₂ P j hA₀ hM₁ hM₂ hP halpha hbeta
  dsimp only
  have hM₁pos : 0 < M₁ := zero_lt_one.trans_le hM₁
  have hM₂pos : 0 < M₂ := zero_lt_one.trans_le hM₂
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hQpos : 0 < (2 : ℝ) ^ j * P ^ k := by positivity
  let B : ℝ := A₀ ^ (3 : ℕ) * (k.factorial : ℝ) * D *
    (typeIOverIICompositeSliceLength M₁ M₂
      ((2 : ℝ) ^ j * P ^ k)) ^ rho
  have hB : 0 ≤ B := by
    dsimp [B]
    have hlength : 0 ≤ typeIOverIICompositeSliceLength M₁ M₂
        ((2 : ℝ) ^ j * P ^ k) := by
      unfold typeIOverIICompositeSliceLength
      positivity
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (pow_nonneg (zero_le_one.trans hA₀) 3) (Nat.cast_nonneg _))
        (zero_le_one.trans hD))
      (Real.rpow_nonneg hlength rho)
  have hcoeff : ∀ n ∈ typeIOverIICompositeSliceSupport M₁ M₂
      ((2 : ℝ) ^ j * P ^ k),
      ‖typeIOverIICompositeSliceCoefficient alpha beta
          (rawPrimePowerCoefficient (dyadicPrimes P) k)
          M₁ M₂ ((2 : ℝ) ^ j * P ^ k) n‖ ≤ B := by
    intro n hn
    exact hcoefficient alpha beta A₀ M₁ M₂ P j
      hA₀ hM₁ hM₂ hP halpha hbeta n hn
  have henergy := typeIOverIICompositeSliceEnergy_le_of_coefficient_bound
    hM₁pos hM₂pos hQpos hB hcoeff
  simpa [B] using henergy

def typeIOverIIFiniteSliceClosureModule : ProofModule :=
  { name := "Completion.TypeIOverIIFiniteSliceClosure"
    paperLocation := "MT23 Section 5.2, Type-I/II finite-slice insertion"
    purpose :=
      "Carry the full sum of prime-power dyadic slices through Type-I/II Cauchy--Schwarz, apply Watt and MT23 Lemma 3.2 uniformly, and prove the explicit collected coefficient-energy envelope."
    dependsOn :=
      [ "Completion.FiniteSliceInsertedCauchy",
        "Completion.TypeIOverIIClosure",
        "Completion.TypeIPrimePowerEnergy",
        "Completion.TypeIOverIICompositeMeanValue" ]
    status := .proved }

end

end Completion
end ExactSemiprimes
