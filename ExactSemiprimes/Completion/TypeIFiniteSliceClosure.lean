import ExactSemiprimes.Completion.FiniteSliceInsertedCauchy

/-!
# Type-I finite-slice closure

This module instantiates the deterministic finite-slice insertion theorem
with the exact dyadic pieces of the raw prime-polynomial power.  A single
constant from MT23, Lemma 3.5(ii) is used uniformly for every slice.  MT23,
Lemma 3.2 supplies the long-factor fourth moment.

The result proves the formerly isolated
`TypeIPrimePowerFiniteSliceAssemblyStatement`.  It stops at the literal
sum of source majorants; no unavailable scale relation is inferred.
-/

namespace ExactSemiprimes
namespace Completion

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Source-closed finite-slice assembly for a Type-I component. -/
theorem typeI_primePower_finiteSliceAssembly :
    TypeIPrimePowerFiniteSliceAssemblyStatement := by
  intro hDI hMV eta epsilon P N N' T M₁ k alpha E
    heta hP hk hN hN' hT hM₁ hNN' hN'two hE hEsub hlarge
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  obtain ⟨C_DI, hC_DI, hDIall⟩ := hDI eta heta
  obtain ⟨C_MV, hC_MV, hlongFull⟩ :=
    typeI_longFourthMoment_le_of_matomakiTeravainen hMV
  let coeff : ℕ → ℂ := rawPrimePowerCoefficient (dyadicPrimes P) k
  let scale : ℕ → ℝ := fun j ↦ (2 : ℝ) ^ j * P ^ k
  let Long : ℝ → ℝ := fun t ↦
    ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖
  let Short : ℝ → ℝ := fun t ↦
    ‖matomakiTeravainenZetaSegmentPolynomial N N' (onePlusIT t)‖
  let Slice : ℕ → ℝ → ℝ := fun j t ↦
    ‖dyadicDirichletPolynomial coeff (scale j) (onePlusIT t)‖
  let K : ℝ := ((P ^ (-epsilon / 10)) ^ k)⁻¹
  let L : ℝ :=
    (4 * T + C_MV * (2 * M₁) ^ (2 : ℕ)) *
      TypeII.poweredLineOneEnergy alpha M₁ 2
  let R : ℕ → ℝ := fun j ↦
    typeIDIMajorant C_DI eta (scale j) N N' T coeff
  have hscaleOne : ∀ j ∈ Finset.range k, 1 ≤ scale j := by
    intro j hj
    have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hPpow : (1 : ℝ) ≤ P ^ k := one_le_pow₀ hP
    dsimp [scale]
    nlinarith [mul_le_mul htwo hPpow (by positivity) (by positivity)]
  have hLongCont : Continuous Long :=
    (Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
      alpha M₁).norm
  have hShortCont : Continuous Short := by
    dsimp [Short]
    exact (Sparse.continuous_dirichletPolynomial_onePlusIT_sparse
      (fun _ ↦ 1) (natOpenClosedInterval N N')).norm
  have hSliceCont : ∀ j ∈ Finset.range k, Continuous (Slice j) := by
    intro j hj
    exact (Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
      coeff (scale j)).norm
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
    simpa [K, Slice, scale, coeff] using
      (typeI_primePower_dyadicSum_insertion hPpos hk t (hlarge t ht))
  have hlongContFourth : Continuous (fun t ↦ Long t ^ (4 : ℕ)) :=
    hLongCont.pow 4
  have hlongRestrict :
      (∫ t in E, Long t ^ (4 : ℕ)) ≤
        ∫ t in Set.Icc T (2 * T), Long t ^ (4 : ℕ) := by
    apply setIntegral_mono_set hlongContFourth.integrableOn_Icc
    · exact Filter.Eventually.of_forall fun t ↦ by positivity
    · exact Filter.Eventually.of_forall hEsub
  have hlongMoment : (∫ t in E, Long t ^ (4 : ℕ)) ≤ L := by
    refine hlongRestrict.trans ?_
    simpa [Long, L] using hlongFull alpha M₁ T hM₁ hT
  have h2T : 1 ≤ 2 * T := by linarith
  have hsliceFull : ∀ j ∈ Finset.range k,
      (∫ t in Set.Icc T (2 * T),
        Short t ^ (4 : ℕ) * Slice j t ^ (2 : ℕ)) ≤ R j := by
    intro j hj
    have hsource := hDIall (scale j) N N' (2 * T) coeff
      (hscaleOne j hj) hN hN' h2T hNN' hN'two
    simpa [Short, Slice, R, scale, coeff,
      matomakiTeravainenTwistedFourthMoment,
      dyadicDirichletPolynomial, typeIDIMajorant] using hsource
  have hsliceMoment : ∀ j ∈ Finset.range k,
      (∫ t in E, Short t ^ (4 : ℕ) * Slice j t ^ (2 : ℕ)) ≤
        R j := by
    intro j hj
    have hweightCont : Continuous (fun t ↦
        Short t ^ (4 : ℕ) * Slice j t ^ (2 : ℕ)) :=
      (hShortCont.pow 4).mul ((hSliceCont j hj).pow 2)
    have hrestrict :
        (∫ t in E, Short t ^ (4 : ℕ) * Slice j t ^ (2 : ℕ)) ≤
          ∫ t in Set.Icc T (2 * T),
            Short t ^ (4 : ℕ) * Slice j t ^ (2 : ℕ) := by
      apply setIntegral_mono_set hweightCont.integrableOn_Icc
      · exact Filter.Eventually.of_forall fun t ↦ by positivity
      · exact Filter.Eventually.of_forall hEsub
    exact hrestrict.trans (hsliceFull j hj)
  have hassembled := finiteSlice_inserted_cauchy
    (Finset.range k) hE hEsub hKnonneg hLongCont hShortCont
    hSliceCont hSliceNonneg hinsert hlongMoment hsliceMoment
  refine ⟨C_DI, C_MV, hC_DI, hC_MV, ?_⟩
  simpa [Long, Short, Slice, K, L, R, scale, coeff] using hassembled

/-! ## Substitution of the proved prime-power coefficient energy -/

/-- The DI majorant with its averaged coefficient energy replaced by an
explicit upper bound `energy / A`. -/
def typeIDIMajorantEnergyEnvelope
    (C eta A N _N' T energy : ℝ) : ℝ :=
  C * (2 * T) ^ eta *
    ((((2 * T) + A ^ (2 : ℕ) * (2 * T) ^ (1 / 2 : ℝ) +
          A ^ (5 / 4 : ℝ) * (2 * T) ^ (3 / 4 : ℝ)) /
          (N ^ (2 : ℕ) * A) +
        ((2 * T) + A) / ((2 * T) ^ (4 : ℕ) * A)) *
      (energy / A))

/-- Equation (5.4), already proved combinatorially in
`TypeIPrimePowerEnergy`, may be substituted directly into every literal DI
majorant. -/
theorem typeIDIMajorant_rawPrimePower_le_energyEnvelope
    {C eta A N N' T : ℝ} {S : Finset ℕ} {k : ℕ}
    (hC : 0 ≤ C) (hA : 0 < A) (hN : 0 < N) (hT : 0 < T)
    (hS : ∀ p ∈ S, Nat.Prime p) :
    typeIDIMajorant C eta A N N' T (rawPrimePowerCoefficient S k) ≤
      typeIDIMajorantEnergyEnvelope C eta A N N' T
        ((k.factorial : ℝ) * (S.card : ℝ) ^ k) := by
  have havg := rawPrimePowerCoefficient_dyadicAverage_le
    (S := S) (k := k) hS hA
  have hfront : 0 ≤ C * (2 * T) ^ eta := by positivity
  have hmiddle : 0 ≤
      (((2 * T) + A ^ (2 : ℕ) * (2 * T) ^ (1 / 2 : ℝ) +
          A ^ (5 / 4 : ℝ) * (2 * T) ^ (3 / 4 : ℝ)) /
          (N ^ (2 : ℕ) * A) +
        ((2 * T) + A) / ((2 * T) ^ (4 : ℕ) * A)) := by
    positivity
  unfold typeIDIMajorant typeIDIMajorantEnergyEnvelope
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left havg hmiddle) hfront

/-- Finite-slice assembly after substituting the sharp `k! |S|^k`
coefficient-energy estimate into every DI slice.  This is the strongest
literal source bound available before the paper-specific scale relations
are supplied. -/
theorem typeI_primePower_finiteSliceAssembly_energy
    (hDI : MatomakiTeravainenLemmaThreeFivePartTwoStatement)
    (hMV : MatomakiTeravainenLemmaThreeTwoStatement)
    {eta epsilon P N N' T M₁ : ℝ} {k : ℕ}
    {alpha : ℕ → ℂ} {E : Set ℝ}
    (heta : 0 < eta) (hP : 1 ≤ P) (hk : 1 ≤ k)
    (hN : 1 ≤ N) (hN' : 1 ≤ N') (hT : 1 ≤ T) (hM₁ : 1 ≤ M₁)
    (hNN' : N < N') (hN'two : N' ≤ 2 * N)
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc T (2 * T))
    (hlarge : ∀ t ∈ E,
      P ^ (-epsilon / 10) ≤
        ‖primeDirichletPolynomial P (onePlusIT t)‖) :
    ∃ C_DI C_MV : ℝ, 0 < C_DI ∧ 0 < C_MV ∧
      (∫ t in E,
        ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖matomakiTeravainenZetaSegmentPolynomial N N'
            (onePlusIT t)‖ ^ (2 : ℕ)) ≤
        ((P ^ (-epsilon / 10)) ^ k)⁻¹ *
          ((((k : ℝ) *
              ∑ j ∈ Finset.range k,
                typeIDIMajorantEnergyEnvelope C_DI eta
                  ((2 : ℝ) ^ j * P ^ k) N N' T
                  ((k.factorial : ℝ) *
                    ((dyadicPrimes P).card : ℝ) ^ k)) ^
                (1 / 2 : ℝ)) *
            (((4 * T + C_MV * (2 * M₁) ^ (2 : ℕ)) *
                TypeII.poweredLineOneEnergy alpha M₁ 2) ^
              (1 / 2 : ℝ))) := by
  obtain ⟨C_DI, C_MV, hC_DI, hC_MV, hraw⟩ :=
    typeI_primePower_finiteSliceAssembly hDI hMV eta epsilon P N N' T M₁
      k alpha E heta hP hk hN hN' hT hM₁ hNN' hN'two hE hEsub hlarge
  refine ⟨C_DI, C_MV, hC_DI, hC_MV, ?_⟩
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hSprime : ∀ p ∈ dyadicPrimes P, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hscalePos : ∀ j : ℕ, 0 < (2 : ℝ) ^ j * P ^ k := by
    intro j
    positivity
  have hsum :
      (∑ j ∈ Finset.range k,
          typeIDIMajorant C_DI eta ((2 : ℝ) ^ j * P ^ k) N N' T
            (rawPrimePowerCoefficient (dyadicPrimes P) k)) ≤
        ∑ j ∈ Finset.range k,
          typeIDIMajorantEnergyEnvelope C_DI eta
            ((2 : ℝ) ^ j * P ^ k) N N' T
            ((k.factorial : ℝ) * ((dyadicPrimes P).card : ℝ) ^ k) := by
    apply Finset.sum_le_sum
    intro j hj
    exact typeIDIMajorant_rawPrimePower_le_energyEnvelope
      hC_DI.le (hscalePos j) hNpos hTpos hSprime
  have hmajorantNonneg : ∀ j : ℕ,
      0 ≤ typeIDIMajorant C_DI eta ((2 : ℝ) ^ j * P ^ k) N N' T
        (rawPrimePowerCoefficient (dyadicPrimes P) k) := by
    intro j
    unfold typeIDIMajorant
    positivity
  have hbaseNonneg : 0 ≤
      (k : ℝ) *
        ∑ j ∈ Finset.range k,
          typeIDIMajorant C_DI eta ((2 : ℝ) ^ j * P ^ k) N N' T
            (rawPrimePowerCoefficient (dyadicPrimes P) k) := by
    apply mul_nonneg (Nat.cast_nonneg k)
    exact Finset.sum_nonneg fun j hj ↦ hmajorantNonneg j
  have hbase :
      (k : ℝ) *
          ∑ j ∈ Finset.range k,
            typeIDIMajorant C_DI eta ((2 : ℝ) ^ j * P ^ k) N N' T
              (rawPrimePowerCoefficient (dyadicPrimes P) k) ≤
        (k : ℝ) *
          ∑ j ∈ Finset.range k,
            typeIDIMajorantEnergyEnvelope C_DI eta
              ((2 : ℝ) ^ j * P ^ k) N N' T
              ((k.factorial : ℝ) * ((dyadicPrimes P).card : ℝ) ^ k) :=
    mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg k)
  have hhalf := Real.rpow_le_rpow hbaseNonneg hbase
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hKnonneg : 0 ≤ ((P ^ (-epsilon / 10)) ^ k)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (Real.rpow_nonneg hPpos.le _) k)
  have hlongHalfNonneg : 0 ≤
      ((4 * T + C_MV * (2 * M₁) ^ (2 : ℕ)) *
        TypeII.poweredLineOneEnergy alpha M₁ 2) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (by
      unfold TypeII.poweredLineOneEnergy
      positivity) _
  refine hraw.trans (mul_le_mul_of_nonneg_left ?_ hKnonneg)
  exact mul_le_mul_of_nonneg_right hhalf hlongHalfNonneg

/-- Explicit long-factor envelope obtained from the proved uniform
divisor-subpower convolution estimate. -/
def typeILongFourthSubpowerEnvelope
    (C D rho M T A₀ : ℝ) : ℝ :=
  (4 * T + C * (2 * M) ^ (2 : ℕ)) *
    ((2 * M) ^ (2 : ℕ) *
      ((A₀ ^ (2 : ℕ) * D * ((2 * M) ^ (2 : ℕ)) ^ rho) /
        M ^ (2 : ℕ)) ^ (2 : ℕ))

/-- Fully explicit coefficient-energy form of the source-closed
finite-slice estimate: the prime-power energy uses `k! |S|^k`, while the
long divisor-bounded factor uses a uniform subpower convolution bound. -/
theorem typeI_primePower_finiteSliceAssembly_divisorBounded
    (hDI : MatomakiTeravainenLemmaThreeFivePartTwoStatement)
    (hMV : MatomakiTeravainenLemmaThreeTwoStatement)
    {B₀ rho eta epsilon P N N' T M₁ A₀ : ℝ} {k : ℕ}
    {alpha : ℕ → ℂ} {E : Set ℝ}
    (hB₀ : 0 ≤ B₀) (hrho : 0 < rho)
    (heta : 0 < eta) (hP : 1 ≤ P) (hk : 1 ≤ k)
    (hN : 1 ≤ N) (hN' : 1 ≤ N') (hT : 1 ≤ T) (hM₁ : 1 ≤ M₁)
    (hNN' : N < N') (hN'two : N' ≤ 2 * N)
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc T (2 * T))
    (halpha : IsDivisorBoundedByConstant B₀ A₀ alpha)
    (hlarge : ∀ t ∈ E,
      P ^ (-epsilon / 10) ≤
        ‖primeDirichletPolynomial P (onePlusIT t)‖) :
    ∃ C_DI C_MV D : ℝ,
      0 < C_DI ∧ 0 < C_MV ∧ 1 ≤ D ∧
      (∫ t in E,
        ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖matomakiTeravainenZetaSegmentPolynomial N N'
            (onePlusIT t)‖ ^ (2 : ℕ)) ≤
        ((P ^ (-epsilon / 10)) ^ k)⁻¹ *
          ((((k : ℝ) *
              ∑ j ∈ Finset.range k,
                typeIDIMajorantEnergyEnvelope C_DI eta
                  ((2 : ℝ) ^ j * P ^ k) N N' T
                  ((k.factorial : ℝ) *
                    ((dyadicPrimes P).card : ℝ) ^ k)) ^
                (1 / 2 : ℝ)) *
            (typeILongFourthSubpowerEnvelope C_MV D rho M₁ T A₀ ^
              (1 / 2 : ℝ))) := by
  obtain ⟨C_DI, C_MV, hC_DI, hC_MV, hraw⟩ :=
    typeI_primePower_finiteSliceAssembly_energy hDI hMV heta hP hk hN hN'
      hT hM₁ hNN' hN'two hE hEsub hlarge
  obtain ⟨D, hD, hcoeff⟩ :=
    TypeII.exists_uniform_powerConvolution_bound_subpower
      hB₀ (ell := 2) (by norm_num) hrho
  refine ⟨C_DI, C_MV, D, hC_DI, hC_MV, hD, ?_⟩
  have hM₁pos : 0 < M₁ := zero_lt_one.trans_le hM₁
  have hA₀nonneg : 0 ≤ A₀ := halpha.2.1.le
  have hDnonneg : 0 ≤ D := zero_le_one.trans hD
  have hconvBound : 0 ≤
      A₀ ^ (2 : ℕ) * D * ((2 * M₁) ^ (2 : ℕ)) ^ rho := by
    positivity
  have henergy := TypeII.poweredLineOneEnergy_le_of_convolution_bound
    hM₁pos hconvBound (hcoeff alpha M₁ A₀ hM₁pos halpha)
  have hprefactor : 0 ≤ 4 * T + C_MV * (2 * M₁) ^ (2 : ℕ) := by
    positivity
  have hlong :
      (4 * T + C_MV * (2 * M₁) ^ (2 : ℕ)) *
          TypeII.poweredLineOneEnergy alpha M₁ 2 ≤
        typeILongFourthSubpowerEnvelope C_MV D rho M₁ T A₀ := by
    unfold typeILongFourthSubpowerEnvelope
    exact mul_le_mul_of_nonneg_left henergy hprefactor
  have hlongBaseNonneg : 0 ≤
      (4 * T + C_MV * (2 * M₁) ^ (2 : ℕ)) *
        TypeII.poweredLineOneEnergy alpha M₁ 2 := by
    unfold TypeII.poweredLineOneEnergy
    positivity
  have hlongHalf := Real.rpow_le_rpow hlongBaseNonneg hlong
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hKnonneg : 0 ≤ ((P ^ (-epsilon / 10)) ^ k)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (Real.rpow_nonneg hPpos.le _) k)
  have henvelopeNonneg : ∀ j : ℕ,
      0 ≤ typeIDIMajorantEnergyEnvelope C_DI eta
        ((2 : ℝ) ^ j * P ^ k) N N' T
        ((k.factorial : ℝ) * ((dyadicPrimes P).card : ℝ) ^ k) := by
    intro j
    unfold typeIDIMajorantEnergyEnvelope
    positivity
  have hfirstBaseNonneg : 0 ≤
      (k : ℝ) *
        ∑ j ∈ Finset.range k,
          typeIDIMajorantEnergyEnvelope C_DI eta
            ((2 : ℝ) ^ j * P ^ k) N N' T
            ((k.factorial : ℝ) * ((dyadicPrimes P).card : ℝ) ^ k) := by
    apply mul_nonneg (Nat.cast_nonneg k)
    exact Finset.sum_nonneg fun j hj ↦ henvelopeNonneg j
  have hfirstHalfNonneg : 0 ≤
      (((k : ℝ) *
          ∑ j ∈ Finset.range k,
            typeIDIMajorantEnergyEnvelope C_DI eta
              ((2 : ℝ) ^ j * P ^ k) N N' T
              ((k.factorial : ℝ) * ((dyadicPrimes P).card : ℝ) ^ k)) ^
        (1 / 2 : ℝ)) := Real.rpow_nonneg hfirstBaseNonneg _
  refine hraw.trans (mul_le_mul_of_nonneg_left ?_ hKnonneg)
  exact mul_le_mul_of_nonneg_left hlongHalf hfirstHalfNonneg

def typeIFiniteSliceClosureModule : ProofModule :=
  { name := "Completion.TypeIFiniteSliceClosure"
    paperLocation := "MT23 Section 5.1, Type-I finite-slice insertion"
    purpose :=
      "Prove the quantifier-correct Type-I finite-slice assembly using one uniform Lemma 3.5(ii) constant, the exact cardinality loss, and the Lemma 3.2 long moment."
    dependsOn :=
      [ "Completion.FiniteSliceInsertedCauchy",
        "Completion.TypeIPrimePowerEnergy",
        "Completion.TypeIFirstFactorMoment" ]
    status := .proved }

end

end Completion
end ExactSemiprimes
