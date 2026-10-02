import ExactSemiprimes.Completion.TypeIClosure
import ExactSemiprimes.Completion.TypeIPrimePowerEnergy
import ExactSemiprimes.Completion.TypeIFirstFactorMoment
import ExactSemiprimes.Sparse.GlobalComponentCancellation

/-!
# Source-closed Type-I component reduction

This file separates the Type-I part of the final component assembly into
three logically independent layers.

* The source convolution is identified exactly with the product of its two
  finite Dirichlet polynomials.
* Matomaki--Teravainen Lemma 3.5(ii), in the normalization already recorded
  in `Assumptions`, is specialized from `[T/2,T]` to the block `[T,2T]`.
* The pointwise insertion and Cauchy--Schwarz step of MT23, Section 5.1 is
  proved as a deterministic integral inequality.

The only remaining analytic Type-I obligation is stated at the end as an
exact local proposition.  It is not an additional assumption.  It records
the finite-slice assembly required because the pointwise prime-power
insertion produces a sum of slices, not one slice uniform in the height.
The coefficient energy and the long-factor fourth moment are proved here or
in imported completion modules.  Final power absorption would additionally
need component-scale relations that this representation interface does not
record; the main theorem uses the labelled extension E4 instead.
-/

namespace ExactSemiprimes
namespace Completion

open MeasureTheory
open scoped BigOperators

noncomputable section

/-! ## Exact factorization of a source Type-I component -/

def typeIFirstSupport (M₁ : ℝ) : Finset ℕ :=
  dyadicInterval M₁

def typeISecondSupport (delta M₂ : ℝ) : Finset ℕ :=
  natOpenClosedInterval M₂ ((1 + delta) * M₂)

def typeIRangePairs (delta M₁ M₂ : ℝ) (n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter
    (fun p ↦ p.1 * p.2 = n ∧ InDyadicRange M₁ p.1 ∧
      M₂ < (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ (1 + delta) * M₂)

def typeISupportPairs (delta M₁ M₂ : ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  ((typeIFirstSupport M₁).product (typeISecondSupport delta M₂)).filter
    (fun p ↦ p.1 * p.2 = n)

theorem mem_typeIFirstSupport_iff {M₁ : ℝ} {m : ℕ} (hM₁ : 0 < M₁) :
    m ∈ typeIFirstSupport M₁ ↔ InDyadicRange M₁ m := by
  exact mem_dyadicInterval hM₁.le

theorem mem_typeISecondSupport_iff
    {delta M₂ : ℝ} {m : ℕ} (hdelta : 0 ≤ delta) (hM₂ : 0 < M₂) :
    m ∈ typeISecondSupport delta M₂ ↔
      M₂ < (m : ℝ) ∧ (m : ℝ) ≤ (1 + delta) * M₂ := by
  apply mem_natOpenClosedInterval hM₂.le
  exact mul_nonneg (by linarith) hM₂.le

theorem typeI_pair_filter_eq
    {delta M₁ M₂ : ℝ} {n : ℕ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) :
    typeIRangePairs delta M₁ M₂ n = typeISupportPairs delta M₁ M₂ n := by
  classical
  ext p
  simp only [typeIRangePairs, typeISupportPairs]
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hpairs, hprod, hp₁, hp₂low, hp₂up⟩
    exact ⟨Finset.mem_product.mpr
      ⟨(mem_typeIFirstSupport_iff hM₁).2 hp₁,
        (mem_typeISecondSupport_iff hdelta hM₂).2 ⟨hp₂low, hp₂up⟩⟩,
      hprod⟩
  · rintro ⟨hpairs, hprod⟩
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hpairs
    have hp₁data := (mem_typeIFirstSupport_iff hM₁).1 hp₁
    have hp₂data := (mem_typeISecondSupport_iff hdelta hM₂).1 hp₂
    have hp₁posReal : 0 < (p.1 : ℝ) := hM₁.trans hp₁data.1
    have hp₂posReal : 0 < (p.2 : ℝ) := hM₂.trans hp₂data.1
    have hp₁pos : 0 < p.1 := by exact_mod_cast hp₁posReal
    have hp₂pos : 0 < p.2 := by exact_mod_cast hp₂posReal
    have hnpos : 0 < n := by
      rw [← hprod]
      exact Nat.mul_pos hp₁pos hp₂pos
    have hp₁le : p.1 ≤ n :=
      Nat.le_of_dvd hnpos ⟨p.2, hprod.symm⟩
    have hp₂le : p.2 ≤ n := Nat.le_of_dvd hnpos ⟨p.1, by
      rw [mul_comm]
      exact hprod.symm⟩
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩,
      hprod, hp₁data, hp₂data.1, hp₂data.2⟩

theorem matomakiTeravainenTypeIValue_eq_binaryConvolution
    {delta M₁ M₂ : ℝ} {alpha : ℕ → ℂ} {n : ℕ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) :
    matomakiTeravainenTypeIValue delta M₁ M₂ alpha n =
      Sparse.binaryConvolutionCoefficient alpha (fun _ ↦ 1)
        (typeIFirstSupport M₁) (typeISecondSupport delta M₂) n := by
  classical
  rw [matomakiTeravainenTypeIValue, Sparse.binaryConvolutionCoefficient]
  rw [← Finset.sum_product']
  change (∑ p ∈ (Finset.range (n + 1)).product (Finset.range (n + 1)),
      if p.1 * p.2 = n ∧ InDyadicRange M₁ p.1 ∧
          M₂ < (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ (1 + delta) * M₂ then
        alpha p.1
      else 0) = _
  rw [← Finset.sum_filter]
  change (∑ p ∈ typeIRangePairs delta M₁ M₂ n, alpha p.1) = _
  rw [typeI_pair_filter_eq hdelta hM₁ hM₂]
  simp [typeISupportPairs]

/-- The polynomial generated on the literal product support by a source
Type-I convolution is exactly its dyadic coefficient factor times its short
unit-coefficient segment. -/
theorem matomakiTeravainenTypeI_polynomial_factorization
    {delta M₁ M₂ : ℝ} {alpha : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (s : ℂ) :
    dirichletPolynomial
        (matomakiTeravainenTypeIValue delta M₁ M₂ alpha)
        (Sparse.typeIProductSupport delta M₁ M₂) s =
      dyadicDirichletPolynomial alpha M₁ s *
        matomakiTeravainenZetaSegmentPolynomial M₂
          ((1 + delta) * M₂) s := by
  rw [dyadicDirichletPolynomial,
    matomakiTeravainenZetaSegmentPolynomial]
  symm
  calc
    dirichletPolynomial alpha (typeIFirstSupport M₁) s *
          dirichletPolynomial (fun _ ↦ 1) (typeISecondSupport delta M₂) s =
        dirichletPolynomial
          (Sparse.binaryConvolutionCoefficient alpha (fun _ ↦ 1)
            (typeIFirstSupport M₁) (typeISecondSupport delta M₂))
          (((typeIFirstSupport M₁).product
            (typeISecondSupport delta M₂)).image fun p ↦ p.1 * p.2) s :=
      Sparse.dirichletPolynomial_mul_eq_binaryConvolution _ _ _ _ s
    _ = dirichletPolynomial
          (matomakiTeravainenTypeIValue delta M₁ M₂ alpha)
          (Sparse.typeIProductSupport delta M₁ M₂) s := by
      unfold dirichletPolynomial Sparse.typeIProductSupport
      apply Finset.sum_congr rfl
      intro n hn
      rw [matomakiTeravainenTypeIValue_eq_binaryConvolution
        hdelta hM₁ hM₂]

/-- The factorization in the exact representation supplied by MT23,
Proposition 2.2(i). -/
theorem representedTypeI_polynomial_factorization
    {delta M₁ M₂ : ℝ} {alpha f : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hf : ∀ n, f n = matomakiTeravainenTypeIValue delta M₁ M₂ alpha n)
    (s : ℂ) :
    dirichletPolynomial f (Sparse.typeIProductSupport delta M₁ M₂) s =
      dyadicDirichletPolynomial alpha M₁ s *
        matomakiTeravainenZetaSegmentPolynomial M₂
          ((1 + delta) * M₂) s := by
  calc
    dirichletPolynomial f (Sparse.typeIProductSupport delta M₁ M₂) s =
        dirichletPolynomial
          (matomakiTeravainenTypeIValue delta M₁ M₂ alpha)
          (Sparse.typeIProductSupport delta M₁ M₂) s := by
      unfold dirichletPolynomial
      apply Finset.sum_congr rfl
      intro n hn
      rw [hf n]
    _ = _ := matomakiTeravainenTypeI_polynomial_factorization
      hdelta hM₁ hM₂ s

/-! ## Literal block specialization of Lemma 3.5(ii) -/

/-- The source right-hand side of MT23, Lemma 3.5(ii), after replacing its
height variable by `2T`, so that its integration interval is `[T,2T]`. -/
def typeIDIMajorant
    (C eta A N _N' T : ℝ) (b : ℕ → ℂ) : ℝ :=
  C * (2 * T) ^ eta *
    ((((2 * T) + A ^ (2 : ℕ) * (2 * T) ^ (1 / 2 : ℝ) +
          A ^ (5 / 4 : ℝ) * (2 * T) ^ (3 / 4 : ℝ)) /
          (N ^ (2 : ℕ) * A) +
        ((2 * T) + A) / ((2 * T) ^ (4 : ℕ) * A)) *
      ((1 / A) * ∑ m ∈ dyadicInterval A, ‖b m‖ ^ (2 : ℕ)))

/-- Direct, source-closed application of the Deshouillers--Iwaniec input on
the block `[T,2T]`.  No asymptotic simplification is hidden here. -/
theorem typeI_twistedFourthMoment_le_of_matomakiTeravainen
    (hDI : MatomakiTeravainenLemmaThreeFivePartTwoStatement)
    {eta A N N' T : ℝ} {b : ℕ → ℂ}
    (heta : 0 < eta) (hA : 1 ≤ A) (hN : 1 ≤ N) (hN' : 1 ≤ N')
    (hT : 1 ≤ T) (hNN' : N < N') (hN'two : N' ≤ 2 * N) :
    ∃ C : ℝ, 0 < C ∧
      (∫ t in Set.Icc T (2 * T),
        ‖matomakiTeravainenZetaSegmentPolynomial N N' (onePlusIT t)‖ ^
            (4 : ℕ) *
          ‖dyadicDirichletPolynomial b A (onePlusIT t)‖ ^ (2 : ℕ)) ≤
        typeIDIMajorant C eta A N N' T b := by
  obtain ⟨C, hC, hsource⟩ := hDI eta heta
  refine ⟨C, hC, ?_⟩
  have h2T : 1 ≤ 2 * T := by linarith
  have h := hsource A N N' (2 * T) b hA hN hN' h2T hNN' hN'two
  simpa [matomakiTeravainenTwistedFourthMoment,
    dyadicDirichletPolynomial, typeIDIMajorant] using h

/-! ## The pointwise insertion and Cauchy--Schwarz step -/

/-- Abstract deterministic form of the insertion used in MT23, Section 5.1.
The functions are norms of finite Dirichlet polynomials in the application;
the explicit measurability and integrability hypotheses avoid hiding any
analytic regularity in the statement. -/
theorem typeI_integral_le_inserted_cauchy
    {E : Set ℝ} {K : ℝ} {A N B : ℝ → ℝ}
    (hE : MeasurableSet E)
    (hK : 0 ≤ K)
    (hB : ∀ t ∈ E, 0 ≤ B t)
    (hinsert : ∀ t ∈ E, 1 ≤ K * B t)
    (hmeasF : AEStronglyMeasurable (fun t ↦ N t ^ 2 * B t)
      (volume.restrict E))
    (hmeasG : AEStronglyMeasurable (fun t ↦ A t ^ 2)
      (volume.restrict E))
    (hintF : IntegrableOn (fun t ↦ (N t ^ 2 * B t) ^ 2) E)
    (hintG : IntegrableOn (fun t ↦ (A t ^ 2) ^ 2) E)
    (hintLeft : IntegrableOn (fun t ↦ A t ^ 2 * N t ^ 2) E)
    (hintProduct : IntegrableOn
      (fun t ↦ (N t ^ 2 * B t) * (A t ^ 2)) E) :
    (∫ t in E, A t ^ 2 * N t ^ 2) ≤
      K *
        ((∫ t in E, N t ^ 4 * B t ^ 2) ^ (1 / 2 : ℝ) *
          (∫ t in E, A t ^ 4) ^ (1 / 2 : ℝ)) := by
  let F : ℝ → ℝ := fun t ↦ N t ^ 2 * B t
  let G : ℝ → ℝ := fun t ↦ A t ^ 2
  have hFnonneg : 0 ≤ᵐ[volume.restrict E] F := by
    filter_upwards [ae_restrict_mem hE] with t ht
    dsimp [F]
    exact mul_nonneg (sq_nonneg _) (hB t ht)
  have hGnonneg : 0 ≤ᵐ[volume.restrict E] G := by
    filter_upwards [ae_restrict_mem hE] with t ht
    dsimp [G]
    positivity
  have hFmem : MemLp F 2 (volume.restrict E) :=
    (memLp_two_iff_integrable_sq hmeasF).2 hintF
  have hGmem : MemLp G 2 (volume.restrict E) :=
    (memLp_two_iff_integrable_sq hmeasG).2 hintG
  have hFmem' : MemLp F (ENNReal.ofReal 2) (volume.restrict E) := by
    simpa using hFmem
  have hGmem' : MemLp G (ENNReal.ofReal 2) (volume.restrict E) := by
    simpa using hGmem
  have hcauchy := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two hFnonneg hGnonneg hFmem' hGmem'
  have hinserted :
      (∫ t in E, A t ^ 2 * N t ^ 2) ≤
        K * ∫ t in E, F t * G t := by
    calc
      (∫ t in E, A t ^ 2 * N t ^ 2) ≤
          ∫ t in E, K * (F t * G t) := by
        apply setIntegral_mono_on hintLeft (hintProduct.const_mul K) hE
        intro t ht
        have hnonneg : 0 ≤ A t ^ 2 * N t ^ 2 := by positivity
        calc
          A t ^ 2 * N t ^ 2 = (A t ^ 2 * N t ^ 2) * 1 := by ring
          _ ≤ (A t ^ 2 * N t ^ 2) * (K * B t) :=
            mul_le_mul_of_nonneg_left (hinsert t ht) hnonneg
          _ = K * (F t * G t) := by dsimp [F, G]; ring
      _ = K * ∫ t in E, F t * G t := by
        rw [MeasureTheory.integral_const_mul]
  calc
    (∫ t in E, A t ^ 2 * N t ^ 2) ≤
        K * ∫ t in E, F t * G t := hinserted
    _ ≤ K *
        ((∫ t in E, F t ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫ t in E, G t ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hcauchy hK
    _ = K *
        ((∫ t in E, N t ^ 4 * B t ^ 2) ^ (1 / 2 : ℝ) *
          (∫ t in E, A t ^ 4) ^ (1 / 2 : ℝ)) := by
      have hFI : (∫ t in E, F t ^ (2 : ℝ)) =
          ∫ t in E, N t ^ 4 * B t ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp [F]
        rw [Real.rpow_two]
        ring
      have hGI : (∫ t in E, G t ^ (2 : ℝ)) =
          ∫ t in E, A t ^ 4 := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp [G]
        rw [Real.rpow_two]
        ring
      rw [hFI, hGI]

/-- The complete source-closed analytic interface for one Type-I block.
The Deshouillers--Iwaniec estimate controls the first Cauchy--Schwarz
moment; the caller supplies only the pointwise inserted-factor inequality
and the fourth-moment bound for the divisor-bounded long factor. -/
theorem typeI_componentBlockIntegral_le_of_matomakiTeravainen
    (hDI : MatomakiTeravainenLemmaThreeFivePartTwoStatement)
    {eta A N N' T M₁ K L : ℝ} {b alpha : ℕ → ℂ} {E : Set ℝ}
    (heta : 0 < eta) (hA : 1 ≤ A) (hN : 1 ≤ N) (hN' : 1 ≤ N')
    (hT : 1 ≤ T) (hNN' : N < N') (hN'two : N' ≤ 2 * N)
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc T (2 * T))
    (hK : 0 ≤ K)
    (hinsert : ∀ t ∈ E,
      1 ≤ K * ‖dyadicDirichletPolynomial b A (onePlusIT t)‖)
    (hlong :
      (∫ t in E,
        ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (4 : ℕ)) ≤ L) :
    ∃ C : ℝ, 0 < C ∧
      (∫ t in E,
        ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖matomakiTeravainenZetaSegmentPolynomial N N' (onePlusIT t)‖ ^
            (2 : ℕ)) ≤
        K *
          ((typeIDIMajorant C eta A N N' T b) ^ (1 / 2 : ℝ) *
            L ^ (1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hDIbound⟩ :=
    typeI_twistedFourthMoment_le_of_matomakiTeravainen hDI
      heta hA hN hN' hT hNN' hN'two
  refine ⟨C, hC, ?_⟩
  let Long : ℝ → ℝ := fun t ↦
    ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖
  let Short : ℝ → ℝ := fun t ↦
    ‖matomakiTeravainenZetaSegmentPolynomial N N' (onePlusIT t)‖
  let Inserted : ℝ → ℝ := fun t ↦
    ‖dyadicDirichletPolynomial b A (onePlusIT t)‖
  have hLongCont : Continuous Long := by
    exact (Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
      alpha M₁).norm
  have hShortCont : Continuous Short := by
    dsimp [Short]
    exact (Sparse.continuous_dirichletPolynomial_onePlusIT_sparse
      (fun _ ↦ 1) (natOpenClosedInterval N N')).norm
  have hInsertedCont : Continuous Inserted := by
    exact (Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
      b A).norm
  have hmeasF : AEStronglyMeasurable
      (fun t ↦ Short t ^ 2 * Inserted t) (volume.restrict E) :=
    ((hShortCont.pow 2).mul hInsertedCont).aestronglyMeasurable
  have hmeasG : AEStronglyMeasurable
      (fun t ↦ Long t ^ 2) (volume.restrict E) :=
    (hLongCont.pow 2).aestronglyMeasurable
  have hintF : IntegrableOn
      (fun t ↦ (Short t ^ 2 * Inserted t) ^ 2) E :=
    (((hShortCont.pow 2).mul hInsertedCont).pow 2).integrableOn_Icc.mono_set
      hEsub
  have hintG : IntegrableOn (fun t ↦ (Long t ^ 2) ^ 2) E :=
    ((hLongCont.pow 2).pow 2).integrableOn_Icc.mono_set hEsub
  have hintLeft : IntegrableOn
      (fun t ↦ Long t ^ 2 * Short t ^ 2) E :=
    ((hLongCont.pow 2).mul (hShortCont.pow 2)).integrableOn_Icc.mono_set
      hEsub
  have hintProduct : IntegrableOn
      (fun t ↦ (Short t ^ 2 * Inserted t) * (Long t ^ 2)) E :=
    (((hShortCont.pow 2).mul hInsertedCont).mul
      (hLongCont.pow 2)).integrableOn_Icc.mono_set hEsub
  have hcauchy := typeI_integral_le_inserted_cauchy
    hE hK (fun t ht ↦ norm_nonneg _)
    (fun t ht ↦ by simpa [Inserted] using hinsert t ht)
    hmeasF hmeasG hintF hintG hintLeft hintProduct
  have hTwistedCont : Continuous (fun t ↦
      Short t ^ 4 * Inserted t ^ 2) :=
    (hShortCont.pow 4).mul (hInsertedCont.pow 2)
  have hTwistedFull : IntegrableOn (fun t ↦
      Short t ^ 4 * Inserted t ^ 2) (Set.Icc T (2 * T)) :=
    hTwistedCont.integrableOn_Icc
  have hTwistedNonneg : ∀ t, 0 ≤ Short t ^ 4 * Inserted t ^ 2 :=
    fun t ↦ mul_nonneg (pow_nonneg (norm_nonneg _) 4)
      (pow_nonneg (norm_nonneg _) 2)
  have hTwistedRestrict :
      (∫ t in E, Short t ^ 4 * Inserted t ^ 2) ≤
        ∫ t in Set.Icc T (2 * T), Short t ^ 4 * Inserted t ^ 2 := by
    apply setIntegral_mono_set hTwistedFull
    · exact Filter.Eventually.of_forall hTwistedNonneg
    · exact Filter.Eventually.of_forall hEsub
  have hTwistedSource :
      (∫ t in E, Short t ^ 4 * Inserted t ^ 2) ≤
        typeIDIMajorant C eta A N N' T b := by
    refine hTwistedRestrict.trans ?_
    simpa [Short, Inserted] using hDIbound
  have hTwistedE0 : 0 ≤ ∫ t in E,
      Short t ^ 4 * Inserted t ^ 2 :=
    setIntegral_nonneg hE (fun t ht ↦ hTwistedNonneg t)
  have hMajorant0 : 0 ≤ typeIDIMajorant C eta A N N' T b :=
    hTwistedE0.trans hTwistedSource
  have hLongE0 : 0 ≤ ∫ t in E, Long t ^ 4 :=
    setIntegral_nonneg hE (fun t ht ↦ pow_nonneg (norm_nonneg _) 4)
  have hL0 : 0 ≤ L := by
    apply hLongE0.trans
    simpa [Long] using hlong
  have hTwistedHalf := Real.rpow_le_rpow hTwistedE0 hTwistedSource
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hLongHalf :
      (∫ t in E, Long t ^ 4) ^ (1 / 2 : ℝ) ≤ L ^ (1 / 2 : ℝ) := by
    apply Real.rpow_le_rpow hLongE0
    · simpa [Long] using hlong
    · norm_num
  have hproduct :
      (∫ t in E, Short t ^ 4 * Inserted t ^ 2) ^ (1 / 2 : ℝ) *
          (∫ t in E, Long t ^ 4) ^ (1 / 2 : ℝ) ≤
        (typeIDIMajorant C eta A N N' T b) ^ (1 / 2 : ℝ) *
          L ^ (1 / 2 : ℝ) := by
    exact mul_le_mul hTwistedHalf hLongHalf
      (Real.rpow_nonneg hLongE0 _) (Real.rpow_nonneg hMajorant0 _)
  calc
    (∫ t in E,
        ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖matomakiTeravainenZetaSegmentPolynomial N N' (onePlusIT t)‖ ^
            (2 : ℕ)) ≤
        K *
          ((∫ t in E, Short t ^ 4 * Inserted t ^ 2) ^ (1 / 2 : ℝ) *
            (∫ t in E, Long t ^ 4) ^ (1 / 2 : ℝ)) := by
      simpa [Long, Short, Inserted] using hcauchy
    _ ≤ K *
        ((typeIDIMajorant C eta A N N' T b) ^ (1 / 2 : ℝ) *
          L ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hproduct hK

/-! ## Closing the first-factor moment from the cited source -/

/-- The strongest source-closed per-component estimate before the
prime-power localization step.  Both analytic factors in Cauchy--Schwarz
are now supplied by the cited MT23 inputs: Lemma 3.5(ii) controls the
twisted short factor and Lemma 3.2 controls the fourth moment of the long
factor.  The powered coefficient energy is intentionally left exact. -/
theorem typeI_componentIntegral_le_of_matomakiTeravainen
    (hDI : MatomakiTeravainenLemmaThreeFivePartTwoStatement)
    (hMV : MatomakiTeravainenLemmaThreeTwoStatement)
    {eta A N N' T M₁ K : ℝ} {b alpha : ℕ → ℂ} {E : Set ℝ}
    (heta : 0 < eta) (hA : 1 ≤ A) (hN : 1 ≤ N) (hN' : 1 ≤ N')
    (hT : 1 ≤ T) (hM₁ : 1 ≤ M₁)
    (hNN' : N < N') (hN'two : N' ≤ 2 * N)
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc T (2 * T))
    (hK : 0 ≤ K)
    (hinsert : ∀ t ∈ E,
      1 ≤ K * ‖dyadicDirichletPolynomial b A (onePlusIT t)‖) :
    ∃ C_DI C_MV : ℝ, 0 < C_DI ∧ 0 < C_MV ∧
      (∫ t in E,
        ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖matomakiTeravainenZetaSegmentPolynomial N N' (onePlusIT t)‖ ^
            (2 : ℕ)) ≤
        K *
          ((typeIDIMajorant C_DI eta A N N' T b) ^ (1 / 2 : ℝ) *
            ((4 * T + C_MV * (2 * M₁) ^ (2 : ℕ)) *
                TypeII.poweredLineOneEnergy alpha M₁ 2) ^ (1 / 2 : ℝ)) := by
  obtain ⟨C_MV, hC_MV, hlongFull⟩ :=
    typeI_longFourthMoment_le_of_matomakiTeravainen hMV
  let longIntegrand : ℝ → ℝ := fun t ↦
    ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (4 : ℕ)
  have hlongCont : Continuous longIntegrand :=
    (Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
      alpha M₁).norm.pow 4
  have hlongRestrict :
      (∫ t in E, longIntegrand t) ≤
        ∫ t in Set.Icc T (2 * T), longIntegrand t := by
    apply setIntegral_mono_set hlongCont.integrableOn_Icc
    · exact Filter.Eventually.of_forall
        (fun t ↦ pow_nonneg (norm_nonneg _) 4)
    · exact Filter.Eventually.of_forall hEsub
  have hlong :
      (∫ t in E,
          ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (4 : ℕ)) ≤
        (4 * T + C_MV * (2 * M₁) ^ (2 : ℕ)) *
          TypeII.poweredLineOneEnergy alpha M₁ 2 := by
    change (∫ t in E, longIntegrand t) ≤ _
    exact hlongRestrict.trans (hlongFull alpha M₁ T hM₁ hT)
  obtain ⟨C_DI, hC_DI, hcomponent⟩ :=
    typeI_componentBlockIntegral_le_of_matomakiTeravainen hDI
      heta hA hN hN' hT hNN' hN'two hE hEsub hK hinsert hlong
  exact ⟨C_DI, C_MV, hC_DI, hC_MV, hcomponent⟩

/-- Divisor-bounded form of the complete source-closed component estimate.
The subpower constant is uniform in the coefficient sequence, its displayed
constant, and all scales.  What remains after this theorem is only the
prime-power dyadic localization/insertion and real-exponent scale algebra. -/
theorem typeI_componentIntegral_le_of_sources_divisorBounded
    (hDI : MatomakiTeravainenLemmaThreeFivePartTwoStatement)
    (hMV : MatomakiTeravainenLemmaThreeTwoStatement)
    {B₀ rho eta A N N' T M₁ K A₀ : ℝ}
    {b alpha : ℕ → ℂ} {E : Set ℝ}
    (hB₀ : 0 ≤ B₀) (hrho : 0 < rho)
    (heta : 0 < eta) (hA : 1 ≤ A) (hN : 1 ≤ N) (hN' : 1 ≤ N')
    (hT : 1 ≤ T) (hM₁ : 1 ≤ M₁)
    (hNN' : N < N') (hN'two : N' ≤ 2 * N)
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc T (2 * T))
    (hK : 0 ≤ K)
    (halpha : IsDivisorBoundedByConstant B₀ A₀ alpha)
    (hinsert : ∀ t ∈ E,
      1 ≤ K * ‖dyadicDirichletPolynomial b A (onePlusIT t)‖) :
    ∃ C_DI C_MV D : ℝ,
      0 < C_DI ∧ 0 < C_MV ∧ 1 ≤ D ∧
      (∫ t in E,
        ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖matomakiTeravainenZetaSegmentPolynomial N N' (onePlusIT t)‖ ^
            (2 : ℕ)) ≤
        K *
          ((typeIDIMajorant C_DI eta A N N' T b) ^ (1 / 2 : ℝ) *
            ((4 * T + C_MV * (2 * M₁) ^ (2 : ℕ)) *
              ((2 * M₁) ^ (2 : ℕ) *
                ((A₀ ^ (2 : ℕ) * D *
                    ((2 * M₁) ^ (2 : ℕ)) ^ rho) /
                  M₁ ^ (2 : ℕ)) ^ (2 : ℕ))) ^ (1 / 2 : ℝ)) := by
  obtain ⟨C_MV, D, hC_MV, hD, hlongFull⟩ :=
    typeI_longFourthMoment_le_of_divisorBounded hMV hB₀ hrho
  let longIntegrand : ℝ → ℝ := fun t ↦
    ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (4 : ℕ)
  have hlongCont : Continuous longIntegrand :=
    (Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
      alpha M₁).norm.pow 4
  have hlongRestrict :
      (∫ t in E, longIntegrand t) ≤
        ∫ t in Set.Icc T (2 * T), longIntegrand t := by
    apply setIntegral_mono_set hlongCont.integrableOn_Icc
    · exact Filter.Eventually.of_forall
        (fun t ↦ pow_nonneg (norm_nonneg _) 4)
    · exact Filter.Eventually.of_forall hEsub
  have hlong :
      (∫ t in E,
          ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (4 : ℕ)) ≤
        (4 * T + C_MV * (2 * M₁) ^ (2 : ℕ)) *
          ((2 * M₁) ^ (2 : ℕ) *
            ((A₀ ^ (2 : ℕ) * D *
                ((2 * M₁) ^ (2 : ℕ)) ^ rho) /
              M₁ ^ (2 : ℕ)) ^ (2 : ℕ)) := by
    change (∫ t in E, longIntegrand t) ≤ _
    exact hlongRestrict.trans
      (hlongFull alpha M₁ T A₀ hM₁ hT halpha)
  obtain ⟨C_DI, hC_DI, hcomponent⟩ :=
    typeI_componentBlockIntegral_le_of_matomakiTeravainen hDI
      heta hA hN hN' hT hNN' hN'two hE hEsub hK hinsert hlong
  exact ⟨C_DI, C_MV, D, hC_DI, hC_MV, hD, hcomponent⟩

/-! ## Exact remaining finite-slice bridge -/

/-- The exact proposition still needed to pass from the proved pointwise
sum insertion to the source-closed component bound.

The right side deliberately contains **all** `k` dyadic slices.  The
triangle inequality proved in `typeI_primePower_dyadicSum_insertion` does
not justify choosing one slice uniformly in `t`.  Finite Cauchy--Schwarz
instead costs the displayed factor `k`, after which the same uniform
constant from MT23 Lemma 3.5(ii) applies to every slice.

This is a local `Prop`, not an axiom or an `ExternalInputs` field.  The
coefficient energy for each displayed majorant and the long fourth moment
are proved above.  After this proposition only scale absorption is left.
A final `X^{-c}` statement is not stated here because this representation
interface does not record the relations among `M₁`, `N`, `P^k`, `T`, and
the chosen integer `k`; the main theorem uses the labelled extension E4. -/
def TypeIPrimePowerFiniteSliceAssemblyStatement : Prop :=
  ∀ (_hDI : MatomakiTeravainenLemmaThreeFivePartTwoStatement)
      (_hMV : MatomakiTeravainenLemmaThreeTwoStatement)
      (eta epsilon P N N' T M₁ : ℝ) (k : ℕ)
      (alpha : ℕ → ℂ) (E : Set ℝ),
    0 < eta → 1 ≤ P → 1 ≤ k →
    1 ≤ N → 1 ≤ N' → 1 ≤ T → 1 ≤ M₁ →
    N < N' → N' ≤ 2 * N →
    MeasurableSet E → E ⊆ Set.Icc T (2 * T) →
    (∀ t ∈ E,
      P ^ (-epsilon / 10) ≤
        ‖primeDirichletPolynomial P (onePlusIT t)‖) →
    ∃ C_DI C_MV : ℝ, 0 < C_DI ∧ 0 < C_MV ∧
      (∫ t in E,
        ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖matomakiTeravainenZetaSegmentPolynomial N N'
            (onePlusIT t)‖ ^ (2 : ℕ)) ≤
        ((P ^ (-epsilon / 10)) ^ k)⁻¹ *
          ((((k : ℝ) *
              ∑ j ∈ Finset.range k,
                typeIDIMajorant C_DI eta
                  ((2 : ℝ) ^ j * P ^ k) N N' T
                  (rawPrimePowerCoefficient (dyadicPrimes P) k)) ^
                (1 / 2 : ℝ)) *
            (((4 * T + C_MV * (2 * M₁) ^ (2 : ℕ)) *
                TypeII.poweredLineOneEnergy alpha M₁ 2) ^
              (1 / 2 : ℝ)))

def typeIComponentClosureModule : ProofModule :=
  { name := "Completion.TypeIComponentClosure"
    paperLocation := "MT23 Section 5.1 and Proposition 7.1, Type-I components"
    purpose :=
      "Prove the exact Type-I convolution factorization, the literal [T,2T] specialization of MT23 Lemma 3.5(ii), the cited long-factor fourth moment, and the source-closed per-component Cauchy bound; isolate only the quantifier-correct finite-slice assembly and absent final component-scale package."
    dependsOn :=
      [ "Completion.TypeIClosure",
        "Completion.TypeIPrimePowerEnergy",
        "Completion.TypeIFirstFactorMoment",
        "Sparse.GlobalComponentCancellation",
        "Assumptions.deshouillersIwaniecEquationFourteen",
        "Assumptions.matomakiTeravainenLemmaThreeTwo" ]
    status := .proved }

end

end Completion
end ExactSemiprimes
