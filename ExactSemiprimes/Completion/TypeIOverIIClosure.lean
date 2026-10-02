import ExactSemiprimes.Completion.PerronTarget
import ExactSemiprimes.Assumptions
import ExactSemiprimes.Sparse.GlobalComponentCancellation

/-! # Closure of Type-I/II convolution components -/

namespace ExactSemiprimes
namespace Completion

open MeasureTheory
open scoped BigOperators

noncomputable section

/-! ## Exact finite factorization of a Type-I/II component -/

def typeIOneHalfFirstSupport (M₁ : ℝ) : Finset ℕ :=
  dyadicInterval M₁

def typeIOneHalfSecondSupport (M₂ : ℝ) : Finset ℕ :=
  dyadicInterval M₂

def typeIOneHalfThirdSupport (delta M₃ : ℝ) : Finset ℕ :=
  natOpenClosedInterval M₃ ((1 + delta) * M₃)

def typeIOneHalfSupportTriples
    (delta M₁ M₂ M₃ : ℝ) (n : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((((typeIOneHalfFirstSupport M₁).product
      (typeIOneHalfSecondSupport M₂)).product
      (typeIOneHalfThirdSupport delta M₃)).filter
    (fun p ↦ p.1.1 * p.1.2 * p.2 = n))

def ternaryConvolutionCoefficient
    (alpha beta gamma : ℕ → ℂ) (S₁ S₂ S₃ : Finset ℕ) (n : ℕ) : ℂ :=
  ∑ p ∈ (((S₁.product S₂).product S₃).filter
      (fun p ↦ p.1.1 * p.1.2 * p.2 = n)),
    alpha p.1.1 * beta p.1.2 * gamma p.2

/-- A three-fold finite Dirichlet-polynomial product is the polynomial of
the corresponding ternary convolution on its literal product-image
support.  This is the finite algebra behind MT23, Proposition 2.2(ii). -/
theorem dirichletPolynomial_mul_mul_eq_ternaryConvolution
    (alpha beta gamma : ℕ → ℂ) (S₁ S₂ S₃ : Finset ℕ) (s : ℂ) :
    dirichletPolynomial alpha S₁ s * dirichletPolynomial beta S₂ s *
        dirichletPolynomial gamma S₃ s =
      dirichletPolynomial
        (ternaryConvolutionCoefficient alpha beta gamma S₁ S₂ S₃)
        (((S₁.product S₂).product S₃).image
          fun p ↦ p.1.1 * p.1.2 * p.2) s := by
  classical
  simp only [dirichletPolynomial]
  calc
    ((∑ m₁ ∈ S₁, alpha m₁ * (m₁ : ℂ) ^ (-s)) *
          (∑ m₂ ∈ S₂, beta m₂ * (m₂ : ℂ) ^ (-s))) *
          (∑ m₃ ∈ S₃, gamma m₃ * (m₃ : ℂ) ^ (-s)) =
        (∑ p ∈ S₁.product S₂,
          (alpha p.1 * (p.1 : ℂ) ^ (-s)) *
            (beta p.2 * (p.2 : ℂ) ^ (-s))) *
          (∑ m₃ ∈ S₃, gamma m₃ * (m₃ : ℂ) ^ (-s)) := by
      congr 1
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
      rfl
    _ = (∑ p ∈ (S₁.product S₂).product S₃,
        ((alpha p.1.1 * (p.1.1 : ℂ) ^ (-s)) *
          (beta p.1.2 * (p.1.2 : ℂ) ^ (-s))) *
          (gamma p.2 * (p.2 : ℂ) ^ (-s))) := by
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
      rfl
    _ = ∑ p ∈ (S₁.product S₂).product S₃,
        (alpha p.1.1 * beta p.1.2 * gamma p.2) *
          ((p.1.1 * p.1.2 * p.2 : ℕ) : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro p hp
      have h12 :
          (((p.1.1 * p.1.2 : ℕ) : ℂ) ^ (-s)) =
            (p.1.1 : ℂ) ^ (-s) * (p.1.2 : ℂ) ^ (-s) := by
        simpa only [Nat.cast_mul] using
          Complex.natCast_mul_natCast_cpow p.1.1 p.1.2 (-s)
      have h123 :
          (((p.1.1 * p.1.2 * p.2 : ℕ) : ℂ) ^ (-s)) =
            ((p.1.1 * p.1.2 : ℕ) : ℂ) ^ (-s) *
              (p.2 : ℂ) ^ (-s) := by
        simpa only [Nat.cast_mul] using
          Complex.natCast_mul_natCast_cpow
            (p.1.1 * p.1.2) p.2 (-s)
      rw [h123, h12]
      ring
    _ = ∑ n ∈ (((S₁.product S₂).product S₃).image
          fun p ↦ p.1.1 * p.1.2 * p.2),
        ∑ p ∈ (S₁.product S₂).product S₃ with
            p.1.1 * p.1.2 * p.2 = n,
          (alpha p.1.1 * beta p.1.2 * gamma p.2) *
            ((p.1.1 * p.1.2 * p.2 : ℕ) : ℂ) ^ (-s) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (s := (S₁.product S₂).product S₃)
        (t := (((S₁.product S₂).product S₃).image
          fun p ↦ p.1.1 * p.1.2 * p.2))
        (g := fun p ↦ p.1.1 * p.1.2 * p.2)
        (fun p hp ↦ Finset.mem_image.mpr ⟨p, hp, rfl⟩)
        (fun p ↦
          (alpha p.1.1 * beta p.1.2 * gamma p.2) *
            ((p.1.1 * p.1.2 * p.2 : ℕ) : ℂ) ^ (-s))
    _ = ∑ n ∈ (((S₁.product S₂).product S₃).image
          fun p ↦ p.1.1 * p.1.2 * p.2),
        ternaryConvolutionCoefficient alpha beta gamma S₁ S₂ S₃ n *
          (n : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ternaryConvolutionCoefficient, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]

theorem mem_typeIOneHalfFirstSupport_iff
    {M₁ : ℝ} {m : ℕ} (hM₁ : 0 < M₁) :
    m ∈ typeIOneHalfFirstSupport M₁ ↔ InDyadicRange M₁ m := by
  exact mem_dyadicInterval hM₁.le

theorem mem_typeIOneHalfSecondSupport_iff
    {M₂ : ℝ} {m : ℕ} (hM₂ : 0 < M₂) :
    m ∈ typeIOneHalfSecondSupport M₂ ↔ InDyadicRange M₂ m := by
  exact mem_dyadicInterval hM₂.le

theorem mem_typeIOneHalfThirdSupport_iff
    {delta M₃ : ℝ} {m : ℕ} (hdelta : 0 ≤ delta) (hM₃ : 0 < M₃) :
    m ∈ typeIOneHalfThirdSupport delta M₃ ↔
      M₃ < (m : ℝ) ∧ (m : ℝ) ≤ (1 + delta) * M₃ := by
  apply mem_natOpenClosedInterval hM₃.le
  exact mul_nonneg (by linarith) hM₃.le

def typeIOneHalfRangeTriples
    (delta M₁ M₂ M₃ : ℝ) (n : ℕ) : Finset ((ℕ × ℕ) × ℕ) := by
  classical
  exact ((((Finset.range (n + 1)).product (Finset.range (n + 1))).product
    (Finset.range (n + 1))).filter fun p ↦
      p.1.1 * p.1.2 * p.2 = n ∧ InDyadicRange M₁ p.1.1 ∧
        InDyadicRange M₂ p.1.2 ∧ M₃ < (p.2 : ℝ) ∧
        (p.2 : ℝ) ≤ (1 + delta) * M₃)

theorem typeIOneHalf_triple_filter_eq
    {delta M₁ M₂ M₃ : ℝ} {n : ℕ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM₃ : 0 < M₃) :
    typeIOneHalfRangeTriples delta M₁ M₂ M₃ n =
      typeIOneHalfSupportTriples delta M₁ M₂ M₃ n := by
  classical
  ext p
  simp only [typeIOneHalfRangeTriples, typeIOneHalfSupportTriples]
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hrange, hprod, hm₁, hm₂, hm₃low, hm₃up⟩
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩,
      hprod⟩
    · exact (mem_typeIOneHalfFirstSupport_iff hM₁).2 hm₁
    · exact (mem_typeIOneHalfSecondSupport_iff hM₂).2 hm₂
    · exact (mem_typeIOneHalfThirdSupport_iff hdelta hM₃).2
        ⟨hm₃low, hm₃up⟩
  · rintro ⟨hsupport, hprod⟩
    obtain ⟨hm₁m₂mem, hm₃mem⟩ := Finset.mem_product.mp hsupport
    obtain ⟨hm₁mem, hm₂mem⟩ := Finset.mem_product.mp hm₁m₂mem
    have hm₁ := (mem_typeIOneHalfFirstSupport_iff hM₁).1 hm₁mem
    have hm₂ := (mem_typeIOneHalfSecondSupport_iff hM₂).1 hm₂mem
    have hm₃ := (mem_typeIOneHalfThirdSupport_iff hdelta hM₃).1
      hm₃mem
    have hm₁posReal : 0 < (p.1.1 : ℝ) := hM₁.trans hm₁.1
    have hm₂posReal : 0 < (p.1.2 : ℝ) := hM₂.trans hm₂.1
    have hm₃posReal : 0 < (p.2 : ℝ) := hM₃.trans hm₃.1
    have hm₁pos : 0 < p.1.1 := by exact_mod_cast hm₁posReal
    have hm₂pos : 0 < p.1.2 := by exact_mod_cast hm₂posReal
    have hm₃pos : 0 < p.2 := by exact_mod_cast hm₃posReal
    have hnpos : 0 < n := by
      rw [← hprod]
      exact Nat.mul_pos (Nat.mul_pos hm₁pos hm₂pos) hm₃pos
    have hm₁le : p.1.1 ≤ n :=
      Nat.le_of_dvd hnpos ⟨p.1.2 * p.2, by
        simpa [Nat.mul_assoc] using hprod.symm⟩
    have hm₂le : p.1.2 ≤ n :=
      Nat.le_of_dvd hnpos ⟨p.1.1 * p.2, by
        simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hprod.symm⟩
    have hm₃le : p.2 ≤ n :=
      Nat.le_of_dvd hnpos ⟨p.1.1 * p.1.2, by
        simpa [Nat.mul_comm] using hprod.symm⟩
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩,
      hprod, hm₁, hm₂, hm₃⟩
    · exact Finset.mem_range.mpr (by omega)
    · exact Finset.mem_range.mpr (by omega)
    · exact Finset.mem_range.mpr (by omega)

theorem matomakiTeravainenTypeIOneHalfValue_eq_ternaryConvolution
    {delta M₁ M₂ M₃ : ℝ} {alpha beta : ℕ → ℂ} {n : ℕ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM₃ : 0 < M₃) :
    matomakiTeravainenTypeIOneHalfValue delta M₁ M₂ M₃ alpha beta n =
      ternaryConvolutionCoefficient alpha beta (fun _ ↦ 1)
        (typeIOneHalfFirstSupport M₁) (typeIOneHalfSecondSupport M₂)
        (typeIOneHalfThirdSupport delta M₃) n := by
  classical
  rw [matomakiTeravainenTypeIOneHalfValue, ternaryConvolutionCoefficient]
  let R := Finset.range (n + 1)
  calc
    (∑ m₁ ∈ R, ∑ m₂ ∈ R, ∑ m₃ ∈ R,
        if m₁ * m₂ * m₃ = n ∧ InDyadicRange M₁ m₁ ∧
            InDyadicRange M₂ m₂ ∧ M₃ < (m₃ : ℝ) ∧
            (m₃ : ℝ) ≤ (1 + delta) * M₃ then
          alpha m₁ * beta m₂
        else 0) =
      ∑ p ∈ (R.product R).product R,
        if p.1.1 * p.1.2 * p.2 = n ∧ InDyadicRange M₁ p.1.1 ∧
            InDyadicRange M₂ p.1.2 ∧ M₃ < (p.2 : ℝ) ∧
            (p.2 : ℝ) ≤ (1 + delta) * M₃ then
          alpha p.1.1 * beta p.1.2
        else 0 := by
      rw [← Finset.sum_product', ← Finset.sum_product']
      rfl
    _ = ∑ p ∈ typeIOneHalfRangeTriples delta M₁ M₂ M₃ n,
        alpha p.1.1 * beta p.1.2 := by
      rw [← Finset.sum_filter]
      rfl
    _ = ∑ p ∈ typeIOneHalfSupportTriples delta M₁ M₂ M₃ n,
        alpha p.1.1 * beta p.1.2 := by
      rw [typeIOneHalf_triple_filter_eq hdelta hM₁ hM₂ hM₃]
    _ = ∑ p ∈ ((((typeIOneHalfFirstSupport M₁).product
          (typeIOneHalfSecondSupport M₂)).product
          (typeIOneHalfThirdSupport delta M₃)).filter
          (fun p ↦ p.1.1 * p.1.2 * p.2 = n)),
        alpha p.1.1 * beta p.1.2 * (fun _ ↦ (1 : ℂ)) p.2 := by
      simp [typeIOneHalfSupportTriples]

/-- The complete polynomial generated by a source Type-I/II convolution is
exactly the product of its two dyadic coefficient factors and its short
unit-coefficient segment. -/
theorem matomakiTeravainenTypeIOneHalf_polynomial_factorization
    {delta M₁ M₂ M₃ : ℝ} {alpha beta : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM₃ : 0 < M₃) (s : ℂ) :
    dirichletPolynomial
        (matomakiTeravainenTypeIOneHalfValue
          delta M₁ M₂ M₃ alpha beta)
        (Sparse.typeIOneHalfProductSupport delta M₁ M₂ M₃) s =
      dyadicDirichletPolynomial alpha M₁ s *
        dyadicDirichletPolynomial beta M₂ s *
        matomakiTeravainenZetaSegmentPolynomial M₃
          ((1 + delta) * M₃) s := by
  rw [dyadicDirichletPolynomial, matomakiTeravainenZetaSegmentPolynomial]
  symm
  calc
    dirichletPolynomial alpha (typeIOneHalfFirstSupport M₁) s *
          dirichletPolynomial beta (typeIOneHalfSecondSupport M₂) s *
          dirichletPolynomial (fun _ ↦ 1)
            (typeIOneHalfThirdSupport delta M₃) s =
        dirichletPolynomial
          (ternaryConvolutionCoefficient alpha beta (fun _ ↦ 1)
            (typeIOneHalfFirstSupport M₁) (typeIOneHalfSecondSupport M₂)
            (typeIOneHalfThirdSupport delta M₃))
          ((((typeIOneHalfFirstSupport M₁).product
            (typeIOneHalfSecondSupport M₂)).product
            (typeIOneHalfThirdSupport delta M₃)).image
              fun p ↦ p.1.1 * p.1.2 * p.2) s :=
      dirichletPolynomial_mul_mul_eq_ternaryConvolution _ _ _ _ _ _ s
    _ = dirichletPolynomial
          (matomakiTeravainenTypeIOneHalfValue
            delta M₁ M₂ M₃ alpha beta)
          (Sparse.typeIOneHalfProductSupport delta M₁ M₂ M₃) s := by
      unfold dirichletPolynomial Sparse.typeIOneHalfProductSupport
        typeIOneHalfFirstSupport typeIOneHalfSecondSupport
        typeIOneHalfThirdSupport
      apply Finset.sum_congr rfl
      intro n hn
      rw [matomakiTeravainenTypeIOneHalfValue_eq_ternaryConvolution
        hdelta hM₁ hM₂ hM₃]
      rfl

/-- The factorization in the exact representation supplied by MT23,
Proposition 2.2(ii). -/
theorem representedTypeIOneHalf_polynomial_factorization
    {delta M₁ M₂ M₃ : ℝ} {alpha beta f : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM₃ : 0 < M₃)
    (hf : ∀ n, f n = matomakiTeravainenTypeIOneHalfValue
      delta M₁ M₂ M₃ alpha beta n) (s : ℂ) :
    dirichletPolynomial f
        (Sparse.typeIOneHalfProductSupport delta M₁ M₂ M₃) s =
      dyadicDirichletPolynomial alpha M₁ s *
        dyadicDirichletPolynomial beta M₂ s *
        matomakiTeravainenZetaSegmentPolynomial M₃
          ((1 + delta) * M₃) s := by
  calc
    dirichletPolynomial f
          (Sparse.typeIOneHalfProductSupport delta M₁ M₂ M₃) s =
        dirichletPolynomial
          (matomakiTeravainenTypeIOneHalfValue
            delta M₁ M₂ M₃ alpha beta)
          (Sparse.typeIOneHalfProductSupport delta M₁ M₂ M₃) s := by
      unfold dirichletPolynomial
      apply Finset.sum_congr rfl
      intro n hn
      rw [hf n]
    _ = _ := matomakiTeravainenTypeIOneHalf_polynomial_factorization
      hdelta hM₁ hM₂ hM₃ s

/-! ## Literal block specialization of Watt's estimate -/

/-- The source right-hand side of MT23, Lemma 3.5(i), after replacing its
height by `2T`, so its integration interval is exactly `[T,2T]`. -/
def typeIOverIIWattMajorant
    (C eta A N _N' T : ℝ) (b : ℕ → ℂ) : ℝ :=
  C * (2 * T) ^ eta *
    ((((2 * T) + A ^ (2 : ℕ) * (2 * T) ^ (1 / 2 : ℝ)) /
          (N ^ (2 : ℕ) * A) +
        ((2 * T) + A) / ((2 * T) ^ (4 : ℕ) * A)) *
      dyadicComplexCoefficientSup b A ^ (2 : ℕ))

/-- Direct application of the published Watt input on the dyadic height
block `[T,2T]`; no exponent simplification is folded into the statement. -/
theorem typeIOverII_twistedFourthMoment_le_of_matomakiTeravainen
    (hWatt : MatomakiTeravainenLemmaThreeFivePartOneStatement)
    {eta A N N' T : ℝ} {b : ℕ → ℂ}
    (heta : 0 < eta) (hA : 1 ≤ A) (hN : 1 ≤ N) (hN' : 1 ≤ N')
    (hT : 1 ≤ T) (hNN' : N < N') (hN'two : N' ≤ 2 * N) :
    ∃ C : ℝ, 0 < C ∧
      (∫ t in Set.Icc T (2 * T),
        ‖matomakiTeravainenZetaSegmentPolynomial N N'
            (onePlusIT t)‖ ^ (4 : ℕ) *
          ‖dyadicDirichletPolynomial b A (onePlusIT t)‖ ^ (2 : ℕ)) ≤
        typeIOverIIWattMajorant C eta A N N' T b := by
  obtain ⟨C, hC, hsource⟩ := hWatt eta heta
  refine ⟨C, hC, ?_⟩
  have h2T : 1 ≤ 2 * T := by linarith
  have h := hsource A N N' (2 * T) b hA hN hN' h2T hNN' hN'two
  simpa [matomakiTeravainenTwistedFourthMoment,
    dyadicDirichletPolynomial, typeIOverIIWattMajorant] using h

/-! ## The exact inserted Cauchy--Schwarz step from Section 5.2 -/

/-- Deterministic form of the insertion in MT23, Section 5.2.  In the
application `A₁,A₂,A₃` are the norms of the three component
polynomials and `B` is the norm of a power of the prime polynomial. -/
theorem typeIOverII_integral_le_inserted_cauchy
    {E : Set ℝ} {K : ℝ} {A₁ A₂ A₃ B : ℝ → ℝ}
    (hE : MeasurableSet E)
    (hK : 0 ≤ K)
    (hA₂ : ∀ t ∈ E, 0 ≤ A₂ t) (hB : ∀ t ∈ E, 0 ≤ B t)
    (hinsert : ∀ t ∈ E, 1 ≤ K * B t)
    (hmeasF : AEStronglyMeasurable
      (fun t ↦ A₃ t ^ 2 * A₂ t) (volume.restrict E))
    (hmeasG : AEStronglyMeasurable
      (fun t ↦ A₁ t ^ 2 * A₂ t * B t) (volume.restrict E))
    (hintF : IntegrableOn (fun t ↦ (A₃ t ^ 2 * A₂ t) ^ 2) E)
    (hintG : IntegrableOn
      (fun t ↦ (A₁ t ^ 2 * A₂ t * B t) ^ 2) E)
    (hintLeft : IntegrableOn
      (fun t ↦ A₁ t ^ 2 * A₂ t ^ 2 * A₃ t ^ 2) E)
    (hintProduct : IntegrableOn
      (fun t ↦ (A₃ t ^ 2 * A₂ t) *
        (A₁ t ^ 2 * A₂ t * B t)) E) :
    (∫ t in E, A₁ t ^ 2 * A₂ t ^ 2 * A₃ t ^ 2) ≤
      K *
        ((∫ t in E, A₃ t ^ 4 * A₂ t ^ 2) ^ (1 / 2 : ℝ) *
          (∫ t in E, A₁ t ^ 4 * A₂ t ^ 2 * B t ^ 2) ^
            (1 / 2 : ℝ)) := by
  let F : ℝ → ℝ := fun t ↦ A₃ t ^ 2 * A₂ t
  let G : ℝ → ℝ := fun t ↦ A₁ t ^ 2 * A₂ t * B t
  have hFnonneg : 0 ≤ᵐ[volume.restrict E] F := by
    filter_upwards [ae_restrict_mem hE] with t ht
    dsimp [F]
    exact mul_nonneg (sq_nonneg _) (hA₂ t ht)
  have hGnonneg : 0 ≤ᵐ[volume.restrict E] G := by
    filter_upwards [ae_restrict_mem hE] with t ht
    dsimp [G]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (hA₂ t ht)) (hB t ht)
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
      (∫ t in E, A₁ t ^ 2 * A₂ t ^ 2 * A₃ t ^ 2) ≤
        K * ∫ t in E, F t * G t := by
    calc
      (∫ t in E, A₁ t ^ 2 * A₂ t ^ 2 * A₃ t ^ 2) ≤
          ∫ t in E, K * (F t * G t) := by
        apply setIntegral_mono_on hintLeft (hintProduct.const_mul K) hE
        intro t ht
        have hnonneg : 0 ≤ A₁ t ^ 2 * A₂ t ^ 2 * A₃ t ^ 2 := by
          positivity
        calc
          A₁ t ^ 2 * A₂ t ^ 2 * A₃ t ^ 2 =
              (A₁ t ^ 2 * A₂ t ^ 2 * A₃ t ^ 2) * 1 := by ring
          _ ≤ (A₁ t ^ 2 * A₂ t ^ 2 * A₃ t ^ 2) * (K * B t) :=
            mul_le_mul_of_nonneg_left (hinsert t ht) hnonneg
          _ = K * (F t * G t) := by dsimp [F, G]; ring
      _ = K * ∫ t in E, F t * G t := by
        rw [MeasureTheory.integral_const_mul]
  calc
    (∫ t in E, A₁ t ^ 2 * A₂ t ^ 2 * A₃ t ^ 2) ≤
        K * ∫ t in E, F t * G t := hinserted
    _ ≤ K *
        ((∫ t in E, F t ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫ t in E, G t ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hcauchy hK
    _ = K *
        ((∫ t in E, A₃ t ^ 4 * A₂ t ^ 2) ^ (1 / 2 : ℝ) *
          (∫ t in E, A₁ t ^ 4 * A₂ t ^ 2 * B t ^ 2) ^
            (1 / 2 : ℝ)) := by
      have hFI : (∫ t in E, F t ^ (2 : ℝ)) =
          ∫ t in E, A₃ t ^ 4 * A₂ t ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp [F]
        rw [Real.rpow_two]
        ring
      have hGI : (∫ t in E, G t ^ (2 : ℝ)) =
          ∫ t in E, A₁ t ^ 4 * A₂ t ^ 2 * B t ^ 2 := by
        apply integral_congr_ae
        filter_upwards with t
        dsimp [G]
        rw [Real.rpow_two]
        ring
      rw [hFI, hGI]

/-- Complete source-facing analytic interface for one Type-I/II height
block.  Watt controls the `M₃⁴ M₂²` moment.  The remaining ordinary
mean-value moment is exposed as `hlong`, so no unstated estimate is hidden
inside this theorem. -/
theorem typeIOverII_componentBlockIntegral_le_of_matomakiTeravainen
    (hWatt : MatomakiTeravainenLemmaThreeFivePartOneStatement)
    {eta A N N' T M₁ Q K L : ℝ}
    {beta alpha q : ℕ → ℂ} {E : Set ℝ}
    (heta : 0 < eta) (hA : 1 ≤ A) (hN : 1 ≤ N) (hN' : 1 ≤ N')
    (hT : 1 ≤ T) (hNN' : N < N') (hN'two : N' ≤ 2 * N)
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc T (2 * T))
    (hK : 0 ≤ K)
    (hinsert : ∀ t ∈ E,
      1 ≤ K * ‖dyadicDirichletPolynomial q Q (onePlusIT t)‖)
    (hlong :
      (∫ t in E,
        ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (4 : ℕ) *
          ‖dyadicDirichletPolynomial beta A (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖dyadicDirichletPolynomial q Q (onePlusIT t)‖ ^ (2 : ℕ)) ≤ L) :
    ∃ C : ℝ, 0 < C ∧
      (∫ t in E,
        ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖dyadicDirichletPolynomial beta A (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖matomakiTeravainenZetaSegmentPolynomial N N'
            (onePlusIT t)‖ ^ (2 : ℕ)) ≤
        K *
          ((typeIOverIIWattMajorant C eta A N N' T beta) ^
              (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hWattBound⟩ :=
    typeIOverII_twistedFourthMoment_le_of_matomakiTeravainen hWatt
      heta hA hN hN' hT hNN' hN'two
  refine ⟨C, hC, ?_⟩
  let Long : ℝ → ℝ := fun t ↦
    ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖
  let Middle : ℝ → ℝ := fun t ↦
    ‖dyadicDirichletPolynomial beta A (onePlusIT t)‖
  let Short : ℝ → ℝ := fun t ↦
    ‖matomakiTeravainenZetaSegmentPolynomial N N' (onePlusIT t)‖
  let Inserted : ℝ → ℝ := fun t ↦
    ‖dyadicDirichletPolynomial q Q (onePlusIT t)‖
  have hLongCont : Continuous Long :=
    (Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
      alpha M₁).norm
  have hMiddleCont : Continuous Middle :=
    (Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
      beta A).norm
  have hShortCont : Continuous Short := by
    dsimp [Short]
    exact (Sparse.continuous_dirichletPolynomial_onePlusIT_sparse
      (fun _ ↦ 1) (natOpenClosedInterval N N')).norm
  have hInsertedCont : Continuous Inserted :=
    (Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse q Q).norm
  have hmeasF : AEStronglyMeasurable
      (fun t ↦ Short t ^ 2 * Middle t) (volume.restrict E) :=
    ((hShortCont.pow 2).mul hMiddleCont).aestronglyMeasurable
  have hmeasG : AEStronglyMeasurable
      (fun t ↦ Long t ^ 2 * Middle t * Inserted t)
      (volume.restrict E) :=
    (((hLongCont.pow 2).mul hMiddleCont).mul
      hInsertedCont).aestronglyMeasurable
  have hintF : IntegrableOn
      (fun t ↦ (Short t ^ 2 * Middle t) ^ 2) E :=
    (((hShortCont.pow 2).mul hMiddleCont).pow 2).integrableOn_Icc.mono_set
      hEsub
  have hintG : IntegrableOn
      (fun t ↦ (Long t ^ 2 * Middle t * Inserted t) ^ 2) E :=
    ((((hLongCont.pow 2).mul hMiddleCont).mul hInsertedCont).pow 2)
      |>.integrableOn_Icc.mono_set hEsub
  have hintLeft : IntegrableOn
      (fun t ↦ Long t ^ 2 * Middle t ^ 2 * Short t ^ 2) E :=
    (((hLongCont.pow 2).mul (hMiddleCont.pow 2)).mul
      (hShortCont.pow 2)).integrableOn_Icc.mono_set hEsub
  have hintProduct : IntegrableOn
      (fun t ↦ (Short t ^ 2 * Middle t) *
        (Long t ^ 2 * Middle t * Inserted t)) E :=
    (((hShortCont.pow 2).mul hMiddleCont).mul
      (((hLongCont.pow 2).mul hMiddleCont).mul hInsertedCont))
      |>.integrableOn_Icc.mono_set hEsub
  have hcauchy := typeIOverII_integral_le_inserted_cauchy
    hE hK (fun t ht ↦ norm_nonneg _) (fun t ht ↦ norm_nonneg _)
    (fun t ht ↦ by simpa [Inserted] using hinsert t ht)
    hmeasF hmeasG hintF hintG hintLeft hintProduct
  have hWattCont : Continuous (fun t ↦
      Short t ^ 4 * Middle t ^ 2) :=
    (hShortCont.pow 4).mul (hMiddleCont.pow 2)
  have hWattFull : IntegrableOn (fun t ↦
      Short t ^ 4 * Middle t ^ 2) (Set.Icc T (2 * T)) :=
    hWattCont.integrableOn_Icc
  have hWattNonneg : ∀ t, 0 ≤ Short t ^ 4 * Middle t ^ 2 :=
    fun t ↦ mul_nonneg (pow_nonneg (norm_nonneg _) 4)
      (pow_nonneg (norm_nonneg _) 2)
  have hWattRestrict :
      (∫ t in E, Short t ^ 4 * Middle t ^ 2) ≤
        ∫ t in Set.Icc T (2 * T), Short t ^ 4 * Middle t ^ 2 := by
    apply setIntegral_mono_set hWattFull
    · exact Filter.Eventually.of_forall hWattNonneg
    · exact Filter.Eventually.of_forall hEsub
  have hWattSource :
      (∫ t in E, Short t ^ 4 * Middle t ^ 2) ≤
        typeIOverIIWattMajorant C eta A N N' T beta := by
    refine hWattRestrict.trans ?_
    simpa [Short, Middle] using hWattBound
  have hWattE0 : 0 ≤ ∫ t in E, Short t ^ 4 * Middle t ^ 2 :=
    setIntegral_nonneg hE (fun t ht ↦ hWattNonneg t)
  have hMajorant0 :
      0 ≤ typeIOverIIWattMajorant C eta A N N' T beta :=
    hWattE0.trans hWattSource
  have hLongE0 : 0 ≤ ∫ t in E,
      Long t ^ 4 * Middle t ^ 2 * Inserted t ^ 2 :=
    setIntegral_nonneg hE (fun t ht ↦ by positivity)
  have hL0 : 0 ≤ L := by
    apply hLongE0.trans
    simpa [Long, Middle, Inserted] using hlong
  have hWattHalf := Real.rpow_le_rpow hWattE0 hWattSource
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hLongHalf :
      (∫ t in E, Long t ^ 4 * Middle t ^ 2 * Inserted t ^ 2) ^
          (1 / 2 : ℝ) ≤ L ^ (1 / 2 : ℝ) := by
    apply Real.rpow_le_rpow hLongE0
    · simpa [Long, Middle, Inserted] using hlong
    · norm_num
  have hproduct :
      (∫ t in E, Short t ^ 4 * Middle t ^ 2) ^ (1 / 2 : ℝ) *
          (∫ t in E, Long t ^ 4 * Middle t ^ 2 * Inserted t ^ 2) ^
            (1 / 2 : ℝ) ≤
        (typeIOverIIWattMajorant C eta A N N' T beta) ^ (1 / 2 : ℝ) *
          L ^ (1 / 2 : ℝ) := by
    exact mul_le_mul hWattHalf hLongHalf
      (Real.rpow_nonneg hLongE0 _) (Real.rpow_nonneg hMajorant0 _)
  calc
    (∫ t in E,
        ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖dyadicDirichletPolynomial beta A (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖matomakiTeravainenZetaSegmentPolynomial N N'
            (onePlusIT t)‖ ^ (2 : ℕ)) ≤
        K *
          ((∫ t in E, Short t ^ 4 * Middle t ^ 2) ^ (1 / 2 : ℝ) *
            (∫ t in E,
              Long t ^ 4 * Middle t ^ 2 * Inserted t ^ 2) ^
                (1 / 2 : ℝ)) := by
      simpa [Long, Middle, Short, Inserted] using hcauchy
    _ ≤ K *
        ((typeIOverIIWattMajorant C eta A N N' T beta) ^
            (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hproduct hK

/-! ## The ordinary mean-value input used for the second moment -/

/-- The exact upper majorant obtained from MT23, Lemma 3.2 at height `2T`.
The leading term is `4T` because the cited integral is over `[-2T,2T]`. -/
def typeIOverIIMeanSquareMajorant
    (C N T : ℝ) (a : ℕ → ℂ) : ℝ :=
  (4 * T + C * N) *
    ∑ n ∈ natOpenClosedInterval 0 N, ‖a n‖ ^ (2 : ℕ)

/-- Source-closed upper-bound form of the ordinary mean-value theorem on
the symmetric block containing `[T,2T]`. -/
theorem typeIOverII_initialMeanSquare_le_of_matomakiTeravainen
    (hMV : MatomakiTeravainenLemmaThreeTwoStatement)
    {N T : ℝ} {a : ℕ → ℂ} (hN : 1 ≤ N) (hT : 1 ≤ T) :
    ∃ C : ℝ, 0 < C ∧
      (∫ t in Set.Icc (-2 * T) (2 * T),
        ‖matomakiTeravainenInitialDirichletPolynomial a N
          ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)) ≤
        typeIOverIIMeanSquareMajorant C N T a := by
  obtain ⟨C, hC, hsource⟩ := hMV
  refine ⟨C, hC, ?_⟩
  have h2T : 1 ≤ 2 * T := by linarith
  have h := hsource N (2 * T) a hN h2T
  let S : ℝ := ∑ n ∈ natOpenClosedInterval 0 N, ‖a n‖ ^ (2 : ℕ)
  let I : ℝ := ∫ t in Set.Icc (-2 * T) (2 * T),
    ‖matomakiTeravainenInitialDirichletPolynomial a N
      ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)
  have herror : |I - 2 * (2 * T) * S| ≤ C * N * S := by
    simpa [I, S] using h
  have hupper : I - 2 * (2 * T) * S ≤ C * N * S :=
    (le_abs_self (I - 2 * (2 * T) * S)).trans herror
  dsimp [typeIOverIIMeanSquareMajorant, I, S]
  linarith

/-! ## Endpoint arithmetic independent of Watt's estimate

The analytic estimate is a cited input.  The declarations below formalize
only the elementary power checks performed after that input has produced its
displayed exponent.
-/

/-- At the endpoint `a = 35/32`, the factor `(1 - 1/a)/4` equals
`3/140`; it is strictly larger as soon as `a` is strictly larger than the
endpoint. -/
theorem typeIOverII_endpoint_lower_bound {a : ℝ}
    (ha : 35 / 32 < a) :
    3 / 140 < (1 - 1 / a) / 4 := by
  have hEndpointPos : (0 : ℝ) < 35 / 32 := by norm_num
  have hReciprocal : 1 / a < 1 / (35 / 32 : ℝ) :=
    one_div_lt_one_div_of_lt hEndpointPos ha
  norm_num at hReciprocal ⊢
  linarith

/-- The numerical separation used in the paper is not merely positive:
`3/140 - 1/100 = 2/175`. -/
theorem three_over_oneForty_gt_one_over_oneHundred :
    (1 / 100 : ℝ) < 3 / 140 := by
  norm_num

/-- The two strict inequalities displayed in the repaired paper. -/
theorem typeIOverII_endpoint_chain {a : ℝ}
    (ha : 35 / 32 < a) :
    (1 / 100 : ℝ) < 3 / 140 ∧
      3 / 140 < (1 - 1 / a) / 4 :=
  ⟨three_over_oneForty_gt_one_over_oneHundred,
    typeIOverII_endpoint_lower_bound ha⟩

/-- The buffered paper hypothesis supplies the strict endpoint inequality. -/
theorem typeIOverII_endpoint_chain_of_buffer {a eta : ℝ}
    (heta : 0 < eta) (ha : 35 / 32 + eta ≤ a) :
    (1 / 100 : ℝ) < 3 / 140 ∧
      3 / 140 < (1 - 1 / a) / 4 := by
  apply typeIOverII_endpoint_chain
  linarith

/-- After subtracting the positive `epsilon/100` term, the Watt exponent
still has a uniform gap greater than `2/175`. -/
theorem typeIOverII_uniform_power_gap {a : ℝ}
    (ha : 35 / 32 < a) :
    (2 / 175 : ℝ) < (1 - 1 / a) / 4 - 1 / 100 := by
  have hmain := typeIOverII_endpoint_lower_bound ha
  norm_num at hmain ⊢
  linarith

/-! ## Explicit error reservations -/

/-- If the total error in Watt's exponent is at most `epsilon/175`, then
the exponent is in fact strictly smaller than `-epsilon/175`.  This exposes
the power saving hidden by the paper's `O(epsilon^2)` notation. -/
theorem typeIOverII_exponent_lt_neg_margin
    {a epsilon error : ℝ}
    (ha : 35 / 32 < a) (hepsilon : 0 < epsilon)
    (herror : error ≤ epsilon / 175) :
    -epsilon * ((1 - 1 / a) / 4) + epsilon / 100 + error <
      -epsilon / 175 := by
  have hgap := typeIOverII_uniform_power_gap ha
  have hscaled :
      epsilon * (2 / 175 : ℝ) <
        epsilon * ((1 - 1 / a) / 4 - 1 / 100) :=
    mul_lt_mul_of_pos_left hgap hepsilon
  nlinarith

/-- In particular, the reserved-margin Watt exponent is negative. -/
theorem typeIOverII_exponent_neg
    {a epsilon error : ℝ}
    (ha : 35 / 32 < a) (hepsilon : 0 < epsilon)
    (herror : error ≤ epsilon / 175) :
    -epsilon * ((1 - 1 / a) / 4) + epsilon / 100 + error < 0 := by
  have hmargin :=
    typeIOverII_exponent_lt_neg_margin ha hepsilon herror
  have hnegative : -epsilon / 175 < 0 := by nlinarith
  exact hmargin.trans hnegative

/-- An explicit smallness condition converts a quadratic error bound
`error ≤ C * epsilon^2` into the linear margin required above. -/
theorem quadratic_error_le_typeIOverII_margin
    {C epsilon error : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hsmall : C * epsilon ≤ 1 / 175)
    (herror : error ≤ C * epsilon ^ 2) :
    error ≤ epsilon / 175 := by
  calc
    error ≤ C * epsilon ^ 2 := herror
    _ = epsilon * (C * epsilon) := by ring
    _ ≤ epsilon * (1 / 175) :=
      mul_le_mul_of_nonneg_left hsmall hepsilon
    _ = epsilon / 175 := by ring

/-- The complete elementary `O(epsilon^2)` check: once
`C * epsilon ≤ 1/175`, an error bounded by `C * epsilon^2` leaves a
strictly negative exponent. -/
theorem typeIOverII_exponent_neg_of_quadratic_error
    {a C epsilon error : ℝ}
    (ha : 35 / 32 < a) (hepsilon : 0 < epsilon)
    (hsmall : C * epsilon ≤ 1 / 175)
    (herror : error ≤ C * epsilon ^ 2) :
    -epsilon * ((1 - 1 / a) / 4) + epsilon / 100 + error < 0 := by
  apply typeIOverII_exponent_neg ha hepsilon
  exact quadratic_error_le_typeIOverII_margin hepsilon.le hsmall herror

/-- Paper-parameter version of the preceding result.  The positive buffer
`eta` supplies the strict endpoint inequality uniformly for every
`a ≥ 35/32 + eta`. -/
theorem typeIOverII_exponent_neg_of_buffered_quadratic_error
    {a eta C epsilon error : ℝ}
    (heta : 0 < eta) (ha : 35 / 32 + eta ≤ a)
    (hepsilon : 0 < epsilon)
    (hsmall : C * epsilon ≤ 1 / 175)
    (herror : error ≤ C * epsilon ^ 2) :
    -epsilon * ((1 - 1 / a) / 4) + epsilon / 100 + error < 0 := by
  apply typeIOverII_exponent_neg_of_quadratic_error (a := a)
    (C := C) (epsilon := epsilon) (error := error)
  · linarith
  · exact hepsilon
  · exact hsmall
  · exact herror

/-- The unchanged Type-I exponent has the corresponding endpoint saving
`(1-1/a)/20 > 3/700`. -/
theorem typeI_endpoint_lower_bound {a : ℝ}
    (ha : 35 / 32 < a) :
    3 / 700 < (1 - 1 / a) / 20 := by
  have hmain := typeIOverII_endpoint_lower_bound ha
  linarith

/-- Reserving half of the endpoint Type-I gap makes its exponent negative. -/
theorem typeI_exponent_neg_of_error_bound {a error : ℝ}
    (ha : 35 / 32 < a) (herror : error ≤ 3 / 1400) :
    -(1 - 1 / a) / 20 + error < 0 := by
  have hmain := typeI_endpoint_lower_bound ha
  linarith

/-! ## Exact residual localization-and-energy bridge -/

/-- The one internal statement still required after the source-closed
factorization, Watt block estimate, ordinary mean-value estimate, and
Cauchy--Schwarz insertion proved above.

Its proof is finite and local: choose
`k = ceil (log (T^(epsilon/2)) / log P₁)`, expand `P₁(s)^k`, split it
into the endpoint-compatible dyadic pieces from
`TypeII.OpenClosedDyadicSlices`, establish the coefficient estimate (5.4),
collect the coefficients of `M₁(s)^2 M₂(s) M(s)`, and apply MT23
Lemma 3.2.  The displayed scale hypotheses are precisely Proposition
2.2(ii).  This is a definition, not an axiom or an external input. -/
def TypeIOneHalfPrimePowerLocalizationAndEnergyStatement : Prop :=
  ∀ a error epsilon Bcoeff Acoeff : ℝ,
    35 / 32 < a → 0 < error → 0 < epsilon →
    0 ≤ Bcoeff → 1 ≤ Acoeff →
    ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧
      ∀ (X P₁ T M₁ M₂ M₃ delta : ℝ) (alpha beta : ℕ → ℂ)
          (E : Set ℝ),
        X₀ ≤ X → P₁ = (Real.log X) ^ a → 1 ≤ P₁ →
        X ^ (1 / 1000 : ℝ) ≤ T → T ≤ X →
        0 ≤ delta → delta ≤ 1 →
        0 < M₁ → 0 < M₂ → 0 < M₃ →
        M₁ ^ (2 : ℕ) * M₂ ≤ X ^ (1 - epsilon) →
        M₂ ≤ X ^ (1 / 4 - epsilon) →
        X / (2 * P₁) < M₁ * M₂ * M₃ →
        M₁ * M₂ * M₃ ≤ 4 * X / P₁ →
        MeasurableSet E → E ⊆ Set.Icc T (2 * T) →
        IsDivisorBoundedByConstant Bcoeff Acoeff alpha →
        IsDivisorBoundedByConstant Bcoeff Acoeff beta →
        (∀ t ∈ E,
          P₁ ^ (-epsilon / 10) ≤
            ‖primeDirichletPolynomial P₁ (onePlusIT t)‖) →
        (∫ t in E,
          ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (2 : ℕ) *
            ‖dyadicDirichletPolynomial beta M₂ (onePlusIT t)‖ ^ (2 : ℕ) *
            ‖matomakiTeravainenZetaSegmentPolynomial M₃
              ((1 + delta) * M₃) (onePlusIT t)‖ ^ (2 : ℕ)) ≤
          C * X ^
            (-epsilon * ((1 - 1 / a) / 4) + epsilon / 100 + error)

/-- Once the explicit localization-and-energy bridge is supplied, the
already checked endpoint gap turns its source exponent into a uniform fixed
power saving for every Type-I/II component. -/
theorem typeIOverII_component_powerSaving_of_localizationAndEnergy
    (hlocal : TypeIOneHalfPrimePowerLocalizationAndEnergyStatement)
    {a error epsilon Bcoeff Acoeff : ℝ}
    (ha : 35 / 32 < a) (herrorPos : 0 < error) (hepsilon : 0 < epsilon)
    (herror : error ≤ epsilon / 175)
    (hBcoeff : 0 ≤ Bcoeff) (hAcoeff : 1 ≤ Acoeff) :
    ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧
      ∀ (X P₁ T M₁ M₂ M₃ delta : ℝ) (alpha beta : ℕ → ℂ)
          (E : Set ℝ),
        X₀ ≤ X → P₁ = (Real.log X) ^ a → 1 ≤ P₁ →
        X ^ (1 / 1000 : ℝ) ≤ T → T ≤ X →
        0 ≤ delta → delta ≤ 1 →
        0 < M₁ → 0 < M₂ → 0 < M₃ →
        M₁ ^ (2 : ℕ) * M₂ ≤ X ^ (1 - epsilon) →
        M₂ ≤ X ^ (1 / 4 - epsilon) →
        X / (2 * P₁) < M₁ * M₂ * M₃ →
        M₁ * M₂ * M₃ ≤ 4 * X / P₁ →
        MeasurableSet E → E ⊆ Set.Icc T (2 * T) →
        IsDivisorBoundedByConstant Bcoeff Acoeff alpha →
        IsDivisorBoundedByConstant Bcoeff Acoeff beta →
        (∀ t ∈ E,
          P₁ ^ (-epsilon / 10) ≤
            ‖primeDirichletPolynomial P₁ (onePlusIT t)‖) →
        (∫ t in E,
          ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (2 : ℕ) *
            ‖dyadicDirichletPolynomial beta M₂ (onePlusIT t)‖ ^ (2 : ℕ) *
            ‖matomakiTeravainenZetaSegmentPolynomial M₃
              ((1 + delta) * M₃) (onePlusIT t)‖ ^ (2 : ℕ)) ≤
          C * X ^ (-epsilon / 175 : ℝ) := by
  obtain ⟨C, X₀, hC, hX₀, hbound⟩ :=
    hlocal a error epsilon Bcoeff Acoeff ha herrorPos hepsilon
      hBcoeff hAcoeff
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X P₁ T M₁ M₂ M₃ delta alpha beta E hX hP₁ hP₁one
    hTlower hTupper hdelta hdeltaOne hM₁ hM₂ hM₃ hscale hM₂upper
    hprodLower hprodUpper hE hEsub halpha hbeta hlarge
  have hraw := hbound X P₁ T M₁ M₂ M₃ delta alpha beta E
    hX hP₁ hP₁one hTlower hTupper hdelta hdeltaOne hM₁ hM₂ hM₃
    hscale hM₂upper hprodLower hprodUpper hE hEsub halpha hbeta hlarge
  have hXone : 1 ≤ X := by linarith [hX₀.trans hX]
  have hexp :
      -epsilon * ((1 - 1 / a) / 4) + epsilon / 100 + error ≤
        -epsilon / 175 :=
    (typeIOverII_exponent_lt_neg_margin ha hepsilon herror).le
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hXone hexp) hC.le)

def typeIOverIIClosureModule : ProofModule :=
  { name := "Completion.TypeIOverIIClosure"
    paperLocation := "Proof of Proposition 7.1, Type-I/II power check"
    purpose :=
      "Prove the exact Type-I/II convolution factorization, the literal Watt and ordinary mean-value specializations, the inserted Cauchy--Schwarz block interface, and the endpoint power gap. The main theorem uses the labelled extension E5 for this component."
    dependsOn :=
      [ "Completion.PerronTarget",
        "Sparse.GlobalComponentCancellation",
        "Assumptions.wattEquationFourSeven",
        "Assumptions.matomakiTeravainenLemmaThreeTwo" ]
    status := .superseded }

end

end Completion
end ExactSemiprimes
