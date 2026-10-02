import ExactSemiprimes.Completion.TypeIOverIIClosure
import ExactSemiprimes.Completion.TypeIPrimePowerEnergy
import ExactSemiprimes.TypeII.PoweredMeanValue

/-!
# Collected Type-I/II slice and the ordinary mean value theorem

For one dyadic slice of the inserted prime-polynomial power, the second
Cauchy moment is the mean square of

`M₁(s)^2 M₂(s) Slice(s)`.

This file defines its nested convolution coefficient and support, proves
the exact finite-polynomial factorization, moves the product from
`Re(s)=1` to the zero line, and applies MT23, Lemma 3.2 with its literal
coefficient energy.  The later sections propagate divisor bounds through
the nested convolution and prove the resulting uniform subpower energy
envelope separately from the mean-value application.
-/

namespace ExactSemiprimes
namespace Completion

open MeasureTheory
open scoped BigOperators

noncomputable section

def typeIOverIIAlphaSquareSupport (M₁ : ℝ) : Finset ℕ :=
  (TypeII.powerTuples (dyadicInterval M₁) 2).image TypeII.tupleProduct

def typeIOverIIAlphaSquareCoefficient
    (alpha : ℕ → ℂ) (M₁ : ℝ) : ℕ → ℂ :=
  TypeII.powerConvolutionCoefficient alpha (dyadicInterval M₁) 2

def typeIOverIIFirstTwoSupport (M₁ M₂ : ℝ) : Finset ℕ :=
  ((typeIOverIIAlphaSquareSupport M₁).product (dyadicInterval M₂)).image
    fun p ↦ p.1 * p.2

def typeIOverIIFirstTwoCoefficient
    (alpha beta : ℕ → ℂ) (M₁ M₂ : ℝ) : ℕ → ℂ :=
  Sparse.binaryConvolutionCoefficient
    (typeIOverIIAlphaSquareCoefficient alpha M₁) beta
    (typeIOverIIAlphaSquareSupport M₁) (dyadicInterval M₂)

def typeIOverIICompositeSliceSupport
    (M₁ M₂ Q : ℝ) : Finset ℕ :=
  ((typeIOverIIFirstTwoSupport M₁ M₂).product (dyadicInterval Q)).image
    fun p ↦ p.1 * p.2

def typeIOverIICompositeSliceCoefficient
    (alpha beta q : ℕ → ℂ) (M₁ M₂ Q : ℝ) : ℕ → ℂ :=
  Sparse.binaryConvolutionCoefficient
    (typeIOverIIFirstTwoCoefficient alpha beta M₁ M₂) q
    (typeIOverIIFirstTwoSupport M₁ M₂) (dyadicInterval Q)

/-- Exact collection of the three factors, with the first factor squared. -/
theorem typeIOverIICompositeSlice_polynomial_factorization
    (alpha beta q : ℕ → ℂ) (M₁ M₂ Q : ℝ) (s : ℂ) :
    dirichletPolynomial
        (typeIOverIICompositeSliceCoefficient alpha beta q M₁ M₂ Q)
        (typeIOverIICompositeSliceSupport M₁ M₂ Q) s =
      dyadicDirichletPolynomial alpha M₁ s ^ (2 : ℕ) *
        dyadicDirichletPolynomial beta M₂ s *
        dyadicDirichletPolynomial q Q s := by
  symm
  calc
    dyadicDirichletPolynomial alpha M₁ s ^ (2 : ℕ) *
          dyadicDirichletPolynomial beta M₂ s *
          dyadicDirichletPolynomial q Q s =
        (dirichletPolynomial
            (typeIOverIIAlphaSquareCoefficient alpha M₁)
            (typeIOverIIAlphaSquareSupport M₁) s *
          dirichletPolynomial beta (dyadicInterval M₂) s) *
          dirichletPolynomial q (dyadicInterval Q) s := by
      rw [show dyadicDirichletPolynomial alpha M₁ s ^ (2 : ℕ) =
          dirichletPolynomial
            (typeIOverIIAlphaSquareCoefficient alpha M₁)
            (typeIOverIIAlphaSquareSupport M₁) s by
        exact TypeII.dirichletPolynomial_pow_eq_convolution_image
          alpha (dyadicInterval M₁) s 2]
      rfl
    _ = dirichletPolynomial
          (typeIOverIIFirstTwoCoefficient alpha beta M₁ M₂)
          (typeIOverIIFirstTwoSupport M₁ M₂) s *
        dirichletPolynomial q (dyadicInterval Q) s := by
      rw [Sparse.dirichletPolynomial_mul_eq_binaryConvolution]
      rfl
    _ = dirichletPolynomial
          (typeIOverIICompositeSliceCoefficient alpha beta q M₁ M₂ Q)
          (typeIOverIICompositeSliceSupport M₁ M₂ Q) s := by
      rw [Sparse.dirichletPolynomial_mul_eq_binaryConvolution]
      rfl

/-- A convenient source length enclosing the whole nested product support. -/
def typeIOverIICompositeSliceLength (M₁ M₂ Q : ℝ) : ℝ :=
  (2 * M₁) ^ (2 : ℕ) * (2 * M₂) * (2 * Q)

def typeIOverIICompositeSliceLineZeroCoefficient
    (alpha beta q : ℕ → ℂ) (M₁ M₂ Q : ℝ) (n : ℕ) : ℂ :=
  typeIOverIICompositeSliceCoefficient alpha beta q M₁ M₂ Q n /
    (n : ℂ)

def typeIOverIICompositeSliceEnergy
    (alpha beta q : ℕ → ℂ) (M₁ M₂ Q : ℝ) : ℝ :=
  ∑ n ∈ natOpenClosedInterval 0 (typeIOverIICompositeSliceLength M₁ M₂ Q),
    ‖typeIOverIICompositeSliceLineZeroCoefficient
      alpha beta q M₁ M₂ Q n‖ ^ (2 : ℕ)

/-! ## Divisor-bound propagation through a binary convolution -/

/-- A deliberately robust binary-convolution bound.  We count a product
fibre by `d(n)^2`; the extra divisor power is harmless and makes no
injectivity choice necessary. -/
theorem binaryConvolutionCoefficient_isDivisorBoundedByConstant
    {a b : ℕ → ℂ} {S₁ S₂ : Finset ℕ}
    {B₁ B₂ A₁ A₂ : ℝ}
    (ha : IsDivisorBoundedByConstant B₁ A₁ a)
    (hb : IsDivisorBoundedByConstant B₂ A₂ b) :
    IsDivisorBoundedByConstant (B₁ + B₂ + 2) (A₁ * A₂)
      (Sparse.binaryConvolutionCoefficient a b S₁ S₂) := by
  refine ⟨by linarith [ha.1, hb.1], mul_pos ha.2.1 hb.2.1, ?_⟩
  intro n hn
  classical
  let pairs : Finset (ℕ × ℕ) :=
    (S₁.product S₂).filter fun p ↦ p.1 * p.2 = n
  have hpairSubset : pairs ⊆ n.divisors.product n.divisors := by
    intro p hp
    have hprod : p.1 * p.2 = n := (Finset.mem_filter.mp hp).2
    have hp₁dvd : p.1 ∣ n := ⟨p.2, hprod.symm⟩
    have hp₂dvd : p.2 ∣ n := ⟨p.1, by simpa [mul_comm] using hprod.symm⟩
    exact Finset.mem_product.mpr
      ⟨Nat.mem_divisors.mpr ⟨hp₁dvd, hn.ne'⟩,
        Nat.mem_divisors.mpr ⟨hp₂dvd, hn.ne'⟩⟩
  have hpairs : (pairs.card : ℝ) ≤ (divisorCount n : ℝ) ^ (2 : ℕ) := by
    have hcard := Finset.card_le_card hpairSubset
    have hcard' : pairs.card ≤ divisorCount n * divisorCount n := by
      simpa [Finset.card_product, divisorCount] using hcard
    have hcardPow : pairs.card ≤ divisorCount n ^ (2 : ℕ) := by
      simpa [pow_two] using hcard'
    exact_mod_cast hcardPow
  have hdNat : 1 ≤ divisorCount n := by
    unfold divisorCount
    exact Finset.one_le_card.mpr
      ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩
  have hd : (1 : ℝ) ≤ (divisorCount n : ℝ) := by exact_mod_cast hdNat
  have hpowTwo : (divisorCount n : ℝ) ^ (2 : ℕ) =
      (divisorCount n : ℝ) ^ (2 : ℝ) :=
    (Real.rpow_natCast (divisorCount n : ℝ) 2).symm
  have hterm : ∀ p ∈ pairs,
      ‖a p.1 * b p.2‖ ≤
        A₁ * A₂ * (divisorCount n : ℝ) ^ (B₁ + B₂) := by
    intro p hp
    have hprod : p.1 * p.2 = n := (Finset.mem_filter.mp hp).2
    have hp₁dvd : p.1 ∣ n := ⟨p.2, hprod.symm⟩
    have hp₂dvd : p.2 ∣ n := ⟨p.1, by simpa [mul_comm] using hprod.symm⟩
    have hp₁pos : 0 < p.1 :=
      Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hn.ne' hp₁dvd)
    have hp₂pos : 0 < p.2 :=
      Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hn.ne' hp₂dvd)
    have hcard₁ : divisorCount p.1 ≤ divisorCount n := by
      unfold divisorCount
      exact Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' hp₁dvd)
    have hcard₂ : divisorCount p.2 ≤ divisorCount n := by
      unfold divisorCount
      exact Finset.card_le_card (Nat.divisors_subset_of_dvd hn.ne' hp₂dvd)
    have ha' : ‖a p.1‖ ≤ A₁ * (divisorCount n : ℝ) ^ B₁ :=
      (ha.2.2 p.1 hp₁pos).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hcard₁) ha.1)
        ha.2.1.le)
    have hb' : ‖b p.2‖ ≤ A₂ * (divisorCount n : ℝ) ^ B₂ :=
      (hb.2.2 p.2 hp₂pos).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hcard₂) hb.1)
        hb.2.1.le)
    rw [norm_mul]
    calc
      ‖a p.1‖ * ‖b p.2‖ ≤
          (A₁ * (divisorCount n : ℝ) ^ B₁) *
            (A₂ * (divisorCount n : ℝ) ^ B₂) :=
        mul_le_mul ha' hb' (norm_nonneg _)
          (mul_nonneg ha.2.1.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      _ = A₁ * A₂ * (divisorCount n : ℝ) ^ (B₁ + B₂) := by
        rw [Real.rpow_add (lt_of_lt_of_le zero_lt_one hd)]
        ring
  change ‖∑ p ∈ pairs, a p.1 * b p.2‖ ≤ _
  calc
    ‖∑ p ∈ pairs, a p.1 * b p.2‖ ≤
        ∑ p ∈ pairs, ‖a p.1 * b p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ pairs,
        A₁ * A₂ * (divisorCount n : ℝ) ^ (B₁ + B₂) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hterm p hp
    _ = (pairs.card : ℝ) *
        (A₁ * A₂ * (divisorCount n : ℝ) ^ (B₁ + B₂)) := by
      simp
    _ ≤ (divisorCount n : ℝ) ^ (2 : ℕ) *
        (A₁ * A₂ * (divisorCount n : ℝ) ^ (B₁ + B₂)) :=
      mul_le_mul_of_nonneg_right hpairs
        (mul_nonneg (mul_pos ha.2.1 hb.2.1).le
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    _ = A₁ * A₂ *
        ((divisorCount n : ℝ) ^ (B₁ + B₂) *
          (divisorCount n : ℝ) ^ (2 : ℝ)) := by
      rw [hpowTwo]
      ring
    _ = A₁ * A₂ *
        (divisorCount n : ℝ) ^ (B₁ + B₂ + 2) := by
      rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hd)]

/-- The raw inserted prime-power coefficient has the uniform constant
`k!` and needs no divisor power. -/
theorem rawPrimePowerCoefficient_isDivisorBoundedByConstant
    {S : Finset ℕ} {k : ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) :
    IsDivisorBoundedByConstant 0 (k.factorial : ℝ)
      (rawPrimePowerCoefficient S k) := by
  refine ⟨by norm_num, by positivity, ?_⟩
  intro n hn
  simpa using
    (norm_rawPrimePowerCoefficient_le_factorial
      (S := S) (k := k) (n := n) hS)

/-- The exact divisor-bound bookkeeping for the coefficient collected from
`alpha^2`, `beta`, and one raw prime-power slice.  The two deliberately
robust binary fibre counts cost two divisor powers each. -/
theorem typeIOverIICompositeSliceCoefficient_isDivisorBoundedByConstant
    {alpha beta : ℕ → ℂ} {S : Finset ℕ}
    {B₀ A₀ M₁ M₂ Q : ℝ} {k : ℕ}
    (halpha : IsDivisorBoundedByConstant B₀ A₀ alpha)
    (hbeta : IsDivisorBoundedByConstant B₀ A₀ beta)
    (hS : ∀ p ∈ S, Nat.Prime p) :
    IsDivisorBoundedByConstant (3 * B₀ + 5)
      (A₀ ^ (3 : ℕ) * (k.factorial : ℝ))
      (typeIOverIICompositeSliceCoefficient alpha beta
        (rawPrimePowerCoefficient S k) M₁ M₂ Q) := by
  have hsquare :=
    TypeII.powerConvolutionCoefficient_isDivisorBoundedByConstant
      (S := dyadicInterval M₁) (ℓ := 2) (by omega) halpha
  have hfirst :=
    binaryConvolutionCoefficient_isDivisorBoundedByConstant
      (S₁ := typeIOverIIAlphaSquareSupport M₁)
      (S₂ := dyadicInterval M₂) hsquare hbeta
  have hraw := rawPrimePowerCoefficient_isDivisorBoundedByConstant
    (S := S) (k := k) hS
  have hcomposite :=
    binaryConvolutionCoefficient_isDivisorBoundedByConstant
      (S₁ := typeIOverIIFirstTwoSupport M₁ M₂)
      (S₂ := dyadicInterval Q) hfirst hraw
  change IsDivisorBoundedByConstant (3 * B₀ + 5)
    (A₀ ^ (3 : ℕ) * (k.factorial : ℝ))
    (Sparse.binaryConvolutionCoefficient
      (Sparse.binaryConvolutionCoefficient
        (TypeII.powerConvolutionCoefficient alpha (dyadicInterval M₁) 2)
        beta (typeIOverIIAlphaSquareSupport M₁) (dyadicInterval M₂))
      (rawPrimePowerCoefficient S k)
      (typeIOverIIFirstTwoSupport M₁ M₂) (dyadicInterval Q))
  convert hcomposite using 1 <;> ring

theorem typeIOverIIAlphaSquareSupport_bounds
    {M₁ : ℝ} (hM₁ : 0 < M₁)
    {n : ℕ} (hn : n ∈ typeIOverIIAlphaSquareSupport M₁) :
    M₁ ^ (2 : ℕ) ≤ (n : ℝ) ∧
      (n : ℝ) ≤ (2 * M₁) ^ (2 : ℕ) := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hn
  exact TypeII.tupleProduct_mem_poweredSupport hM₁.le hf
    (fun m hm ↦ (mem_dyadicInterval hM₁.le).mp hm)

theorem typeIOverIIFirstTwoSupport_bounds
    {M₁ M₂ : ℝ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    {n : ℕ} (hn : n ∈ typeIOverIIFirstTwoSupport M₁ M₂) :
    M₁ ^ (2 : ℕ) * M₂ < (n : ℝ) ∧
      (n : ℝ) ≤ (2 * M₁) ^ (2 : ℕ) * (2 * M₂) := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
  have hfirst := typeIOverIIAlphaSquareSupport_bounds hM₁ hp₁
  have hsecond := (mem_dyadicInterval hM₂.le).mp hp₂
  have hp₁pos : 0 < (p.1 : ℝ) :=
    (pow_pos hM₁ (2 : ℕ)).trans_le hfirst.1
  rw [Nat.cast_mul]
  constructor
  · exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hfirst.1 hM₂.le)
      (mul_lt_mul_of_pos_left hsecond.1 hp₁pos)
  · exact mul_le_mul hfirst.2 hsecond.2 (Nat.cast_nonneg _)
      (by positivity)

theorem typeIOverIICompositeSliceSupport_bounds
    {M₁ M₂ Q : ℝ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hQ : 0 < Q)
    {n : ℕ} (hn : n ∈ typeIOverIICompositeSliceSupport M₁ M₂ Q) :
    M₁ ^ (2 : ℕ) * M₂ * Q < (n : ℝ) ∧
      (n : ℝ) ≤ typeIOverIICompositeSliceLength M₁ M₂ Q := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
  have hfirst := typeIOverIIFirstTwoSupport_bounds hM₁ hM₂ hp₁
  have hthird := (mem_dyadicInterval hQ.le).mp hp₂
  have hp₁pos : 0 < (p.1 : ℝ) :=
    (by positivity : 0 < M₁ ^ (2 : ℕ) * M₂) |>.trans hfirst.1
  rw [Nat.cast_mul]
  constructor
  · exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hfirst.1.le hQ.le)
      (mul_lt_mul_of_pos_left hthird.1 hp₁pos)
  · unfold typeIOverIICompositeSliceLength
    exact mul_le_mul hfirst.2 hthird.2 (Nat.cast_nonneg _) (by positivity)

theorem typeIOverIICompositeSliceSupport_subset_initial
    {M₁ M₂ Q : ℝ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hQ : 0 < Q) :
    typeIOverIICompositeSliceSupport M₁ M₂ Q ⊆
      natOpenClosedInterval 0
        (typeIOverIICompositeSliceLength M₁ M₂ Q) := by
  intro n hn
  have hb := typeIOverIICompositeSliceSupport_bounds hM₁ hM₂ hQ hn
  rw [mem_natOpenClosedInterval (by norm_num) (by
    unfold typeIOverIICompositeSliceLength
    positivity)]
  exact ⟨(by
    have hlower : 0 < M₁ ^ (2 : ℕ) * M₂ * Q := by positivity
    exact hlower.trans hb.1), hb.2⟩

/-- Uniform subpower control of every collected coefficient on its literal
finite product support.  The constant is chosen before all coefficient
sequences, dyadic scales, and the slice index. -/
theorem exists_uniform_typeIOverIICompositeSliceCoefficient_bound_subpower
    {B₀ rho : ℝ} {k : ℕ}
    (hB₀ : 0 ≤ B₀) (hrho : 0 < rho) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ (alpha beta : ℕ → ℂ) (A₀ M₁ M₂ P : ℝ) (j : ℕ),
        1 ≤ A₀ → 1 ≤ M₁ → 1 ≤ M₂ → 1 ≤ P →
        IsDivisorBoundedByConstant B₀ A₀ alpha →
        IsDivisorBoundedByConstant B₀ A₀ beta →
        let Q : ℝ := (2 : ℝ) ^ j * P ^ k
        ∀ n ∈ typeIOverIICompositeSliceSupport M₁ M₂ Q,
          ‖typeIOverIICompositeSliceCoefficient alpha beta
              (rawPrimePowerCoefficient (dyadicPrimes P) k)
              M₁ M₂ Q n‖ ≤
            A₀ ^ (3 : ℕ) * (k.factorial : ℝ) * D *
              (typeIOverIICompositeSliceLength M₁ M₂ Q) ^ rho := by
  have hE : 0 ≤ 3 * B₀ + 5 := by linarith
  obtain ⟨D, hD, hdivisor⟩ :=
    Hybrid.globalDivisorSubpower (3 * B₀ + 5) rho hE hrho
  refine ⟨D, hD, ?_⟩
  intro alpha beta A₀ M₁ M₂ P j hA₀ hM₁ hM₂ hP halpha hbeta
  dsimp only
  intro n hn
  have hM₁pos : 0 < M₁ := zero_lt_one.trans_le hM₁
  have hM₂pos : 0 < M₂ := zero_lt_one.trans_le hM₂
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hQpos : 0 < (2 : ℝ) ^ j * P ^ k := by positivity
  have hbounds := typeIOverIICompositeSliceSupport_bounds
    hM₁pos hM₂pos hQpos hn
  have hnposReal : 0 < (n : ℝ) := by
    have hlower : 0 < M₁ ^ (2 : ℕ) * M₂ * ((2 : ℝ) ^ j * P ^ k) := by
      positivity
    exact hlower.trans hbounds.1
  have hnpos : 0 < n := by exact_mod_cast hnposReal
  have hSprime : ∀ p ∈ dyadicPrimes P, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hcomposite :=
    typeIOverIICompositeSliceCoefficient_isDivisorBoundedByConstant
      (k := k) (M₁ := M₁) (M₂ := M₂)
      (Q := (2 : ℝ) ^ j * P ^ k)
      halpha hbeta hSprime
  have hraw := hcomposite.2.2 n hnpos
  have hdivisorAt := hdivisor n hnpos
  have hnRpow : (n : ℝ) ^ rho ≤
      (typeIOverIICompositeSliceLength M₁ M₂
        ((2 : ℝ) ^ j * P ^ k)) ^ rho :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) hbounds.2 hrho.le
  have hconstant :
      0 ≤ A₀ ^ (3 : ℕ) * (k.factorial : ℝ) := by positivity
  calc
    ‖typeIOverIICompositeSliceCoefficient alpha beta
        (rawPrimePowerCoefficient (dyadicPrimes P) k)
        M₁ M₂ ((2 : ℝ) ^ j * P ^ k) n‖ ≤
        (A₀ ^ (3 : ℕ) * (k.factorial : ℝ)) *
          (divisorCount n : ℝ) ^ (3 * B₀ + 5) := hraw
    _ ≤ (A₀ ^ (3 : ℕ) * (k.factorial : ℝ)) *
          (D * (n : ℝ) ^ rho) :=
      mul_le_mul_of_nonneg_left hdivisorAt hconstant
    _ ≤ (A₀ ^ (3 : ℕ) * (k.factorial : ℝ)) *
          (D * (typeIOverIICompositeSliceLength M₁ M₂
            ((2 : ℝ) ^ j * P ^ k)) ^ rho) := by
      gcongr
    _ = A₀ ^ (3 : ℕ) * (k.factorial : ℝ) * D *
          (typeIOverIICompositeSliceLength M₁ M₂
            ((2 : ℝ) ^ j * P ^ k)) ^ rho := by ring

/-- The elementary passage from a pointwise bound on the collected
coefficient to the exact zero-line energy in Lemma 3.2. -/
theorem typeIOverIICompositeSliceEnergy_le_of_coefficient_bound
    {alpha beta q : ℕ → ℂ} {M₁ M₂ Q B : ℝ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hQ : 0 < Q) (hB : 0 ≤ B)
    (hcoeff : ∀ n ∈ typeIOverIICompositeSliceSupport M₁ M₂ Q,
      ‖typeIOverIICompositeSliceCoefficient alpha beta q M₁ M₂ Q n‖ ≤ B) :
    typeIOverIICompositeSliceEnergy alpha beta q M₁ M₂ Q ≤
      typeIOverIICompositeSliceLength M₁ M₂ Q *
        (B / (M₁ ^ (2 : ℕ) * M₂ * Q)) ^ (2 : ℕ) := by
  classical
  have hdenom : 0 < M₁ ^ (2 : ℕ) * M₂ * Q := by positivity
  have hlength : 0 ≤ typeIOverIICompositeSliceLength M₁ M₂ Q := by
    unfold typeIOverIICompositeSliceLength
    positivity
  have hterm : ∀ n ∈ natOpenClosedInterval 0
      (typeIOverIICompositeSliceLength M₁ M₂ Q),
      ‖typeIOverIICompositeSliceLineZeroCoefficient
          alpha beta q M₁ M₂ Q n‖ ≤
        B / (M₁ ^ (2 : ℕ) * M₂ * Q) := by
    intro n hn
    by_cases hnSupport :
        n ∈ typeIOverIICompositeSliceSupport M₁ M₂ Q
    · have hbounds := typeIOverIICompositeSliceSupport_bounds
        hM₁ hM₂ hQ hnSupport
      have hnposReal : 0 < (n : ℝ) := hdenom.trans hbounds.1
      rw [typeIOverIICompositeSliceLineZeroCoefficient, norm_div]
      simp only [Complex.norm_natCast]
      apply (div_le_div_iff₀ hnposReal hdenom).2
      calc
        ‖typeIOverIICompositeSliceCoefficient alpha beta q M₁ M₂ Q n‖ *
              (M₁ ^ (2 : ℕ) * M₂ * Q) ≤
            B * (M₁ ^ (2 : ℕ) * M₂ * Q) :=
          mul_le_mul_of_nonneg_right (hcoeff n hnSupport) hdenom.le
        _ ≤ B * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hbounds.1.le hB
    · rw [typeIOverIICompositeSliceLineZeroCoefficient,
        typeIOverIICompositeSliceCoefficient,
        Sparse.binaryConvolutionCoefficient_eq_zero_of_not_mem_productSupport
          _ _ _ _ n hnSupport]
      simp
      positivity
  rw [typeIOverIICompositeSliceEnergy]
  calc
    (∑ n ∈ natOpenClosedInterval 0
        (typeIOverIICompositeSliceLength M₁ M₂ Q),
        ‖typeIOverIICompositeSliceLineZeroCoefficient
          alpha beta q M₁ M₂ Q n‖ ^ (2 : ℕ)) ≤
      ∑ _n ∈ natOpenClosedInterval 0
        (typeIOverIICompositeSliceLength M₁ M₂ Q),
        (B / (M₁ ^ (2 : ℕ) * M₂ * Q)) ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ (norm_nonneg _) (hterm n hn) 2
    _ = ((natOpenClosedInterval 0
          (typeIOverIICompositeSliceLength M₁ M₂ Q)).card : ℝ) *
        (B / (M₁ ^ (2 : ℕ) * M₂ * Q)) ^ (2 : ℕ) := by simp
    _ ≤ typeIOverIICompositeSliceLength M₁ M₂ Q *
        (B / (M₁ ^ (2 : ℕ) * M₂ * Q)) ^ (2 : ℕ) := by
      apply mul_le_mul_of_nonneg_right
        (TypeII.card_initialInterval_le hlength)
      positivity

theorem typeIOverIICompositeSliceLineZero_term_identity
    (alpha beta q : ℕ → ℂ) (M₁ M₂ Q : ℝ)
    {n : ℕ} (hn : 0 < n) (t : ℝ) :
    typeIOverIICompositeSliceLineZeroCoefficient
        alpha beta q M₁ M₂ Q n *
          (n : ℂ) ^ (-((t : ℂ) * Complex.I)) =
      typeIOverIICompositeSliceCoefficient alpha beta q M₁ M₂ Q n *
        (n : ℂ) ^ (-onePlusIT t) := by
  unfold typeIOverIICompositeSliceLineZeroCoefficient
  have hnzero : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hexponent :
      -onePlusIT t = (-1 : ℂ) + (-((t : ℂ) * Complex.I)) := by
    simp only [onePlusIT]
    ring
  rw [hexponent, Complex.cpow_add _ _ hnzero, Complex.cpow_neg_one]
  field_simp [hnzero]

/-- Exact zero-line normalization of a collected Type-I/II slice. -/
theorem typeIOverII_initialCompositeSlicePolynomial_eq
    (alpha beta q : ℕ → ℂ) {M₁ M₂ Q : ℝ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hQ : 0 < Q) (t : ℝ) :
    matomakiTeravainenInitialDirichletPolynomial
        (typeIOverIICompositeSliceLineZeroCoefficient
          alpha beta q M₁ M₂ Q)
        (typeIOverIICompositeSliceLength M₁ M₂ Q)
        ((t : ℂ) * Complex.I) =
      dyadicDirichletPolynomial alpha M₁ (onePlusIT t) ^ (2 : ℕ) *
        dyadicDirichletPolynomial beta M₂ (onePlusIT t) *
        dyadicDirichletPolynomial q Q (onePlusIT t) := by
  have hlengthNonneg : 0 ≤ typeIOverIICompositeSliceLength M₁ M₂ Q := by
    unfold typeIOverIICompositeSliceLength
    positivity
  calc
    matomakiTeravainenInitialDirichletPolynomial
          (typeIOverIICompositeSliceLineZeroCoefficient
            alpha beta q M₁ M₂ Q)
          (typeIOverIICompositeSliceLength M₁ M₂ Q)
          ((t : ℂ) * Complex.I) =
        matomakiTeravainenInitialDirichletPolynomial
          (typeIOverIICompositeSliceCoefficient alpha beta q M₁ M₂ Q)
          (typeIOverIICompositeSliceLength M₁ M₂ Q)
          (onePlusIT t) := by
      simp only [matomakiTeravainenInitialDirichletPolynomial,
        dirichletPolynomial]
      apply Finset.sum_congr rfl
      intro n hn
      have hnBounds := (mem_natOpenClosedInterval (by norm_num)
        hlengthNonneg).mp hn
      have hnpos : 0 < n := by exact_mod_cast hnBounds.1
      exact typeIOverIICompositeSliceLineZero_term_identity
        alpha beta q M₁ M₂ Q hnpos t
    _ = dirichletPolynomial
          (typeIOverIICompositeSliceCoefficient alpha beta q M₁ M₂ Q)
          (typeIOverIICompositeSliceSupport M₁ M₂ Q)
          (onePlusIT t) := by
      classical
      simp only [matomakiTeravainenInitialDirichletPolynomial,
        dirichletPolynomial]
      rw [← Finset.sum_subset
        (typeIOverIICompositeSliceSupport_subset_initial hM₁ hM₂ hQ)]
      intro n hnInitial hnSupport
      rw [typeIOverIICompositeSliceCoefficient,
        Sparse.binaryConvolutionCoefficient_eq_zero_of_not_mem_productSupport
          _ _ _ _ n hnSupport]
      simp
    _ = _ := typeIOverIICompositeSlice_polynomial_factorization
      alpha beta q M₁ M₂ Q (onePlusIT t)

/-- MT23, Lemma 3.2 applied uniformly to every collected Type-I/II slice.
The right side retains the literal zero-line coefficient energy; no
divisor-bound simplification is hidden. -/
theorem typeIOverII_compositeSliceMeanValue_le_of_matomakiTeravainen
    (hMV : MatomakiTeravainenLemmaThreeTwoStatement) :
    ∃ C_MV : ℝ, 0 < C_MV ∧
      ∀ (alpha beta q : ℕ → ℂ) (M₁ M₂ Q T : ℝ),
        1 ≤ M₁ → 1 ≤ M₂ → 1 ≤ Q → 1 ≤ T →
        (∫ t in Set.Icc T (2 * T),
          ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (4 : ℕ) *
            ‖dyadicDirichletPolynomial beta M₂ (onePlusIT t)‖ ^ (2 : ℕ) *
            ‖dyadicDirichletPolynomial q Q (onePlusIT t)‖ ^ (2 : ℕ)) ≤
          typeIOverIIMeanSquareMajorant C_MV
            (typeIOverIICompositeSliceLength M₁ M₂ Q) T
            (typeIOverIICompositeSliceLineZeroCoefficient
              alpha beta q M₁ M₂ Q) := by
  obtain ⟨C_MV, hC_MV, hsource⟩ := hMV
  refine ⟨C_MV, hC_MV, ?_⟩
  intro alpha beta q M₁ M₂ Q T hM₁ hM₂ hQ hT
  have hM₁pos : 0 < M₁ := zero_lt_one.trans_le hM₁
  have hM₂pos : 0 < M₂ := zero_lt_one.trans_le hM₂
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have hlength : 1 ≤ typeIOverIICompositeSliceLength M₁ M₂ Q := by
    unfold typeIOverIICompositeSliceLength
    have hfirst : (1 : ℝ) ≤ (2 * M₁) ^ (2 : ℕ) :=
      one_le_pow₀ (by linarith)
    have hsecond : (1 : ℝ) ≤ 2 * M₂ := by linarith
    have hthird : (1 : ℝ) ≤ 2 * Q := by linarith
    have hfirstTwo : (1 : ℝ) ≤ (2 * M₁) ^ (2 : ℕ) * (2 * M₂) := by
      nlinarith [mul_le_mul hfirst hsecond (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : 0 ≤ (2 * M₁) ^ (2 : ℕ))]
    nlinarith [mul_le_mul hfirstTwo hthird (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : 0 ≤ (2 * M₁) ^ (2 : ℕ) * (2 * M₂))]
  have h2T : 1 ≤ 2 * T := by linarith
  let coeff : ℕ → ℂ :=
    typeIOverIICompositeSliceLineZeroCoefficient alpha beta q M₁ M₂ Q
  let length : ℝ := typeIOverIICompositeSliceLength M₁ M₂ Q
  let energy : ℝ := typeIOverIICompositeSliceEnergy alpha beta q M₁ M₂ Q
  let whole : ℝ :=
    ∫ t in Set.Icc (-(2 * T)) (2 * T),
      ‖matomakiTeravainenInitialDirichletPolynomial coeff length
        ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)
  have hraw := hsource length (2 * T) coeff hlength h2T
  have hsourceUpper :
      whole ≤ (4 * T + C_MV * length) * energy := by
    have hupper := (abs_le.mp hraw).2
    dsimp only [whole, energy, length, coeff] at hupper ⊢
    rw [typeIOverIICompositeSliceEnergy]
    nlinarith
  let integrand : ℝ → ℝ := fun t ↦
    ‖dyadicDirichletPolynomial alpha M₁ (onePlusIT t)‖ ^ (4 : ℕ) *
      ‖dyadicDirichletPolynomial beta M₂ (onePlusIT t)‖ ^ (2 : ℕ) *
      ‖dyadicDirichletPolynomial q Q (onePlusIT t)‖ ^ (2 : ℕ)
  have hintegrandCont : Continuous integrand :=
    (((Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
      alpha M₁).norm.pow 4).mul
      ((Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
        beta M₂).norm.pow 2)).mul
      ((Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse
        q Q).norm.pow 2)
  have hsubset : Set.Icc T (2 * T) ⊆ Set.Icc (-(2 * T)) (2 * T) := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2⟩
  have hrestrict :
      (∫ t in Set.Icc T (2 * T), integrand t) ≤
        ∫ t in Set.Icc (-(2 * T)) (2 * T), integrand t := by
    apply setIntegral_mono_set hintegrandCont.integrableOn_Icc
    · exact Filter.Eventually.of_forall fun t ↦ by positivity
    · exact Filter.Eventually.of_forall hsubset
  have hwholeIdentity :
      (∫ t in Set.Icc (-(2 * T)) (2 * T), integrand t) = whole := by
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [whole, coeff, length]
    rw [typeIOverII_initialCompositeSlicePolynomial_eq
      alpha beta q hM₁pos hM₂pos hQpos t]
    dsimp [integrand]
    simp only [norm_mul, norm_pow]
    ring
  change (∫ t in Set.Icc T (2 * T), integrand t) ≤
    (4 * T + C_MV * length) * energy
  exact hrestrict.trans (hwholeIdentity.le.trans hsourceUpper)

def typeIOverIICompositeMeanValueModule : ProofModule :=
  { name := "Completion.TypeIOverIICompositeMeanValue"
    paperLocation := "MT23 Section 5.2; Lemma 3.2"
    purpose :=
      "Collect M₁(s)^2 M₂(s) times one inserted prime-power slice, normalize the product on the zero line, apply the cited ordinary mean-value theorem, and prove the explicit uniform coefficient-energy envelope."
    dependsOn :=
      [ "Completion.TypeIOverIIClosure",
        "Completion.TypeIPrimePowerEnergy",
        "TypeII.PoweredMeanValue",
        "Hybrid.HybridDensity",
        "Assumptions.matomakiTeravainenLemmaThreeTwo" ]
    status := .proved }

end

end Completion
end ExactSemiprimes
