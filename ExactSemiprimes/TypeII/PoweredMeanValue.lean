import ExactSemiprimes.TypeII.PoweredPolynomial
import ExactSemiprimes.Assumptions
import ExactSemiprimes.Hybrid.HybridDensity

/-!
# Discrete mean values for powered Type-II polynomials

This file supplies the exact finite-algebra bridge needed before applying
Iwaniec--Kowalski, Theorem 9.4, in the `R₁` part of
Matomäki--Teräväinen, Proposition 5.1.  A power of a dyadic Dirichlet
polynomial is collected by the product of its tuple indices, then moved from
the line `Re(s)=1` to the zero line by dividing the collected coefficient by
its index.  No analytic estimate is used until the final theorem.
-/

namespace ExactSemiprimes
namespace TypeII

open scoped BigOperators

noncomputable section

/-! ## Collecting a finite polynomial power by tuple product -/

/-- Complex powers of positive-natural casts are multiplicative over a
finite product.  In fact Mathlib's identity also handles zero factors, so no
positivity hypothesis is needed here. -/
theorem natCast_tupleProduct_cpow {ell : ℕ}
    (f : Fin ell → ℕ) (s : ℂ) :
    (tupleProduct f : ℂ) ^ s = ∏ i, (f i : ℂ) ^ s := by
  classical
  unfold tupleProduct
  induction (Finset.univ : Finset (Fin ell)) using Finset.induction_on with
  | empty => simp
  | @insert i u hi ih =>
      simp only [Finset.prod_insert hi, Nat.cast_mul,
        Complex.natCast_mul_natCast_cpow, ih]

/-- One tuple term factors into its convolution coefficient and the complex
power of its integer product. -/
theorem tupleDirichletTerm_eq {a : ℕ → ℂ} {ell : ℕ}
    (f : Fin ell → ℕ) (s : ℂ) :
    (∏ i, (a (f i) * (f i : ℂ) ^ (-s))) =
      tupleCoefficient a f * (tupleProduct f : ℂ) ^ (-s) := by
  rw [Finset.prod_mul_distrib, natCast_tupleProduct_cpow]
  rfl

/-- Regrouping by the product map turns the tuple expansion into the
convolution-coefficient Dirichlet polynomial on the finite image support. -/
theorem dirichletPolynomial_pow_eq_convolution_image
    (a : ℕ → ℂ) (S : Finset ℕ) (s : ℂ) (ell : ℕ) :
    dirichletPolynomial a S s ^ ell =
      dirichletPolynomial (powerConvolutionCoefficient a S ell)
        ((powerTuples S ell).image tupleProduct) s := by
  classical
  rw [dirichletPolynomial_pow_eq_tupleSum]
  simp only [dirichletPolynomial]
  calc
    (∑ f ∈ powerTuples S ell,
        ∏ i, (a (f i) * (f i : ℂ) ^ (-s))) =
        ∑ f ∈ powerTuples S ell,
          tupleCoefficient a f * (tupleProduct f : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro f hf
      exact tupleDirichletTerm_eq f s
    _ = ∑ n ∈ (powerTuples S ell).image tupleProduct,
          ∑ f ∈ powerTuples S ell with tupleProduct f = n,
            tupleCoefficient a f * (tupleProduct f : ℂ) ^ (-s) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (s := powerTuples S ell)
        (t := (powerTuples S ell).image tupleProduct)
        (g := tupleProduct)
        (fun f hf ↦ Finset.mem_image.mpr ⟨f, hf, rfl⟩)
        (fun f ↦ tupleCoefficient a f * (tupleProduct f : ℂ) ^ (-s))
    _ = ∑ n ∈ (powerTuples S ell).image tupleProduct,
          powerConvolutionCoefficient a S ell n * (n : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [powerConvolutionCoefficient, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro f hf
      have hproduct : tupleProduct f = n := (Finset.mem_filter.mp hf).2
      rw [hproduct]

/-- A convolution coefficient is zero away from the image of the product
map. -/
theorem powerConvolutionCoefficient_eq_zero_of_not_mem_image
    {a : ℕ → ℂ} {S : Finset ℕ} {ell n : ℕ}
    (hn : n ∉ (powerTuples S ell).image tupleProduct) :
    powerConvolutionCoefficient a S ell n = 0 := by
  classical
  rw [powerConvolutionCoefficient]
  apply Finset.sum_eq_zero
  intro f hf
  have hfTuple : f ∈ powerTuples S ell := (Finset.mem_filter.mp hf).1
  have hfProduct : tupleProduct f = n := (Finset.mem_filter.mp hf).2
  exact (hn (Finset.mem_image.mpr ⟨f, hfTuple, hfProduct⟩)).elim

/-! ## Moving the powered polynomial to the zero line -/

/-- The coefficient of the powered polynomial after changing from
`Re(s)=1` to `Re(s)=0`. -/
def poweredLineOneCoefficient (a : ℕ → ℂ) (S : Finset ℕ)
    (ell n : ℕ) : ℂ :=
  powerConvolutionCoefficient a S ell n / (n : ℂ)

/-- Termwise change from the line one to the zero line. -/
theorem poweredLineOne_term_identity
    {a : ℕ → ℂ} {S : Finset ℕ} {ell n : ℕ}
    (hn : 0 < n) (t : ℝ) :
    poweredLineOneCoefficient a S ell n *
        (n : ℂ) ^ (-((t : ℂ) * Complex.I)) =
      powerConvolutionCoefficient a S ell n *
        (n : ℂ) ^ (-onePlusIT t) := by
  unfold poweredLineOneCoefficient
  have hnzero : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hexponent :
      -onePlusIT t = (-1 : ℂ) + (-((t : ℂ) * Complex.I)) := by
    simp only [onePlusIT]
    ring
  rw [hexponent, Complex.cpow_add _ _ hnzero, Complex.cpow_neg_one]
  field_simp [hnzero]

/-- Every product appearing in the `ell`-fold power of a polynomial on
`(M,2M]` lies in the initial interval ending at `(2M)^ell`. -/
theorem poweredDyadicImage_subset_initial
    {M : ℝ} (hM : 0 < M) (ell : ℕ) :
    (powerTuples (dyadicInterval M) ell).image tupleProduct ⊆
      natOpenClosedInterval 0 ((2 * M) ^ ell) := by
  intro n hn
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hn
  have hsupport : ∀ m ∈ dyadicInterval M, InDyadicRange M m := by
    intro m hm
    exact (mem_dyadicInterval hM.le).mp hm
  have hb := tupleProduct_mem_poweredSupport hM.le hf hsupport
  rw [mem_natOpenClosedInterval (by norm_num)
    (pow_nonneg (by positivity) ell)]
  exact ⟨(pow_pos hM ell).trans_le hb.1, hb.2⟩

/-- Enlarging the finite product image to the enclosing initial interval
does not change the convolution polynomial, because every newly inserted
coefficient is zero. -/
theorem initialConvolutionPolynomial_eq_image
    (a : ℕ → ℂ) {M : ℝ} (hM : 0 < M) (ell : ℕ) (s : ℂ) :
    matomakiTeravainenInitialDirichletPolynomial
        (powerConvolutionCoefficient a (dyadicInterval M) ell)
        ((2 * M) ^ ell) s =
      dirichletPolynomial
        (powerConvolutionCoefficient a (dyadicInterval M) ell)
        ((powerTuples (dyadicInterval M) ell).image tupleProduct) s := by
  classical
  simp only [matomakiTeravainenInitialDirichletPolynomial,
    dirichletPolynomial]
  rw [← Finset.sum_subset (poweredDyadicImage_subset_initial hM ell)]
  intro n hnInitial hnImage
  rw [powerConvolutionCoefficient_eq_zero_of_not_mem_image hnImage]
  simp

/-- Exact normalization of the powered dyadic polynomial on `Re(s)=1` as
an initial Dirichlet polynomial on the zero line. -/
theorem initialPoweredLineOnePolynomial_eq
    (a : ℕ → ℂ) {M : ℝ} (hM : 0 < M) (ell : ℕ) (t : ℝ) :
    matomakiTeravainenInitialDirichletPolynomial
        (poweredLineOneCoefficient a (dyadicInterval M) ell)
        ((2 * M) ^ ell) ((t : ℂ) * Complex.I) =
      dyadicDirichletPolynomial a M (onePlusIT t) ^ ell := by
  classical
  calc
    matomakiTeravainenInitialDirichletPolynomial
          (poweredLineOneCoefficient a (dyadicInterval M) ell)
          ((2 * M) ^ ell) ((t : ℂ) * Complex.I) =
        matomakiTeravainenInitialDirichletPolynomial
          (powerConvolutionCoefficient a (dyadicInterval M) ell)
          ((2 * M) ^ ell) (onePlusIT t) := by
      simp only [matomakiTeravainenInitialDirichletPolynomial,
        dirichletPolynomial]
      apply Finset.sum_congr rfl
      intro n hn
      have hnBounds := (mem_natOpenClosedInterval (by norm_num)
        (pow_nonneg (by positivity) ell)).mp hn
      have hnpos : 0 < n := by exact_mod_cast hnBounds.1
      exact poweredLineOne_term_identity hnpos t
    _ = dirichletPolynomial
          (powerConvolutionCoefficient a (dyadicInterval M) ell)
          ((powerTuples (dyadicInterval M) ell).image tupleProduct)
          (onePlusIT t) :=
      initialConvolutionPolynomial_eq_image a hM ell (onePlusIT t)
    _ = dyadicDirichletPolynomial a M (onePlusIT t) ^ ell := by
      symm
      exact dirichletPolynomial_pow_eq_convolution_image
        a (dyadicInterval M) (onePlusIT t) ell

/-! ## Exact application of Iwaniec--Kowalski, Theorem 9.4 -/

/-- The coefficient energy that occurs when Theorem 9.4 is applied to the
`ell`-fold powered polynomial. -/
def poweredLineOneEnergy
    (a : ℕ → ℂ) (M : ℝ) (ell : ℕ) : ℝ :=
  ∑ n ∈ natOpenClosedInterval 0 ((2 * M) ^ ell),
    ‖poweredLineOneCoefficient a (dyadicInterval M) ell n‖ ^ (2 : ℕ)

/-- The initial integer interval `(0,N]` has at most `N` elements. -/
theorem card_initialInterval_le {N : ℝ} (hN : 0 ≤ N) :
    ((natOpenClosedInterval 0 N).card : ℝ) ≤ N := by
  have hcardNat : (natOpenClosedInterval 0 N).card ≤ ⌊N⌋₊ := by
    simp only [natOpenClosedInterval, Nat.card_Ioc]
    exact Nat.sub_le _ _
  have hcast : ((natOpenClosedInterval 0 N).card : ℝ) ≤ (⌊N⌋₊ : ℝ) := by
    exact_mod_cast hcardNat
  exact hcast.trans (Nat.floor_le hN)

/-- An explicit energy bound from a pointwise bound for the collected
convolution coefficients.  Products in the support are at least `M^ell`,
so division by the line-one index contributes `M^(-ell)`; the enclosing
initial interval has length at most `(2M)^ell`.

This is intentionally stated with the coefficient bound `B` exposed.  The
remaining analytic-number-theory step in Proposition 5.1 is to obtain a
polylogarithmic (or subpower) `B` from divisor-bounded input coefficients. -/
theorem poweredLineOneEnergy_le_of_convolution_bound
    {a : ℕ → ℂ} {M B : ℝ} {ell : ℕ}
    (hM : 0 < M) (hB : 0 ≤ B)
    (hcoeff : ∀ n ∈ (powerTuples (dyadicInterval M) ell).image tupleProduct,
      ‖powerConvolutionCoefficient a (dyadicInterval M) ell n‖ ≤ B) :
    poweredLineOneEnergy a M ell ≤
      (2 * M) ^ ell * (B / M ^ ell) ^ (2 : ℕ) := by
  classical
  have hMpow : 0 < M ^ ell := pow_pos hM ell
  have hterm : ∀ n ∈ natOpenClosedInterval 0 ((2 * M) ^ ell),
      ‖poweredLineOneCoefficient a (dyadicInterval M) ell n‖ ≤
        B / M ^ ell := by
    intro n hn
    by_cases hnImage :
        n ∈ (powerTuples (dyadicInterval M) ell).image tupleProduct
    · obtain ⟨f, hf, hfn⟩ := Finset.mem_image.mp hnImage
      have hsupport : ∀ m ∈ dyadicInterval M, InDyadicRange M m := by
        intro m hm
        exact (mem_dyadicInterval hM.le).mp hm
      have hlower :=
        (tupleProduct_mem_poweredSupport hM.le hf hsupport).1
      have hnLower : M ^ ell ≤ (n : ℝ) := by simpa [hfn] using hlower
      have hnpos : 0 < (n : ℝ) := hMpow.trans_le hnLower
      rw [poweredLineOneCoefficient, norm_div]
      simp only [Complex.norm_natCast]
      apply (div_le_div_iff₀ hnpos hMpow).2
      calc
        ‖powerConvolutionCoefficient a (dyadicInterval M) ell n‖ *
              M ^ ell ≤ B * M ^ ell :=
          mul_le_mul_of_nonneg_right (hcoeff n hnImage) hMpow.le
        _ ≤ B * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hnLower hB
    · rw [poweredLineOneCoefficient,
        powerConvolutionCoefficient_eq_zero_of_not_mem_image hnImage]
      simp
      positivity
  rw [poweredLineOneEnergy]
  calc
    (∑ n ∈ natOpenClosedInterval 0 ((2 * M) ^ ell),
        ‖poweredLineOneCoefficient a (dyadicInterval M) ell n‖ ^
          (2 : ℕ)) ≤
        ∑ _n ∈ natOpenClosedInterval 0 ((2 * M) ^ ell),
          (B / M ^ ell) ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ (norm_nonneg _) (hterm n hn) 2
    _ = ((natOpenClosedInterval 0 ((2 * M) ^ ell)).card : ℝ) *
          (B / M ^ ell) ^ (2 : ℕ) := by simp
    _ ≤ (2 * M) ^ ell * (B / M ^ ell) ^ (2 : ℕ) := by
      apply mul_le_mul_of_nonneg_right
        (card_initialInterval_le (pow_nonneg (by positivity) ell))
      positivity

/-- Divisor-bounded input coefficients give a uniform subpower bound for
the collected coefficients on their finite product support.  This combines
the exact convolution-divisor estimate from `PoweredPolynomial` with the
fully proved global estimate `d(n)^E \ll_{E,rho} n^rho`.

The quantifier order records that `D` is independent of the coefficient
sequence, its displayed constant `A₀`, the dyadic scale `M`, and `n`; it
depends only on `B₀`, `ell`, and `rho`. -/
theorem exists_uniform_powerConvolution_bound_subpower
    {B₀ rho : ℝ} {ell : ℕ}
    (hB₀ : 0 ≤ B₀) (hell : 1 ≤ ell) (hrho : 0 < rho) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ (a : ℕ → ℂ) (M A₀ : ℝ),
        0 < M → IsDivisorBoundedByConstant B₀ A₀ a →
        ∀ n ∈ (powerTuples (dyadicInterval M) ell).image tupleProduct,
          ‖powerConvolutionCoefficient a (dyadicInterval M) ell n‖ ≤
            A₀ ^ ell * D * ((2 * M) ^ ell) ^ rho := by
  let E : ℝ := B₀ * (ell : ℝ) + (ell : ℝ) - 1
  have hE : 0 ≤ E := by
    dsimp [E]
    have hBterm : 0 ≤ B₀ * (ell : ℝ) :=
      mul_nonneg hB₀ (Nat.cast_nonneg ell)
    have hellReal : 1 ≤ (ell : ℝ) := by exact_mod_cast hell
    linarith
  obtain ⟨D, hD, hdivisor⟩ :=
    Hybrid.globalDivisorSubpower E rho hE hrho
  refine ⟨D, hD, ?_⟩
  intro a M A₀ hM ha n hn
  obtain ⟨f, hf, hproduct⟩ := Finset.mem_image.mp hn
  have hsupport : ∀ m ∈ dyadicInterval M, InDyadicRange M m := by
    intro m hm
    exact (mem_dyadicInterval hM.le).mp hm
  have hbounds := tupleProduct_mem_poweredSupport hM.le hf hsupport
  have hnposReal : 0 < (n : ℝ) := by
    rw [← hproduct]
    exact (pow_pos hM ell).trans_le hbounds.1
  have hnpos : 0 < n := by exact_mod_cast hnposReal
  have hnUpper : (n : ℝ) ≤ (2 * M) ^ ell := by
    simpa [hproduct] using hbounds.2
  have hcoeff :=
    norm_powerConvolutionCoefficient_le_divisorCount
      (S := dyadicInterval M) hell hnpos ha
  have hdivisorAt := hdivisor n hnpos
  have hnRpow : (n : ℝ) ^ rho ≤ ((2 * M) ^ ell) ^ rho :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) hnUpper hrho.le
  have hA : 0 ≤ A₀ ^ ell := pow_nonneg ha.2.1.le ell
  calc
    ‖powerConvolutionCoefficient a (dyadicInterval M) ell n‖ ≤
        A₀ ^ ell * (divisorCount n : ℝ) ^
          (B₀ * (ell : ℝ) + (ell : ℝ) - 1) := hcoeff
    _ = A₀ ^ ell * (divisorCount n : ℝ) ^ E := by rfl
    _ ≤ A₀ ^ ell * (D * (n : ℝ) ^ rho) :=
      mul_le_mul_of_nonneg_left hdivisorAt hA
    _ ≤ A₀ ^ ell * (D * ((2 * M) ^ ell) ^ rho) := by
      gcongr
    _ = A₀ ^ ell * D * ((2 * M) ^ ell) ^ rho := by ring

/-- Divisor-bounded coefficients have a subpower convolution bound with one
constant uniform over all positive convolution orders `ell ≤ K`.  In
particular, `D` is chosen before `ell`, the coefficient sequence, its
displayed constant, and the dyadic scale. -/
theorem exists_uniform_boundedOrder_powerConvolution_bound_subpower
    {B₀ rho : ℝ} {K : ℕ}
    (hB₀ : 0 ≤ B₀) (hK : 1 ≤ K) (hrho : 0 < rho) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ (ell : ℕ), 1 ≤ ell → ell ≤ K →
        ∀ (a : ℕ → ℂ) (M A₀ : ℝ),
          0 < M → IsDivisorBoundedByConstant B₀ A₀ a →
          ∀ n ∈ (powerTuples (dyadicInterval M) ell).image tupleProduct,
            ‖powerConvolutionCoefficient a (dyadicInterval M) ell n‖ ≤
              A₀ ^ ell * D * ((2 * M) ^ ell) ^ rho := by
  let E : ℝ := B₀ * (K : ℝ) + (K : ℝ) - 1
  have hKReal : (1 : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hK
  have hE : 0 ≤ E := by
    dsimp [E]
    have hBterm : 0 ≤ B₀ * (K : ℝ) :=
      mul_nonneg hB₀ (Nat.cast_nonneg K)
    linarith
  obtain ⟨D, hD, hdivisor⟩ :=
    Hybrid.globalDivisorSubpower E rho hE hrho
  refine ⟨D, hD, ?_⟩
  intro ell hell hellK a M A₀ hM ha n hn
  obtain ⟨f, hf, hproduct⟩ := Finset.mem_image.mp hn
  have hsupport : ∀ m ∈ dyadicInterval M, InDyadicRange M m := by
    intro m hm
    exact (mem_dyadicInterval hM.le).mp hm
  have hbounds := tupleProduct_mem_poweredSupport hM.le hf hsupport
  have hnposReal : 0 < (n : ℝ) := by
    rw [← hproduct]
    exact (pow_pos hM ell).trans_le hbounds.1
  have hnpos : 0 < n := by
    exact_mod_cast hnposReal
  have hnUpper : (n : ℝ) ≤ (2 * M) ^ ell := by
    simpa [hproduct] using hbounds.2
  have hellKReal : (ell : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hellK
  have hBmul : B₀ * (ell : ℝ) ≤ B₀ * (K : ℝ) :=
    mul_le_mul_of_nonneg_left hellKReal hB₀
  have hExponent :
      B₀ * (ell : ℝ) + (ell : ℝ) - 1 ≤ E := by
    dsimp [E]
    linarith
  have hdivisorOneNat : 1 ≤ divisorCount n := by
    unfold divisorCount
    exact Finset.one_le_card.mpr
      ⟨1, Nat.one_mem_divisors.mpr hnpos.ne'⟩
  have hdivisorOne : (1 : ℝ) ≤ (divisorCount n : ℝ) := by
    exact_mod_cast hdivisorOneNat
  have hraiseExponent :
      (divisorCount n : ℝ) ^
          (B₀ * (ell : ℝ) + (ell : ℝ) - 1) ≤
        (divisorCount n : ℝ) ^ E :=
    Real.rpow_le_rpow_of_exponent_le hdivisorOne hExponent
  have hcoeff :=
    norm_powerConvolutionCoefficient_le_divisorCount
      (S := dyadicInterval M) hell hnpos ha
  have hdivisorAt := hdivisor n hnpos
  have hnRpow : (n : ℝ) ^ rho ≤ ((2 * M) ^ ell) ^ rho :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) hnUpper hrho.le
  have hA : 0 ≤ A₀ ^ ell := pow_nonneg ha.2.1.le ell
  calc
    ‖powerConvolutionCoefficient a (dyadicInterval M) ell n‖ ≤
        A₀ ^ ell * (divisorCount n : ℝ) ^
          (B₀ * (ell : ℝ) + (ell : ℝ) - 1) := hcoeff
    _ ≤ A₀ ^ ell * (divisorCount n : ℝ) ^ E :=
      mul_le_mul_of_nonneg_left hraiseExponent hA
    _ ≤ A₀ ^ ell * (D * (n : ℝ) ^ rho) :=
      mul_le_mul_of_nonneg_left hdivisorAt hA
    _ ≤ A₀ ^ ell * (D * ((2 * M) ^ ell) ^ rho) := by
      gcongr
    _ = A₀ ^ ell * D * ((2 * M) ^ ell) ^ rho := by
      ring

/-- Scale-local corollary of the preceding uniform bound.  This form is
convenient when a single dyadic polynomial is already fixed. -/
theorem exists_powerConvolution_bound_subpower
    {a : ℕ → ℂ} {M B₀ A₀ rho : ℝ} {ell : ℕ}
    (hM : 0 < M) (hell : 1 ≤ ell) (hrho : 0 < rho)
    (ha : IsDivisorBoundedByConstant B₀ A₀ a) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ n ∈ (powerTuples (dyadicInterval M) ell).image tupleProduct,
        ‖powerConvolutionCoefficient a (dyadicInterval M) ell n‖ ≤
          A₀ ^ ell * D * ((2 * M) ^ ell) ^ rho := by
  obtain ⟨D, hD, huniform⟩ :=
    exists_uniform_powerConvolution_bound_subpower ha.1 hell hrho
  exact ⟨D, hD, huniform a M A₀ hM ha⟩

/-- Source-faithful local specialization of IK04, Theorem 9.4, to the
powered dyadic polynomial used in the `R₁` argument.  The remaining
number-theoretic task is now isolated exactly as a bound for
`poweredLineOneEnergy`; no change of line or support is left implicit. -/
theorem poweredDyadic_discreteMeanValue
    (hIK : IwaniecKowalskiTheoremNineFourStatement) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → ℂ) (M T : ℝ) (ell : ℕ) (R : Finset ℝ),
        1 ≤ M → 1 ≤ T →
        (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
        IsOneSpaced (↑R : Set ℝ) →
        (∑ t ∈ R,
            ‖dyadicDirichletPolynomial a M (onePlusIT t) ^ ell‖ ^
              (2 : ℕ)) ≤
          C * (T + (2 * M) ^ ell) *
            Real.log (2 * (2 * M) ^ ell) *
            poweredLineOneEnergy a M ell := by
  obtain ⟨C, hC, hmean⟩ := hIK
  refine ⟨C, hC, ?_⟩
  intro a M T ell R hM hT hR hspaced
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hLength : 1 ≤ (2 * M) ^ ell := by
    exact one_le_pow₀ (by linarith)
  have happly := hmean ((2 * M) ^ ell) T
    (poweredLineOneCoefficient a (dyadicInterval M) ell) R
    hLength hT hR hspaced
  simpa only [initialPoweredLineOnePolynomial_eq a hMpos ell,
    poweredLineOneEnergy] using happly

/-- The exact large-value counting consequence used before the paper
estimates the powered coefficient energy.  At every selected height the
original polynomial is at least `M^(-10*eps)`; raising to `ell`, squaring,
and applying the preceding mean-value theorem gives this explicit quotient.
No asymptotic simplification is hidden in the statement. -/
theorem card_largePoweredDyadic_le
    (hIK : IwaniecKowalskiTheoremNineFourStatement) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → ℂ) (M T eps : ℝ) (ell : ℕ) (R : Finset ℝ),
        1 ≤ M → 1 ≤ T →
        (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
        IsOneSpaced (↑R : Set ℝ) →
        (∀ t ∈ R,
          M ^ (-10 * eps) ≤
            ‖dyadicDirichletPolynomial a M (onePlusIT t)‖) →
        (R.card : ℝ) ≤
          (C * (T + (2 * M) ^ ell) *
              Real.log (2 * (2 * M) ^ ell) *
              poweredLineOneEnergy a M ell) /
            ((M ^ (-10 * eps)) ^ ell) ^ (2 : ℕ) := by
  obtain ⟨C, hC, hmean⟩ := poweredDyadic_discreteMeanValue hIK
  refine ⟨C, hC, ?_⟩
  intro a M T eps ell R hM hT hR hspaced hlarge
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hthreshold : 0 < M ^ (-10 * eps) :=
    Real.rpow_pos_of_pos hMpos _
  have hpoweredLarge : ∀ t ∈ R,
      (M ^ (-10 * eps)) ^ ell ≤
        ‖dyadicDirichletPolynomial a M (onePlusIT t) ^ ell‖ := by
    intro t ht
    rw [norm_pow]
    exact pow_le_pow_left₀ hthreshold.le (hlarge t ht) ell
  have hcount :
      (R.card : ℝ) * ((M ^ (-10 * eps)) ^ ell) ^ (2 : ℕ) ≤
        C * (T + (2 * M) ^ ell) *
          Real.log (2 * (2 * M) ^ ell) *
          poweredLineOneEnergy a M ell := by
    calc
      (R.card : ℝ) * ((M ^ (-10 * eps)) ^ ell) ^ (2 : ℕ) =
          ∑ _t ∈ R, ((M ^ (-10 * eps)) ^ ell) ^ (2 : ℕ) := by
        simp
      _ ≤ ∑ t ∈ R,
          ‖dyadicDirichletPolynomial a M (onePlusIT t) ^ ell‖ ^
            (2 : ℕ) := by
        apply Finset.sum_le_sum
        intro t ht
        exact pow_le_pow_left₀ (pow_nonneg hthreshold.le ell)
          (hpoweredLarge t ht) 2
      _ ≤ C * (T + (2 * M) ^ ell) *
          Real.log (2 * (2 * M) ^ ell) *
          poweredLineOneEnergy a M ell :=
        hmean a M T ell R hM hT hR hspaced
  exact (le_div_iff₀ (pow_pos (pow_pos hthreshold ell) 2)).2 hcount

/-- Combination of the exact large-value quotient with the elementary
powered-energy estimate.  After this theorem, the only `R₁` coefficient
input still visible is a pointwise bound `B` for the finite convolution. -/
theorem card_largePoweredDyadic_le_of_convolution_bound
    (hIK : IwaniecKowalskiTheoremNineFourStatement) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → ℂ) (M T eps B : ℝ) (ell : ℕ) (R : Finset ℝ),
        1 ≤ M → 1 ≤ T → 0 ≤ B →
        (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
        IsOneSpaced (↑R : Set ℝ) →
        (∀ t ∈ R,
          M ^ (-10 * eps) ≤
            ‖dyadicDirichletPolynomial a M (onePlusIT t)‖) →
        (∀ n ∈ (powerTuples (dyadicInterval M) ell).image tupleProduct,
          ‖powerConvolutionCoefficient a (dyadicInterval M) ell n‖ ≤ B) →
        (R.card : ℝ) ≤
          (C * (T + (2 * M) ^ ell) *
              Real.log (2 * (2 * M) ^ ell) *
              ((2 * M) ^ ell * (B / M ^ ell) ^ (2 : ℕ))) /
            ((M ^ (-10 * eps)) ^ ell) ^ (2 : ℕ) := by
  obtain ⟨C, hC, hcard⟩ := card_largePoweredDyadic_le hIK
  refine ⟨C, hC, ?_⟩
  intro a M T eps B ell R hM hT hB hR hspaced hlarge hcoeff
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hraw := hcard a M T eps ell R hM hT hR hspaced hlarge
  have henergy :=
    poweredLineOneEnergy_le_of_convolution_bound hMpos hB hcoeff
  have hlength : 1 ≤ (2 * M) ^ ell := one_le_pow₀ (by linarith)
  have hlog : 0 ≤ Real.log (2 * (2 * M) ^ ell) := by
    apply Real.log_nonneg
    nlinarith
  have hprefactor :
      0 ≤ C * (T + (2 * M) ^ ell) *
        Real.log (2 * (2 * M) ^ ell) := by positivity
  refine hraw.trans ?_
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left henergy hprefactor

/-- Uniform `R₁` consequence for divisor-bounded coefficients.  After
`B₀`, `rho`, and `ell` have been fixed, the divisor-subpower constant `D`
is chosen before the coefficient sequence, its displayed constant, and all
dyadic and height parameters.  This is the quantifier order needed for a
later uniform big-`O` assembly. -/
theorem card_largePoweredDyadic_le_of_divisorBounded_uniform
    (hIK : IwaniecKowalskiTheoremNineFourStatement) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B₀ rho : ℝ) (ell : ℕ),
        0 ≤ B₀ → 1 ≤ ell → 0 < rho →
        ∃ D : ℝ, 1 ≤ D ∧
          ∀ (a : ℕ → ℂ) (M T eps A₀ : ℝ) (R : Finset ℝ),
            1 ≤ M → 1 ≤ T →
            IsDivisorBoundedByConstant B₀ A₀ a →
            (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
            IsOneSpaced (↑R : Set ℝ) →
            (∀ t ∈ R,
              M ^ (-10 * eps) ≤
                ‖dyadicDirichletPolynomial a M (onePlusIT t)‖) →
          (R.card : ℝ) ≤
            (C * (T + (2 * M) ^ ell) *
                Real.log (2 * (2 * M) ^ ell) *
                ((2 * M) ^ ell *
                  ((A₀ ^ ell * D * ((2 * M) ^ ell) ^ rho) /
                    M ^ ell) ^ (2 : ℕ))) /
              ((M ^ (-10 * eps)) ^ ell) ^ (2 : ℕ) := by
  obtain ⟨C, hC, hcard⟩ :=
    card_largePoweredDyadic_le_of_convolution_bound hIK
  refine ⟨C, hC, ?_⟩
  intro B₀ rho ell hB₀ hell hrho
  obtain ⟨D, hD, hcoeff⟩ :=
    exists_uniform_powerConvolution_bound_subpower hB₀ hell hrho
  refine ⟨D, hD, ?_⟩
  intro a M T eps A₀ R hM hT ha hR hspaced hlarge
  have hBconv :
      0 ≤ A₀ ^ ell * D * ((2 * M) ^ ell) ^ rho := by
    exact mul_nonneg
      (mul_nonneg (pow_nonneg ha.2.1.le ell) (zero_le_one.trans hD))
      (Real.rpow_nonneg (pow_nonneg (by linarith) ell) rho)
  exact hcard a M T eps
    (A₀ ^ ell * D * ((2 * M) ^ ell) ^ rho) ell R
    hM hT hBconv hR hspaced hlarge
    (hcoeff a M A₀ (zero_lt_one.trans_le hM) ha)

/-- Scale-local corollary of the uniform divisor-bounded `R₁` estimate.
The uniform version above should be used whenever the eventual constant
must remain independent of `M` or `T`. -/
theorem card_largePoweredDyadic_le_of_divisorBounded
    (hIK : IwaniecKowalskiTheoremNineFourStatement) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → ℂ) (M T eps B₀ A₀ rho : ℝ)
          (ell : ℕ) (R : Finset ℝ),
        1 ≤ M → 1 ≤ T → 1 ≤ ell → 0 < rho →
        IsDivisorBoundedByConstant B₀ A₀ a →
        (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
        IsOneSpaced (↑R : Set ℝ) →
        (∀ t ∈ R,
          M ^ (-10 * eps) ≤
            ‖dyadicDirichletPolynomial a M (onePlusIT t)‖) →
        ∃ D : ℝ, 1 ≤ D ∧
          (R.card : ℝ) ≤
            (C * (T + (2 * M) ^ ell) *
                Real.log (2 * (2 * M) ^ ell) *
                ((2 * M) ^ ell *
                  ((A₀ ^ ell * D * ((2 * M) ^ ell) ^ rho) /
                    M ^ ell) ^ (2 : ℕ))) /
              ((M ^ (-10 * eps)) ^ ell) ^ (2 : ℕ) := by
  obtain ⟨C, hC, huniform⟩ :=
    card_largePoweredDyadic_le_of_divisorBounded_uniform hIK
  refine ⟨C, hC, ?_⟩
  intro a M T eps B₀ A₀ rho ell R hM hT hell hrho ha hR hspaced hlarge
  obtain ⟨D, hD, hcard⟩ := huniform B₀ rho ell ha.1 hell hrho
  exact ⟨D, hD, hcard a M T eps A₀ R hM hT ha hR hspaced hlarge⟩

/-- This module closes the algebraic normalization and the exact application
of the cited discrete mean-value theorem. -/
def poweredMeanValueModule : ProofModule :=
  { name := "TypeII.PoweredMeanValue"
    paperLocation :=
      "Proof of Proposition 5.1, R₁; application of IK04, Theorem 9.4"
    purpose :=
      "Collect powers by product, normalize from Re(s)=1 to the zero line, apply the exact discrete mean-value input, and derive divisor-bounded convolution estimates uniform both at fixed power and over every positive power in a prescribed bounded range."
    dependsOn :=
      ["TypeII.PoweredPolynomial", "Assumptions.iwaniecKowalskiTheoremNineFour"]
    status := .proved }

end

end TypeII
end ExactSemiprimes
