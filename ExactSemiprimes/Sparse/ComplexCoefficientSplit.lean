import ExactSemiprimes.Sparse.FirstBranch

/-! # Complex-to-real coefficient splitting

A complex dyadic Dirichlet polynomial is covered by its real- and
imaginary-coefficient large parts, allowing the real-coefficient form of the
cited sparse mean-value theorem to be applied without a new analytic input. -/

namespace ExactSemiprimes
namespace Sparse

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

theorem dyadicDirichletPolynomial_eq_re_add_I_mul_im
    (beta : ℕ → ℂ) (N : ℝ) (s : ℂ) :
    dyadicDirichletPolynomial beta N s =
      dyadicDirichletPolynomial (fun n ↦ ((beta n).re : ℂ)) N s +
        Complex.I *
          dyadicDirichletPolynomial (fun n ↦ ((beta n).im : ℂ)) N s := by
  unfold dyadicDirichletPolynomial dirichletPolynomial
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Complex.re_add_im (beta n)]
  ring

/-- A fixed divisor bound for complex coefficients passes to their real
parts with the same witnesses. -/
theorem isDivisorBoundedByConstant_realPart
    {beta : ℕ → ℂ} {B A : ℝ}
    (hbeta : IsDivisorBoundedByConstant B A beta) :
    IsDivisorBoundedByConstant B A
      (fun n ↦ ((beta n).re : ℂ)) := by
  refine ⟨hbeta.1, hbeta.2.1, ?_⟩
  intro n hn
  calc
    ‖((beta n).re : ℂ)‖ = |(beta n).re| := by simp
    _ ≤ ‖beta n‖ := Complex.abs_re_le_norm _
    _ ≤ A * (divisorCount n : ℝ) ^ B := hbeta.2.2 n hn

/-- A fixed divisor bound for complex coefficients also passes to their
imaginary parts with the same witnesses. -/
theorem isDivisorBoundedByConstant_imaginaryPart
    {beta : ℕ → ℂ} {B A : ℝ}
    (hbeta : IsDivisorBoundedByConstant B A beta) :
    IsDivisorBoundedByConstant B A
      (fun n ↦ ((beta n).im : ℂ)) := by
  refine ⟨hbeta.1, hbeta.2.1, ?_⟩
  intro n hn
  calc
    ‖((beta n).im : ℂ)‖ = |(beta n).im| := by simp
    _ ≤ ‖beta n‖ := Complex.abs_im_le_norm _
    _ ≤ A * (divisorCount n : ℝ) ^ B := hbeta.2.2 n hn

theorem norm_sq_le_two_mul_re_im_norm_sq
    (zre zim : ℂ) :
    ‖zre + Complex.I * zim‖ ^ (2 : ℕ) ≤
      2 * (‖zre‖ ^ (2 : ℕ) + ‖zim‖ ^ (2 : ℕ)) := by
  calc
    ‖zre + Complex.I * zim‖ ^ (2 : ℕ) ≤
        (‖zre‖ + ‖Complex.I * zim‖) ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_add_le zre (Complex.I * zim)) 2
    _ = (‖zre‖ + ‖zim‖) ^ (2 : ℕ) := by simp
    _ ≤ 2 * (‖zre‖ ^ (2 : ℕ) + ‖zim‖ ^ (2 : ℕ)) := by
      nlinarith [sq_nonneg (‖zre‖ - ‖zim‖)]

/-- At least one of the real- or imaginary-coefficient polynomials retains
half of the magnitude of the original complex-coefficient polynomial. -/
theorem half_norm_dyadicDirichletPolynomial_le_re_or_im
    (beta : ℕ → ℂ) (N : ℝ) (s : ℂ) :
    ‖dyadicDirichletPolynomial beta N s‖ / 2 ≤
        ‖dyadicDirichletPolynomial (fun n ↦ ((beta n).re : ℂ)) N s‖ ∨
      ‖dyadicDirichletPolynomial beta N s‖ / 2 ≤
        ‖dyadicDirichletPolynomial (fun n ↦ ((beta n).im : ℂ)) N s‖ := by
  let Are := dyadicDirichletPolynomial
    (fun n ↦ ((beta n).re : ℂ)) N s
  let Aim := dyadicDirichletPolynomial
    (fun n ↦ ((beta n).im : ℂ)) N s
  have hid : dyadicDirichletPolynomial beta N s =
      Are + Complex.I * Aim :=
    dyadicDirichletPolynomial_eq_re_add_I_mul_im beta N s
  have htriangle : ‖dyadicDirichletPolynomial beta N s‖ ≤
      ‖Are‖ + ‖Aim‖ := by
    rw [hid]
    calc
      ‖Are + Complex.I * Aim‖ ≤ ‖Are‖ + ‖Complex.I * Aim‖ :=
        norm_add_le _ _
      _ = ‖Are‖ + ‖Aim‖ := by simp
  by_cases hre : ‖dyadicDirichletPolynomial beta N s‖ / 2 ≤ ‖Are‖
  · exact Or.inl hre
  · right
    by_contra him
    have hre' : ‖Are‖ < ‖dyadicDirichletPolynomial beta N s‖ / 2 :=
      lt_of_not_ge hre
    have him' : ‖Aim‖ < ‖dyadicDirichletPolynomial beta N s‖ / 2 :=
      lt_of_not_ge him
    linarith

/-- Lower-bound form used when a magnitude bin supplies `v ≤ |F|`. -/
theorem half_lowerBound_le_re_or_im_of_le_complex
    {beta : ℕ → ℂ} {N v : ℝ} {s : ℂ}
    (hv : v ≤ ‖dyadicDirichletPolynomial beta N s‖) :
    v / 2 ≤
        ‖dyadicDirichletPolynomial (fun n ↦ ((beta n).re : ℂ)) N s‖ ∨
      v / 2 ≤
        ‖dyadicDirichletPolynomial (fun n ↦ ((beta n).im : ℂ)) N s‖ := by
  rcases half_norm_dyadicDirichletPolynomial_le_re_or_im beta N s with h | h
  · exact Or.inl ((div_le_div_of_nonneg_right hv (by norm_num)).trans h)
  · exact Or.inr ((div_le_div_of_nonneg_right hv (by norm_num)).trans h)

/-- The part of `E` where the real-coefficient polynomial carries at least
half of the prescribed lower threshold. -/
def realCoefficientLargePart (E : Set ℝ) (beta : ℕ → ℂ)
    (N v : ℝ) : Set ℝ :=
  E ∩ {t | v / 2 ≤
    ‖dyadicDirichletPolynomial (fun n ↦ ((beta n).re : ℂ)) N
      (onePlusIT t)‖}

/-- The analogous imaginary-coefficient part.  The two parts may overlap,
which is harmless for the ensuing upper bound. -/
def imaginaryCoefficientLargePart (E : Set ℝ) (beta : ℕ → ℂ)
    (N v : ℝ) : Set ℝ :=
  E ∩ {t | v / 2 ≤
    ‖dyadicDirichletPolynomial (fun n ↦ ((beta n).im : ℂ)) N
      (onePlusIT t)‖}

@[simp]
theorem mem_realCoefficientLargePart {E : Set ℝ} {beta : ℕ → ℂ}
    {N v t : ℝ} :
    t ∈ realCoefficientLargePart E beta N v ↔
      t ∈ E ∧ v / 2 ≤
        ‖dyadicDirichletPolynomial (fun n ↦ ((beta n).re : ℂ)) N
          (onePlusIT t)‖ := by
  rfl

@[simp]
theorem mem_imaginaryCoefficientLargePart {E : Set ℝ} {beta : ℕ → ℂ}
    {N v t : ℝ} :
    t ∈ imaginaryCoefficientLargePart E beta N v ↔
      t ∈ E ∧ v / 2 ≤
        ‖dyadicDirichletPolynomial (fun n ↦ ((beta n).im : ℂ)) N
          (onePlusIT t)‖ := by
  rfl

/-- A lower bound for the complex polynomial covers `E` by its two
real-coefficient large parts. -/
theorem real_union_imaginaryCoefficientLargePart_eq
    {E : Set ℝ} {beta : ℕ → ℂ} {N v : ℝ}
    (hlower : ∀ t ∈ E,
      v ≤ ‖dyadicDirichletPolynomial beta N (onePlusIT t)‖) :
    realCoefficientLargePart E beta N v ∪
        imaginaryCoefficientLargePart E beta N v = E := by
  apply Set.Subset.antisymm
  · intro t ht
    rcases ht with ht | ht
    · exact ht.1
    · exact ht.1
  · intro t ht
    rcases half_lowerBound_le_re_or_im_of_le_complex (hlower t ht) with h | h
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr ⟨ht, h⟩

private theorem continuous_onePlusIT_complexSplit : Continuous onePlusIT := by
  unfold onePlusIT
  fun_prop

private theorem continuous_natCpow_neg_onePlusIT_complexSplit (n : ℕ) :
    Continuous (fun t : ℝ ↦ (n : ℂ) ^ (-onePlusIT t)) := by
  have hexp : Continuous (fun t : ℝ ↦ -onePlusIT t) :=
    continuous_onePlusIT_complexSplit.neg
  apply hexp.const_cpow
  right
  intro t ht
  have hre := congrArg Complex.re ht
  simp [onePlusIT] at hre

theorem continuous_dyadicDirichletPolynomial_onePlusIT_sparse
    (a : ℕ → ℂ) (N : ℝ) :
    Continuous (fun t : ℝ ↦
      dyadicDirichletPolynomial a N (onePlusIT t)) := by
  unfold dyadicDirichletPolynomial dirichletPolynomial
  apply continuous_finsetSum
  intro n hn
  exact continuous_const.mul
    (continuous_natCpow_neg_onePlusIT_complexSplit n)

theorem continuous_primePowerPolynomial_onePlusIT_sparse
    (S : Finset ℕ) (k : ℕ) :
    Continuous (fun t : ℝ ↦ primePowerPolynomial S k (onePlusIT t)) := by
  rw [show (fun t : ℝ ↦ primePowerPolynomial S k (onePlusIT t)) =
      fun t : ℝ ↦ dirichletPolynomial
        (fun n ↦ (primePowerCoefficient S k n : ℂ))
        (primePowerSupport S k) (onePlusIT t) by
    funext t
    simpa only [dirichletPolynomial] using
      (primePowerPolynomial_eq_supportSum S k (onePlusIT t))]
  unfold dirichletPolynomial
  apply continuous_finsetSum
  intro n hn
  exact continuous_const.mul
    (continuous_natCpow_neg_onePlusIT_complexSplit n)

theorem measurableSet_realCoefficientLargePart
    {E : Set ℝ} {beta : ℕ → ℂ} {N v : ℝ}
    (hE : MeasurableSet E) :
    MeasurableSet (realCoefficientLargePart E beta N v) := by
  apply hE.inter
  exact measurableSet_le measurable_const
    ((continuous_dyadicDirichletPolynomial_onePlusIT_sparse
      (fun n ↦ ((beta n).re : ℂ)) N).norm.measurable)

theorem measurableSet_imaginaryCoefficientLargePart
    {E : Set ℝ} {beta : ℕ → ℂ} {N v : ℝ}
    (hE : MeasurableSet E) :
    MeasurableSet (imaginaryCoefficientLargePart E beta N v) := by
  apply hE.inter
  exact measurableSet_le measurable_const
    ((continuous_dyadicDirichletPolynomial_onePlusIT_sparse
      (fun n ↦ ((beta n).im : ℂ)) N).norm.measurable)

/-- Measure-level form used after applying the real-coefficient
Heath--Brown theorem to the two parts separately. -/
theorem volume_complexBin_le_realPart_add_imaginaryPart
    {E : Set ℝ} {beta : ℕ → ℂ} {N v : ℝ}
    (hlower : ∀ t ∈ E,
      v ≤ ‖dyadicDirichletPolynomial beta N (onePlusIT t)‖) :
    volume E ≤ volume (realCoefficientLargePart E beta N v) +
      volume (imaginaryCoefficientLargePart E beta N v) := by
  calc
    volume E = volume
        (realCoefficientLargePart E beta N v ∪
          imaginaryCoefficientLargePart E beta N v) := by
      rw [real_union_imaginaryCoefficientLargePart_eq hlower]
    _ ≤ volume (realCoefficientLargePart E beta N v) +
        volume (imaginaryCoefficientLargePart E beta N v) :=
      measure_union_le _ _

theorem volumeReal_complexBin_le_realPart_add_imaginaryPart
    {E : Set ℝ} {beta : ℕ → ℂ} {N v : ℝ}
    (hlower : ∀ t ∈ E,
      v ≤ ‖dyadicDirichletPolynomial beta N (onePlusIT t)‖) :
    volume.real E ≤
      volume.real (realCoefficientLargePart E beta N v) +
        volume.real (imaginaryCoefficientLargePart E beta N v) := by
  calc
    volume.real E = volume.real
        (realCoefficientLargePart E beta N v ∪
          imaginaryCoefficientLargePart E beta N v) := by
      rw [real_union_imaginaryCoefficientLargePart_eq hlower]
    _ ≤ volume.real (realCoefficientLargePart E beta N v) +
        volume.real (imaginaryCoefficientLargePart E beta N v) :=
      measureReal_union_le _ _

/-- A reusable raw first-branch estimate on an arbitrary measurable set
with pointwise lower bounds for the sparse polynomial and one
real-coefficient dyadic polynomial. -/
theorem measure_set_le_firstBranchRaw_real
    (hHB : MatomakiTeravainenLemmaThreeFourStatement)
    {eta T M N q v : ℝ} {S : Finset ℕ} {k : ℕ} {a : ℕ → ℝ}
    {E : Set ℝ}
    (heta : 0 < eta)
    (hM : 1 ≤ M) (hMT : M ≤ T) (hN : 2 ≤ N)
    (hq : 0 < q) (hv : 0 < v)
    (hSprime : ∀ p ∈ S, Nat.Prime p)
    (hsupport : ∀ m ∈ primePowerSupport S k,
      M ≤ (m : ℝ) ∧ (m : ℝ) ≤ T)
    (hshort : N ≥ T ^ (2 / 3 : ℝ) ∨
      ((primePowerSupport S k).card : ℝ) ≤ T ^ (1 / 3 : ℝ))
    (hEmeas : MeasurableSet E) (hEsub : E ⊆ Set.Icc (-T) T)
    (hQlower : ∀ t ∈ E,
      q ≤ ‖primePowerPolynomial S k (onePlusIT t)‖)
    (hAlower : ∀ t ∈ E,
      v ≤ ‖dyadicDirichletPolynomial (fun n ↦ (a n : ℂ)) N
        (onePlusIT t)‖) :
    ∃ C : ℝ, 0 < C ∧
      let R : ℝ := ((primePowerSupport S k).card : ℝ)
      let A₀ : ℝ := dyadicRealCoefficientSup a N
      volume.real E ≤
        (C *
          ((R / M) ^ (2 : ℕ) +
            (N * T) ^ eta * (R * T / (M ^ (2 : ℕ) * N))) *
          A₀ ^ (2 : ℕ)) /
            (q ^ (2 : ℕ) * v ^ (2 : ℕ)) := by
  let Q : ℝ → ℂ := fun t ↦ primePowerPolynomial S k (onePlusIT t)
  let A : ℝ → ℂ := fun t ↦
    dyadicDirichletPolynomial (fun n ↦ (a n : ℂ)) N (onePlusIT t)
  have hQcont : Continuous Q :=
    continuous_primePowerPolynomial_onePlusIT_sparse S k
  have hAcont : Continuous A :=
    continuous_dyadicDirichletPolynomial_onePlusIT_sparse _ N
  have hintWhole : IntegrableOn
      (fun t ↦ ‖Q t‖ ^ (2 : ℕ) * ‖A t‖ ^ (2 : ℕ))
      (Set.Icc (-T) T) :=
    ((hQcont.norm.pow 2).mul (hAcont.norm.pow 2)).integrableOn_Icc
  have hintE := hintWhole.mono_set hEsub
  have hEfinite : volume E ≠ (⊤ : ENNReal) :=
    ne_of_lt ((measure_mono hEsub).trans_lt measure_Icc_lt_top)
  have hnonneg : ∀ t : ℝ,
      0 ≤ ‖Q t‖ ^ (2 : ℕ) * ‖A t‖ ^ (2 : ℕ) := by
    intro t
    positivity
  have hsetToWhole :
      (∫ t in E, ‖Q t‖ ^ (2 : ℕ) * ‖A t‖ ^ (2 : ℕ)) ≤
        ∫ t in Set.Icc (-T) T,
          ‖Q t‖ ^ (2 : ℕ) * ‖A t‖ ^ (2 : ℕ) := by
    apply setIntegral_mono_set hintWhole
    · exact Filter.Eventually.of_forall hnonneg
    · exact Filter.Eventually.of_forall hEsub
  rcases firstBranch_sparseMeanValue_of_matomakiTeravainen hHB
    heta hM hMT hN hSprime hsupport hshort with ⟨C, hC, hsource⟩
  refine ⟨C, hC, ?_⟩
  apply measureReal_le_sparseIntegralBound_div hEmeas hEfinite hq hv
  · exact hQlower
  · exact hAlower
  · exact hintE
  · exact hsetToWhole.trans hsource

/-- Uniform version of the real-coefficient first-branch estimate.

Here the constant is selected before the height, scales, support,
coefficients, and measurable large-value set.  This is the quantifier order
needed when those objects vary with the main asymptotic parameter. -/
theorem measure_set_le_firstBranchRaw_real_uniform
    (hHB : MatomakiTeravainenLemmaThreeFourStatement)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T M N q v : ℝ} {S : Finset ℕ} {k : ℕ}
          {a : ℕ → ℝ} {E : Set ℝ},
        1 ≤ M → M ≤ T → 2 ≤ N →
        0 < q → 0 < v →
        (∀ p ∈ S, Nat.Prime p) →
        (∀ m ∈ primePowerSupport S k,
          M ≤ (m : ℝ) ∧ (m : ℝ) ≤ T) →
        (N ≥ T ^ (2 / 3 : ℝ) ∨
          ((primePowerSupport S k).card : ℝ) ≤ T ^ (1 / 3 : ℝ)) →
        MeasurableSet E → E ⊆ Set.Icc (-T) T →
        (∀ t ∈ E,
          q ≤ ‖primePowerPolynomial S k (onePlusIT t)‖) →
        (∀ t ∈ E,
          v ≤ ‖dyadicDirichletPolynomial (fun n ↦ (a n : ℂ)) N
            (onePlusIT t)‖) →
        volume.real E ≤
          (C *
            (((((primePowerSupport S k).card : ℝ)) / M) ^ (2 : ℕ) +
              (N * T) ^ eta *
                ((((primePowerSupport S k).card : ℝ) * T) /
                  (M ^ (2 : ℕ) * N))) *
            (dyadicRealCoefficientSup a N) ^ (2 : ℕ)) /
              (q ^ (2 : ℕ) * v ^ (2 : ℕ)) := by
  rcases firstBranch_sparseMeanValue_uniform_of_matomakiTeravainen
    hHB heta with ⟨C, hC, hsource⟩
  refine ⟨C, hC, ?_⟩
  intro T M N q v S k a E hM hMT hN hq hv hSprime hsupport hshort
    hEmeas hEsub hQlower hAlower
  let Q : ℝ → ℂ := fun t ↦ primePowerPolynomial S k (onePlusIT t)
  let A : ℝ → ℂ := fun t ↦
    dyadicDirichletPolynomial (fun n ↦ (a n : ℂ)) N (onePlusIT t)
  have hQcont : Continuous Q :=
    continuous_primePowerPolynomial_onePlusIT_sparse S k
  have hAcont : Continuous A :=
    continuous_dyadicDirichletPolynomial_onePlusIT_sparse _ N
  have hintWhole : IntegrableOn
      (fun t ↦ ‖Q t‖ ^ (2 : ℕ) * ‖A t‖ ^ (2 : ℕ))
      (Set.Icc (-T) T) :=
    ((hQcont.norm.pow 2).mul (hAcont.norm.pow 2)).integrableOn_Icc
  have hintE := hintWhole.mono_set hEsub
  have hEfinite : volume E ≠ (⊤ : ENNReal) :=
    ne_of_lt ((measure_mono hEsub).trans_lt measure_Icc_lt_top)
  have hnonneg : ∀ t : ℝ,
      0 ≤ ‖Q t‖ ^ (2 : ℕ) * ‖A t‖ ^ (2 : ℕ) := by
    intro t
    positivity
  have hsetToWhole :
      (∫ t in E, ‖Q t‖ ^ (2 : ℕ) * ‖A t‖ ^ (2 : ℕ)) ≤
        ∫ t in Set.Icc (-T) T,
          ‖Q t‖ ^ (2 : ℕ) * ‖A t‖ ^ (2 : ℕ) := by
    apply setIntegral_mono_set hintWhole
    · exact Filter.Eventually.of_forall hnonneg
    · exact Filter.Eventually.of_forall hEsub
  have hsource' := hsource (a := a) hM hMT hN hSprime hsupport hshort
  apply measureReal_le_sparseIntegralBound_div hEmeas hEfinite hq hv
  · exact hQlower
  · exact hAlower
  · exact hintE
  · exact hsetToWhole.trans hsource'

/-- Uniform complex-coefficient adapter.  A single source constant works
for both the real and imaginary coefficient pieces and is fixed before all
moving scale data. -/
theorem measure_set_le_firstBranchRaw_complex_uniform
    (hHB : MatomakiTeravainenLemmaThreeFourStatement)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ CRe CIm : ℝ, 0 < CRe ∧ 0 < CIm ∧
      ∀ {T M N q v : ℝ} {S : Finset ℕ} {k : ℕ}
          {beta : ℕ → ℂ} {E : Set ℝ},
        1 ≤ M → M ≤ T → 2 ≤ N →
        0 < q → 0 < v →
        (∀ p ∈ S, Nat.Prime p) →
        (∀ m ∈ primePowerSupport S k,
          M ≤ (m : ℝ) ∧ (m : ℝ) ≤ T) →
        (N ≥ T ^ (2 / 3 : ℝ) ∨
          ((primePowerSupport S k).card : ℝ) ≤ T ^ (1 / 3 : ℝ)) →
        MeasurableSet E → E ⊆ Set.Icc (-T) T →
        (∀ t ∈ E,
          q ≤ ‖primePowerPolynomial S k (onePlusIT t)‖) →
        (∀ t ∈ E,
          v ≤ ‖dyadicDirichletPolynomial beta N (onePlusIT t)‖) →
        volume.real E ≤
          (CRe *
            (((((primePowerSupport S k).card : ℝ)) / M) ^ (2 : ℕ) +
              (N * T) ^ eta *
                ((((primePowerSupport S k).card : ℝ) * T) /
                  (M ^ (2 : ℕ) * N))) *
            (dyadicRealCoefficientSup (fun n ↦ (beta n).re) N) ^
              (2 : ℕ)) /
              (q ^ (2 : ℕ) * (v / 2) ^ (2 : ℕ)) +
          (CIm *
            (((((primePowerSupport S k).card : ℝ)) / M) ^ (2 : ℕ) +
              (N * T) ^ eta *
                ((((primePowerSupport S k).card : ℝ) * T) /
                  (M ^ (2 : ℕ) * N))) *
            (dyadicRealCoefficientSup (fun n ↦ (beta n).im) N) ^
              (2 : ℕ)) /
              (q ^ (2 : ℕ) * (v / 2) ^ (2 : ℕ)) := by
  rcases measure_set_le_firstBranchRaw_real_uniform hHB heta with
    ⟨C, hC, hreal⟩
  refine ⟨C, C, hC, hC, ?_⟩
  intro T M N q v S k beta E hM hMT hN hq hv hSprime hsupport hshort
    hEmeas hEsub hQlower hbetalower
  let ERe := realCoefficientLargePart E beta N v
  let EIm := imaginaryCoefficientLargePart E beta N v
  have hEReMeas : MeasurableSet ERe :=
    measurableSet_realCoefficientLargePart hEmeas
  have hEImMeas : MeasurableSet EIm :=
    measurableSet_imaginaryCoefficientLargePart hEmeas
  have hEReSubE : ERe ⊆ E := fun _ ht ↦ ht.1
  have hEImSubE : EIm ⊆ E := fun _ ht ↦ ht.1
  have hEReSub : ERe ⊆ Set.Icc (-T) T := hEReSubE.trans hEsub
  have hEImSub : EIm ⊆ Set.Icc (-T) T := hEImSubE.trans hEsub
  have hvhalf : 0 < v / 2 := by positivity
  have hRe := hreal hM hMT hN hq hvhalf hSprime hsupport hshort
    hEReMeas hEReSub (fun t ht ↦ hQlower t (hEReSubE ht))
    (fun t ht ↦ ht.2)
  have hIm := hreal hM hMT hN hq hvhalf hSprime hsupport hshort
    hEImMeas hEImSub (fun t ht ↦ hQlower t (hEImSubE ht))
    (fun t ht ↦ ht.2)
  exact (volumeReal_complexBin_le_realPart_add_imaginaryPart hbetalower).trans
    (add_le_add hRe hIm)

/-- Complete complex-coefficient adapter for the first branch.  It applies
the real-coefficient source theorem separately to the real and imaginary
parts and recombines them by measure subadditivity. -/
theorem measure_set_le_firstBranchRaw_complex
    (hHB : MatomakiTeravainenLemmaThreeFourStatement)
    {eta T M N q v : ℝ} {S : Finset ℕ} {k : ℕ} {beta : ℕ → ℂ}
    {E : Set ℝ}
    (heta : 0 < eta)
    (hM : 1 ≤ M) (hMT : M ≤ T) (hN : 2 ≤ N)
    (hq : 0 < q) (hv : 0 < v)
    (hSprime : ∀ p ∈ S, Nat.Prime p)
    (hsupport : ∀ m ∈ primePowerSupport S k,
      M ≤ (m : ℝ) ∧ (m : ℝ) ≤ T)
    (hshort : N ≥ T ^ (2 / 3 : ℝ) ∨
      ((primePowerSupport S k).card : ℝ) ≤ T ^ (1 / 3 : ℝ))
    (hEmeas : MeasurableSet E) (hEsub : E ⊆ Set.Icc (-T) T)
    (hQlower : ∀ t ∈ E,
      q ≤ ‖primePowerPolynomial S k (onePlusIT t)‖)
    (hbetalower : ∀ t ∈ E,
      v ≤ ‖dyadicDirichletPolynomial beta N (onePlusIT t)‖) :
    ∃ CRe CIm : ℝ, 0 < CRe ∧ 0 < CIm ∧
      let R : ℝ := ((primePowerSupport S k).card : ℝ)
      let ARe : ℝ := dyadicRealCoefficientSup (fun n ↦ (beta n).re) N
      let AIm : ℝ := dyadicRealCoefficientSup (fun n ↦ (beta n).im) N
      volume.real E ≤
        (CRe *
          ((R / M) ^ (2 : ℕ) +
            (N * T) ^ eta * (R * T / (M ^ (2 : ℕ) * N))) *
          ARe ^ (2 : ℕ)) /
            (q ^ (2 : ℕ) * (v / 2) ^ (2 : ℕ)) +
        (CIm *
          ((R / M) ^ (2 : ℕ) +
            (N * T) ^ eta * (R * T / (M ^ (2 : ℕ) * N))) *
          AIm ^ (2 : ℕ)) /
            (q ^ (2 : ℕ) * (v / 2) ^ (2 : ℕ)) := by
  let ERe := realCoefficientLargePart E beta N v
  let EIm := imaginaryCoefficientLargePart E beta N v
  have hEReMeas : MeasurableSet ERe :=
    measurableSet_realCoefficientLargePart hEmeas
  have hEImMeas : MeasurableSet EIm :=
    measurableSet_imaginaryCoefficientLargePart hEmeas
  have hEReSubE : ERe ⊆ E := fun _ ht ↦ ht.1
  have hEImSubE : EIm ⊆ E := fun _ ht ↦ ht.1
  have hEReSub : ERe ⊆ Set.Icc (-T) T := hEReSubE.trans hEsub
  have hEImSub : EIm ⊆ Set.Icc (-T) T := hEImSubE.trans hEsub
  have hvhalf : 0 < v / 2 := by positivity
  rcases measure_set_le_firstBranchRaw_real hHB heta hM hMT hN hq
    hvhalf hSprime hsupport hshort hEReMeas hEReSub
    (fun t ht ↦ hQlower t (hEReSubE ht))
    (fun t ht ↦ ht.2) with ⟨CRe, hCRe, hRe⟩
  rcases measure_set_le_firstBranchRaw_real hHB heta hM hMT hN hq
    hvhalf hSprime hsupport hshort hEImMeas hEImSub
    (fun t ht ↦ hQlower t (hEImSubE ht))
    (fun t ht ↦ ht.2) with ⟨CIm, hCIm, hIm⟩
  refine ⟨CRe, CIm, hCRe, hCIm, ?_⟩
  exact (volumeReal_complexBin_le_realPart_add_imaginaryPart hbetalower).trans
    (add_le_add hRe hIm)


def complexCoefficientSplitModule : ProofModule :=
  { name := "Sparse.ComplexCoefficientSplit"
    paperLocation := "Section 6.1, first sparse branch coefficient reduction"
    purpose :=
      "Split a complex-coefficient dyadic polynomial into measurable real- and imaginary-coefficient large parts, then apply the real-coefficient sparse mean-value theorem twice to obtain the complete complex-coefficient first-branch raw volume bound."
    dependsOn := ["Sparse.FirstBranch", "Sparse.MeasureBridge"]
    status := .proved }

end
end Sparse
end ExactSemiprimes
