import ExactSemiprimes.Sparse.MeasureBridge
import ExactSemiprimes.Sparse.QLowerBound
import ExactSemiprimes.Sparse.ResidualRange

/-! # First Heath--Brown sparse branch -/

namespace ExactSemiprimes
namespace Sparse

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

/-! ## The first sufficient condition -/

/-- The exponent budget used for the first condition in the first sparse
branch.  The paper assumes a little more than is needed: the hypothesis
`sigma ≥ 1/5 + 2 * epsilon` leaves an extra `epsilon^2` of room. -/
theorem firstBranch_exponent_budget {epsilon sigma : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hsigma : 1 / 5 + 2 * epsilon ≤ sigma) :
    epsilon / 5 + epsilon ^ 2 ≤ (epsilon / 2) * (2 * sigma) := by
  nlinarith [mul_nonneg hepsilon (sub_nonneg.mpr hsigma)]

/-- A constant-one version of the paper's first sufficient condition.

If `M ≤ X`, `M₁ ≥ X^(epsilon/2)`, and
`sigma₁ ≥ 1/5 + 2 epsilon`, then
`M^(epsilon/5) ≤ M₁^(2 sigma₁) / X^(epsilon^2)`.  Thus the
Vinogradov-symbol version follows immediately, without using the external
sparse mean-value theorem. -/
theorem firstBranch_first_condition_of_power_bounds
    {X M M₁ epsilon sigma₁ : ℝ}
    (hX : 1 ≤ X) (hM : 0 ≤ M) (hMX : M ≤ X)
    (hM₁ : X ^ (epsilon / 2) ≤ M₁)
    (hepsilon : 0 ≤ epsilon)
    (hsigma₁ : 1 / 5 + 2 * epsilon ≤ sigma₁) :
    M ^ (epsilon / 5) ≤ M₁ ^ (2 * sigma₁) / X ^ (epsilon ^ 2) := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hepsilonFive : 0 ≤ epsilon / 5 := by positivity
  have hepsilonSq : 0 ≤ epsilon ^ 2 := sq_nonneg epsilon
  have hsigmaNonneg : 0 ≤ 2 * sigma₁ := by
    have : 0 ≤ sigma₁ := by nlinarith
    positivity
  have hMpower : M ^ (epsilon / 5) ≤ X ^ (epsilon / 5) :=
    Real.rpow_le_rpow hM hMX hepsilonFive
  have hM₁power : (X ^ (epsilon / 2)) ^ (2 * sigma₁) ≤
      M₁ ^ (2 * sigma₁) :=
    Real.rpow_le_rpow (Real.rpow_nonneg hXpos.le _) hM₁ hsigmaNonneg
  have hproduct :
      M ^ (epsilon / 5) * X ^ (epsilon ^ 2) ≤
        M₁ ^ (2 * sigma₁) := by
    calc
      M ^ (epsilon / 5) * X ^ (epsilon ^ 2)
          ≤ X ^ (epsilon / 5) * X ^ (epsilon ^ 2) :=
            mul_le_mul_of_nonneg_right hMpower
              (Real.rpow_nonneg hXpos.le _)
      _ = X ^ (epsilon / 5 + epsilon ^ 2) := by
            rw [Real.rpow_add hXpos]
      _ ≤ X ^ ((epsilon / 2) * (2 * sigma₁)) :=
            Real.rpow_le_rpow_of_exponent_le hX
              (firstBranch_exponent_budget hepsilon hsigma₁)
      _ = (X ^ (epsilon / 2)) ^ (2 * sigma₁) :=
            Real.rpow_mul hXpos.le _ _
      _ ≤ M₁ ^ (2 * sigma₁) := hM₁power
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hXpos _)).2 hproduct

/-! ## Logarithmic comparison and the residual range -/

/-- Exact conversion of the second sufficient power inequality into an
inequality between logarithms to base `X`.  All bases are assumed positive,
and `X > 1` makes division by `log X` order preserving. -/
theorem firstBranch_second_condition_iff_normalizedLogs
    {X M M₁ a sigma₁ error : ℝ}
    (hX : 1 < X) (hM : 0 < M) (hM₁ : 0 < M₁) :
    M₁ ^ (1 - 2 * sigma₁) ≤
        X ^ (-error) * M ^ (1 - 1 / a) ↔
      (Real.log M₁ / Real.log X) * (1 - 2 * sigma₁) ≤
        -error + (Real.log M / Real.log X) * (1 - 1 / a) := by
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hlogX : 0 < Real.log X := Real.log_pos hX
  have hleft : 0 < M₁ ^ (1 - 2 * sigma₁) :=
    Real.rpow_pos_of_pos hM₁ _
  have hright : 0 < X ^ (-error) * M ^ (1 - 1 / a) :=
    mul_pos (Real.rpow_pos_of_pos hXpos _) (Real.rpow_pos_of_pos hM _)
  rw [← Real.log_le_log_iff hleft hright,
    Real.log_rpow hM₁, Real.log_mul
      (ne_of_gt (Real.rpow_pos_of_pos hXpos _))
      (ne_of_gt (Real.rpow_pos_of_pos hM _)),
    Real.log_rpow hXpos, Real.log_rpow hM]
  have hleftNorm :
      (1 - 2 * sigma₁) * Real.log M₁ / Real.log X =
        (Real.log M₁ / Real.log X) * (1 - 2 * sigma₁) := by
    ring
  have hrightNorm :
      ((-error) * Real.log X + (1 - 1 / a) * Real.log M) /
          Real.log X =
        -error + (Real.log M / Real.log X) * (1 - 1 / a) := by
    field_simp [ne_of_gt hlogX]
  rw [← hleftNorm, ← hrightNorm, div_le_div_iff_of_pos_right hlogX]

/-- If the second sufficient condition fails, its strict reverse yields the
paper's residual inequality.  The hypothesis on `M` is expressed exactly as
a lower bound for its logarithmic exponent; the resulting loss is displayed
without `O`-notation. -/
theorem firstBranch_residual_of_second_condition_failure
    {X M M₁ a sigma₁ theta scaleError error : ℝ}
    (hX : 1 < X) (hM : 0 < M) (hM₁ : 0 < M₁)
    (ha : 1 < a)
    (htheta : Real.log M₁ / Real.log X = theta)
    (hMExponent : 1 - scaleError ≤ Real.log M / Real.log X)
    (hFailure : ¬ M₁ ^ (1 - 2 * sigma₁) ≤
      X ^ (-error) * M ^ (1 - 1 / a)) :
    1 - 1 / a - (error + scaleError * (1 - 1 / a)) ≤
      theta * (1 - 2 * sigma₁) := by
  have hNormalizedFailure : ¬
      (Real.log M₁ / Real.log X) * (1 - 2 * sigma₁) ≤
        -error + (Real.log M / Real.log X) * (1 - 1 / a) := by
    intro h
    exact hFailure
      ((firstBranch_second_condition_iff_normalizedLogs hX hM hM₁).2 h)
  have hReverse :
      -error + (Real.log M / Real.log X) * (1 - 1 / a) ≤
        theta * (1 - 2 * sigma₁) := by
    have hStrict := lt_of_not_ge hNormalizedFailure
    rw [htheta] at hStrict
    exact hStrict.le
  have hPositiveExponent : 0 ≤ 1 - 1 / a := by
    have haPos : 0 < a := zero_lt_one.trans ha
    rw [sub_nonneg, div_le_one haPos]
    exact ha.le
  have hScale := mul_le_mul_of_nonneg_right hMExponent hPositiveExponent
  calc
    1 - 1 / a - (error + scaleError * (1 - 1 / a)) =
        -error + (1 - scaleError) * (1 - 1 / a) := by ring
    _ ≤ -error + (Real.log M / Real.log X) * (1 - 1 / a) := by
      gcongr
    _ ≤ theta * (1 - 2 * sigma₁) := hReverse

/-! ## Source-closed sparse mean-value insertion -/

/-- Specialization of Matomäki--Teräväinen Lemma 3.4 to the normalized
prime-power polynomial.  The coefficient bound is derived from the exact
tuple-fibre combinatorics, and the hypothesis eliminating the source's third
term is kept explicit. -/
theorem firstBranch_sparseMeanValue_of_matomakiTeravainen
    (hHB : MatomakiTeravainenLemmaThreeFourStatement)
    {eta T M N : ℝ} {S : Finset ℕ} {k : ℕ} {a : ℕ → ℝ}
    (heta : 0 < eta)
    (hM : 1 ≤ M) (hMT : M ≤ T) (hN : 2 ≤ N)
    (hSprime : ∀ p ∈ S, Nat.Prime p)
    (hsupport : ∀ m ∈ primePowerSupport S k,
      M ≤ (m : ℝ) ∧ (m : ℝ) ≤ T)
    (hshort : N ≥ T ^ (2 / 3 : ℝ) ∨
      ((primePowerSupport S k).card : ℝ) ≤ T ^ (1 / 3 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      let I : ℝ := ∫ t in Set.Icc (-T) T,
        ‖primePowerPolynomial S k (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖dyadicDirichletPolynomial (fun n ↦ (a n : ℂ)) N
            (onePlusIT t)‖ ^ (2 : ℕ)
      let R : ℝ := ((primePowerSupport S k).card : ℝ)
      let A₀ : ℝ := dyadicRealCoefficientSup a N
      I ≤ C *
        ((R / M) ^ (2 : ℕ) +
          (N * T) ^ eta * (R * T / (M ^ (2 : ℕ) * N))) *
        A₀ ^ (2 : ℕ) := by
  rcases hHB eta heta with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  let epsilon : ℕ → ℂ :=
    fun n ↦ (primePowerCoefficient S k n : ℂ)
  have hepsilon : ∀ m ∈ primePowerSupport S k, ‖epsilon m‖ ≤ 1 := by
    intro m hm
    rw [show epsilon m = (primePowerCoefficient S k m : ℂ) by rfl,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (primePowerCoefficient_nonneg S k m)]
    exact primePowerCoefficient_le_one hSprime
  have hsource := (hbound T M N (primePowerSupport S k) epsilon a
    hM hMT hN hsupport hepsilon).2 hshort
  have hpoly (s : ℂ) :
      dirichletPolynomial epsilon (primePowerSupport S k) s =
        primePowerPolynomial S k s := by
    rw [primePowerPolynomial_eq_supportSum]
    rfl
  simpa only [hpoly] using hsource

/-- Uniform-constant form of the preceding specialization.

The order of the quantifiers is important in moving-scale applications:
the constant supplied by [MT23, Lemma 3.4] is chosen after `eta`, but before
`T`, the two polynomial scales, their supports, and their coefficients.  The
fixed-scale theorem above is convenient locally, while this version exposes
the source theorem's actual uniformity. -/
theorem firstBranch_sparseMeanValue_uniform_of_matomakiTeravainen
    (hHB : MatomakiTeravainenLemmaThreeFourStatement)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T M N : ℝ} {S : Finset ℕ} {k : ℕ} {a : ℕ → ℝ},
        1 ≤ M → M ≤ T → 2 ≤ N →
        (∀ p ∈ S, Nat.Prime p) →
        (∀ m ∈ primePowerSupport S k,
          M ≤ (m : ℝ) ∧ (m : ℝ) ≤ T) →
        (N ≥ T ^ (2 / 3 : ℝ) ∨
          ((primePowerSupport S k).card : ℝ) ≤ T ^ (1 / 3 : ℝ)) →
        (∫ t in Set.Icc (-T) T,
            ‖primePowerPolynomial S k (onePlusIT t)‖ ^ (2 : ℕ) *
              ‖dyadicDirichletPolynomial (fun n ↦ (a n : ℂ)) N
                (onePlusIT t)‖ ^ (2 : ℕ)) ≤
          C *
            (((((primePowerSupport S k).card : ℝ)) / M) ^ (2 : ℕ) +
              (N * T) ^ eta *
                ((((primePowerSupport S k).card : ℝ) * T) /
                  (M ^ (2 : ℕ) * N))) *
            (dyadicRealCoefficientSup a N) ^ (2 : ℕ) := by
  rcases hHB eta heta with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro T M N S k a hM hMT hN hSprime hsupport hshort
  let epsilon : ℕ → ℂ :=
    fun n ↦ (primePowerCoefficient S k n : ℂ)
  have hepsilon : ∀ m ∈ primePowerSupport S k, ‖epsilon m‖ ≤ 1 := by
    intro m hm
    rw [show epsilon m = (primePowerCoefficient S k m : ℂ) by rfl,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (primePowerCoefficient_nonneg S k m)]
    exact primePowerCoefficient_le_one hSprime
  have hsource := (hbound T M N (primePowerSupport S k) epsilon a
    hM hMT hN hsupport hepsilon).2 hshort
  have hpoly (s : ℂ) :
      dirichletPolynomial epsilon (primePowerSupport S k) s =
        primePowerPolynomial S k s := by
    rw [primePowerPolynomial_eq_supportSum]
    rfl
  simpa only [hpoly] using hsource

private theorem continuous_onePlusIT_firstBranch : Continuous onePlusIT := by
  unfold onePlusIT
  fun_prop

private theorem continuous_natCpow_neg_onePlusIT_firstBranch (n : ℕ) :
    Continuous (fun t : ℝ ↦ (n : ℂ) ^ (-onePlusIT t)) := by
  have hexp : Continuous (fun t : ℝ ↦ -onePlusIT t) :=
    continuous_onePlusIT_firstBranch.neg
  apply hexp.const_cpow
  right
  intro t ht
  have hre := congrArg Complex.re ht
  simp [onePlusIT] at hre

private theorem continuous_dirichletPolynomial_onePlusIT_firstBranch
    (a : ℕ → ℂ) (S : Finset ℕ) :
    Continuous (fun t : ℝ ↦ dirichletPolynomial a S (onePlusIT t)) := by
  unfold dirichletPolynomial
  apply continuous_finsetSum
  intro n hn
  exact continuous_const.mul (continuous_natCpow_neg_onePlusIT_firstBranch n)

private theorem integrableOn_firstBranch_weight
    {S : Finset ℕ} {k : ℕ} {a : ℕ → ℝ} {T N : ℝ} :
    IntegrableOn
      (fun t : ℝ ↦
        ‖primePowerPolynomial S k (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖dyadicDirichletPolynomial (fun n ↦ (a n : ℂ)) N
            (onePlusIT t)‖ ^ (2 : ℕ))
      (Set.Icc (-T) T) := by
  have hQpoly :
      Continuous (fun t : ℝ ↦ primePowerPolynomial S k (onePlusIT t)) := by
    rw [show (fun t : ℝ ↦ primePowerPolynomial S k (onePlusIT t)) =
        fun t : ℝ ↦ dirichletPolynomial
          (fun n ↦ (primePowerCoefficient S k n : ℂ))
          (primePowerSupport S k) (onePlusIT t) by
      funext t
      simpa only [dirichletPolynomial] using
        (primePowerPolynomial_eq_supportSum S k (onePlusIT t))]
    exact continuous_dirichletPolynomial_onePlusIT_firstBranch _ _
  have hQ := hQpoly.norm.pow 2
  have hA : Continuous (fun t : ℝ ↦
      ‖dyadicDirichletPolynomial (fun n ↦ (a n : ℂ)) N
        (onePlusIT t)‖ ^ (2 : ℕ)) :=
    (continuous_dirichletPolynomial_onePlusIT_firstBranch
      (fun n ↦ (a n : ℂ)) (dyadicInterval N)).norm.pow 2
  exact (hQ.mul hA).integrableOn_Icc

/-- The large-value consequence of the first Heath--Brown application.
The measurable set `V` can be instantiated by a logarithmic magnitude bin;
the lower bound on the integrand converts the source integral estimate into
the required estimate for its real volume. -/
theorem firstBranch_volume_mul_lowerBound_le_of_matomakiTeravainen
    (hHB : MatomakiTeravainenLemmaThreeFourStatement)
    {eta T M N L : ℝ} {S : Finset ℕ} {k : ℕ} {a : ℕ → ℝ}
    {V : Set ℝ}
    (heta : 0 < eta)
    (hM : 1 ≤ M) (hMT : M ≤ T) (hN : 2 ≤ N)
    (hSprime : ∀ p ∈ S, Nat.Prime p)
    (hsupport : ∀ m ∈ primePowerSupport S k,
      M ≤ (m : ℝ) ∧ (m : ℝ) ≤ T)
    (hshort : N ≥ T ^ (2 / 3 : ℝ) ∨
      ((primePowerSupport S k).card : ℝ) ≤ T ^ (1 / 3 : ℝ))
    (hV : MeasurableSet V) (hVsub : V ⊆ Set.Icc (-T) T)
    (hlower : ∀ t ∈ V,
      L ≤ ‖primePowerPolynomial S k (onePlusIT t)‖ ^ (2 : ℕ) *
        ‖dyadicDirichletPolynomial (fun n ↦ (a n : ℂ)) N
          (onePlusIT t)‖ ^ (2 : ℕ)) :
    ∃ C : ℝ, 0 < C ∧
      let R : ℝ := ((primePowerSupport S k).card : ℝ)
      let A₀ : ℝ := dyadicRealCoefficientSup a N
      volume.real V * L ≤ C *
        ((R / M) ^ (2 : ℕ) +
          (N * T) ^ eta * (R * T / (M ^ (2 : ℕ) * N))) *
        A₀ ^ (2 : ℕ) := by
  rcases firstBranch_sparseMeanValue_of_matomakiTeravainen hHB
    heta hM hMT hN hSprime hsupport hshort with ⟨C, hC, hsource⟩
  refine ⟨C, hC, ?_⟩
  let f : ℝ → ℝ := fun t ↦
    ‖primePowerPolynomial S k (onePlusIT t)‖ ^ (2 : ℕ) *
      ‖dyadicDirichletPolynomial (fun n ↦ (a n : ℂ)) N
        (onePlusIT t)‖ ^ (2 : ℕ)
  have hVfin : volume V ≠ (⊤ : ENNReal) :=
    ne_of_lt ((measure_mono hVsub).trans_lt measure_Icc_lt_top)
  have hconst : IntegrableOn (fun _ : ℝ ↦ L) V :=
    integrableOn_const hVfin
  have hfIcc : IntegrableOn f (Set.Icc (-T) T) := by
    exact integrableOn_firstBranch_weight
  have hfV : IntegrableOn f V := hfIcc.mono_set hVsub
  have hlowerIntegral : volume.real V * L ≤ ∫ t in V, f t := by
    calc
      volume.real V * L = ∫ _t in V, L := by
        simp [MeasureTheory.integral_const]
      _ ≤ ∫ t in V, f t :=
        setIntegral_mono_on hconst hfV hV hlower
  have hnonneg : ∀ t : ℝ, 0 ≤ f t := by
    intro t
    dsimp [f]
    positivity
  have htoWhole : (∫ t in V, f t) ≤ ∫ t in Set.Icc (-T) T, f t := by
    apply setIntegral_mono_set hfIcc
    · exact Filter.Eventually.of_forall hnonneg
    · exact Filter.Eventually.of_forall hVsub
  exact hlowerIntegral.trans (htoWhole.trans hsource)

def firstBranchModule : ProofModule :=
  { name := "Sparse.FirstBranch"
    paperLocation := "Section 6.1, first Heath--Brown branch"
    purpose :=
      "Specialize the cited sparse mean-value theorem to the normalized prime-power polynomial, convert its integral estimate into a measure bound for any measurable magnitude bin, and identify the residual range. Concrete bin construction and parameter propagation are handled downstream."
    dependsOn :=
      [ "Sparse.SupportGeometry",
        "Sparse.MeasureBridge",
        "Sparse.QLowerBound",
        "Assumptions.matomakiTeravainenLemmaThreeFour" ]
    status := .proved }

end

end Sparse
end ExactSemiprimes
