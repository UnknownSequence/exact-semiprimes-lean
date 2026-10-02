import ExactSemiprimes.Sparse.FirstBranch

/-! Scratch implementation of the literal two-polynomial magnitude bin and
its first Heath--Brown raw measure estimate. -/

namespace ExactSemiprimes
namespace Sparse

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

/-- A precise version of the paper's `V_{σ₁,σ₂}`: each magnitude lies in
the half-open dyadic window `[Mⱼ^{-σⱼ},2Mⱼ^{-σⱼ})`. -/
def sparseMagnitudeBin (U : Set ℝ) (F₁ F₂ : ℂ → ℂ)
    (M₁ M₂ sigma₁ sigma₂ : ℝ) : Set ℝ :=
  U ∩
    {t | M₁ ^ (-sigma₁) ≤ ‖F₁ (onePlusIT t)‖ ∧
      ‖F₁ (onePlusIT t)‖ < 2 * M₁ ^ (-sigma₁)} ∩
    {t | M₂ ^ (-sigma₂) ≤ ‖F₂ (onePlusIT t)‖ ∧
      ‖F₂ (onePlusIT t)‖ < 2 * M₂ ^ (-sigma₂)}

@[simp]
theorem mem_sparseMagnitudeBin {U : Set ℝ} {F₁ F₂ : ℂ → ℂ}
    {M₁ M₂ sigma₁ sigma₂ t : ℝ} :
    t ∈ sparseMagnitudeBin U F₁ F₂ M₁ M₂ sigma₁ sigma₂ ↔
      t ∈ U ∧
      M₁ ^ (-sigma₁) ≤ ‖F₁ (onePlusIT t)‖ ∧
      ‖F₁ (onePlusIT t)‖ < 2 * M₁ ^ (-sigma₁) ∧
      M₂ ^ (-sigma₂) ≤ ‖F₂ (onePlusIT t)‖ ∧
      ‖F₂ (onePlusIT t)‖ < 2 * M₂ ^ (-sigma₂) := by
  simp only [sparseMagnitudeBin, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

theorem measurableSet_sparseMagnitudeBin
    {U : Set ℝ} {F₁ F₂ : ℂ → ℂ} {M₁ M₂ sigma₁ sigma₂ : ℝ}
    (hU : MeasurableSet U)
    (hF₁ : Measurable (fun t : ℝ ↦ ‖F₁ (onePlusIT t)‖))
    (hF₂ : Measurable (fun t : ℝ ↦ ‖F₂ (onePlusIT t)‖)) :
    MeasurableSet (sparseMagnitudeBin U F₁ F₂ M₁ M₂ sigma₁ sigma₂) := by
  unfold sparseMagnitudeBin
  exact (hU.inter
    ((measurableSet_le measurable_const hF₁).inter
      (measurableSet_lt hF₁ measurable_const))).inter
    ((measurableSet_le measurable_const hF₂).inter
      (measurableSet_lt hF₂ measurable_const))

theorem sparseMagnitudeBin_subset_ambient
    (U : Set ℝ) (F₁ F₂ : ℂ → ℂ) (M₁ M₂ sigma₁ sigma₂ : ℝ) :
    sparseMagnitudeBin U F₁ F₂ M₁ M₂ sigma₁ sigma₂ ⊆ U := by
  intro t ht
  exact (mem_sparseMagnitudeBin.mp ht).1

private theorem continuous_onePlusIT_firstBranchBin : Continuous onePlusIT := by
  unfold onePlusIT
  fun_prop

private theorem continuous_natCpow_neg_onePlusIT_firstBranchBin (n : ℕ) :
    Continuous (fun t : ℝ ↦ (n : ℂ) ^ (-onePlusIT t)) := by
  have hexp : Continuous (fun t : ℝ ↦ -onePlusIT t) :=
    continuous_onePlusIT_firstBranchBin.neg
  apply hexp.const_cpow
  right
  intro t ht
  have hre := congrArg Complex.re ht
  simp [onePlusIT] at hre

theorem continuous_dirichletPolynomial_onePlusIT_sparse
    (a : ℕ → ℂ) (S : Finset ℕ) :
    Continuous (fun t : ℝ ↦ dirichletPolynomial a S (onePlusIT t)) := by
  unfold dirichletPolynomial
  apply continuous_finsetSum
  intro n hn
  exact continuous_const.mul
    (continuous_natCpow_neg_onePlusIT_firstBranchBin n)

theorem continuous_primePowerPolynomial_onePlusIT
    (S : Finset ℕ) (k : ℕ) :
    Continuous (fun t : ℝ ↦ primePowerPolynomial S k (onePlusIT t)) := by
  rw [show (fun t : ℝ ↦ primePowerPolynomial S k (onePlusIT t)) =
      fun t : ℝ ↦ dirichletPolynomial
        (fun n ↦ (primePowerCoefficient S k n : ℂ))
        (primePowerSupport S k) (onePlusIT t) by
    funext t
    simpa only [dirichletPolynomial] using
      (primePowerPolynomial_eq_supportSum S k (onePlusIT t))]
  exact continuous_dirichletPolynomial_onePlusIT_sparse _ _

/-- Raw first-branch bound for the actual magnitude bin.  It combines the
source theorem with the bin's `M₂^{-σ₂}` pointwise lower bound and an
arbitrary positive pointwise lower bound `q` for the sparse factor on `U`.
All later exponent simplifications are deliberately outside this theorem. -/
theorem measure_sparseMagnitudeBin_le_firstBranchRaw
    (hHB : MatomakiTeravainenLemmaThreeFourStatement)
    {eta T M N q M₁ M₂ sigma₁ sigma₂ : ℝ}
    {S : Finset ℕ} {k : ℕ} {a : ℕ → ℝ}
    {U : Set ℝ} {F₁ : ℂ → ℂ}
    (heta : 0 < eta)
    (hM : 1 ≤ M) (hMT : M ≤ T) (hN : 2 ≤ N)
    (hM₂ : 0 < M₂) (hq : 0 < q)
    (hSprime : ∀ p ∈ S, Nat.Prime p)
    (hsupport : ∀ m ∈ primePowerSupport S k,
      M ≤ (m : ℝ) ∧ (m : ℝ) ≤ T)
    (hshort : N ≥ T ^ (2 / 3 : ℝ) ∨
      ((primePowerSupport S k).card : ℝ) ≤ T ^ (1 / 3 : ℝ))
    (hUmeas : MeasurableSet U) (hUsub : U ⊆ Set.Icc (-T) T)
    (hF₁ : Measurable (fun t : ℝ ↦ ‖F₁ (onePlusIT t)‖))
    (hQlower : ∀ t ∈ U,
      q ≤ ‖primePowerPolynomial S k (onePlusIT t)‖) :
    ∃ C : ℝ, 0 < C ∧
      let R : ℝ := ((primePowerSupport S k).card : ℝ)
      let A₀ : ℝ := dyadicRealCoefficientSup a N
      volume.real (sparseMagnitudeBin U F₁
        (dyadicDirichletPolynomial (fun n ↦ (a n : ℂ)) N)
        M₁ M₂ sigma₁ sigma₂) ≤
        (C *
          ((R / M) ^ (2 : ℕ) +
            (N * T) ^ eta * (R * T / (M ^ (2 : ℕ) * N))) *
          A₀ ^ (2 : ℕ)) /
            (q ^ (2 : ℕ) * (M₂ ^ (-sigma₂)) ^ (2 : ℕ)) := by
  let F₂ : ℂ → ℂ :=
    dyadicDirichletPolynomial (fun n ↦ (a n : ℂ)) N
  let E : Set ℝ := sparseMagnitudeBin U F₁ F₂ M₁ M₂ sigma₁ sigma₂
  have hF₂cont : Continuous (fun t : ℝ ↦ F₂ (onePlusIT t)) := by
    exact continuous_dirichletPolynomial_onePlusIT_sparse _ _
  have hF₂meas : Measurable (fun t : ℝ ↦ ‖F₂ (onePlusIT t)‖) :=
    hF₂cont.norm.measurable
  have hEmeas : MeasurableSet E :=
    measurableSet_sparseMagnitudeBin hUmeas hF₁ hF₂meas
  have hEsubU : E ⊆ U :=
    sparseMagnitudeBin_subset_ambient U F₁ F₂ M₁ M₂ sigma₁ sigma₂
  have hEsub : E ⊆ Set.Icc (-T) T := hEsubU.trans hUsub
  have hEfinite : volume E ≠ (⊤ : ENNReal) :=
    ne_of_lt ((measure_mono hEsub).trans_lt measure_Icc_lt_top)
  have hQcont : Continuous (fun t : ℝ ↦
      primePowerPolynomial S k (onePlusIT t)) :=
    continuous_primePowerPolynomial_onePlusIT S k
  have hintWhole : IntegrableOn
      (fun t : ℝ ↦
        ‖primePowerPolynomial S k (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖F₂ (onePlusIT t)‖ ^ (2 : ℕ))
      (Set.Icc (-T) T) :=
    ((hQcont.norm.pow 2).mul (hF₂cont.norm.pow 2)).integrableOn_Icc
  have hintE := hintWhole.mono_set hEsub
  have hnonneg : ∀ t : ℝ,
      0 ≤ ‖primePowerPolynomial S k (onePlusIT t)‖ ^ (2 : ℕ) *
        ‖F₂ (onePlusIT t)‖ ^ (2 : ℕ) := by
    intro t
    positivity
  have hsetToWhole :
      (∫ t in E,
        ‖primePowerPolynomial S k (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖F₂ (onePlusIT t)‖ ^ (2 : ℕ)) ≤
      ∫ t in Set.Icc (-T) T,
        ‖primePowerPolynomial S k (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖F₂ (onePlusIT t)‖ ^ (2 : ℕ) := by
    apply setIntegral_mono_set hintWhole
    · exact Filter.Eventually.of_forall hnonneg
    · exact Filter.Eventually.of_forall hEsub
  rcases firstBranch_sparseMeanValue_of_matomakiTeravainen hHB
    heta hM hMT hN hSprime hsupport hshort with ⟨C, hC, hsource⟩
  refine ⟨C, hC, ?_⟩
  apply measureReal_le_sparseIntegralBound_div hEmeas hEfinite hq
    (Real.rpow_pos_of_pos hM₂ (-sigma₂))
  · intro t ht
    exact hQlower t (hEsubU ht)
  · intro t ht
    exact (mem_sparseMagnitudeBin.mp ht).2.2.2.1
  · exact hintE
  · exact hsetToWhole.trans hsource

/-- Final logical assembly of the first branch: its first sufficient
condition always holds under the paper's power hypotheses, while the second
condition either closes the branch or furnishes the explicit residual range
used by the powered second branch. -/
theorem firstBranch_conditions_or_residual_of_power_bounds
    {X M M₁ a epsilon sigma₁ theta scaleError error : ℝ}
    (hX : 1 < X) (hM : 0 < M) (hMX : M ≤ X)
    (hM₁ : X ^ (epsilon / 2) ≤ M₁) (hM₁pos : 0 < M₁)
    (hepsilon : 0 ≤ epsilon)
    (hsigma₁ : 1 / 5 + 2 * epsilon ≤ sigma₁)
    (ha : 1 < a)
    (htheta : Real.log M₁ / Real.log X = theta)
    (hMExponent : 1 - scaleError ≤ Real.log M / Real.log X) :
    (M ^ (epsilon / 5) ≤ M₁ ^ (2 * sigma₁) / X ^ (epsilon ^ 2) ∧
      M₁ ^ (1 - 2 * sigma₁) ≤
        X ^ (-error) * M ^ (1 - 1 / a)) ∨
    (M ^ (epsilon / 5) ≤ M₁ ^ (2 * sigma₁) / X ^ (epsilon ^ 2) ∧
      1 - 1 / a - (error + scaleError * (1 - 1 / a)) ≤
        theta * (1 - 2 * sigma₁)) := by
  have hfirst :
      M ^ (epsilon / 5) ≤ M₁ ^ (2 * sigma₁) / X ^ (epsilon ^ 2) :=
    firstBranch_first_condition_of_power_bounds hX.le hM.le hMX hM₁
      hepsilon hsigma₁
  by_cases hsecond : M₁ ^ (1 - 2 * sigma₁) ≤
      X ^ (-error) * M ^ (1 - 1 / a)
  · exact Or.inl ⟨hfirst, hsecond⟩
  · exact Or.inr ⟨hfirst,
      firstBranch_residual_of_second_condition_failure hX hM hM₁pos ha
        htheta hMExponent hsecond⟩

def magnitudeBinsModule : ProofModule :=
  { name := "Sparse.MagnitudeBins"
    paperLocation := "Section 6.1, first Heath--Brown branch"
    purpose :=
      "Define the literal half-open two-polynomial magnitude bins and derive their raw volume bound from the cited Matomäki--Teräväinen sparse mean-value theorem."
    dependsOn :=
      [ "Sparse.FirstBranch",
        "Sparse.MeasureBridge",
        "Assumptions.matomakiTeravainenLemmaThreeFour" ]
    status := .proved }

end
end Sparse
end ExactSemiprimes
