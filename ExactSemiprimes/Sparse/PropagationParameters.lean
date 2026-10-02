import ExactSemiprimes.Sparse.PropagationMoving

/-!
# Moving-parameter transfers for sparse propagation

This file discharges the two elementary coordinate implications left
explicit in `PropagationMoving`.  The first branch only spends a reserved
amount of the exponent `firstError`.  In the second branch the literal
complementary length may differ from `X^(1-theta)`; the hypothesis
`1-theta-phi <= productLoss` records that discrepancy, and the key-error
budget pays exactly `2*sigma2*productLoss` for it.
-/

namespace ExactSemiprimes
namespace Sparse

open MeasureTheory Set Filter

noncomputable section

/-- A larger reserved first-branch error implies the precise
`epsilon/3` power condition used by the first majorant. -/
theorem firstBranch_coordinateTransfer_of_errorReserve
    {X M M1 a epsilon mu theta sigma1 firstError : ℝ}
    (hX : 1 < X) (hMcoord : M = X ^ mu)
    (hM1coord : M1 = X ^ theta)
    (hreserve : epsilon / 3 ≤ firstError) :
    M1 ^ (1 - 2 * sigma1) ≤
          X ^ (-firstError) * M ^ (1 - 1 / a) →
      theta * (1 - 2 * sigma1) ≤
        -epsilon / 3 + mu * (1 - 1 / a) := by
  intro hpower
  have hMnonneg : 0 ≤ M := by
    rw [hMcoord]
    exact Real.rpow_nonneg (zero_le_one.trans hX.le) _
  apply firstBranch_exponentCondition_of_powerCondition
    hX hMcoord hM1coord
  calc
    M1 ^ (1 - 2 * sigma1) ≤
        X ^ (-firstError) * M ^ (1 - 1 / a) := hpower
    _ ≤ X ^ (-epsilon / 3) * M ^ (1 - 1 / a) := by
      apply mul_le_mul_of_nonneg_right
      · apply Real.rpow_le_rpow_of_exponent_le hX.le
        linarith
      · exact Real.rpow_nonneg hMnonneg _

/-- The ideal complementary-coordinate inequality in the dichotomy gives
an exponent inequality before the product-length loss is paid. -/
theorem secondBranch_idealExponent_of_powerCondition
    {X a keyError theta sigma1 sigma2 : ℝ}
    (hX : 1 < X)
    (hpower :
      X ^ (1 / a + keyError) ≤
        (X ^ theta) ^ (5 - 8 * sigma1) *
          (X ^ (1 - theta)) ^ (2 * sigma2)) :
    1 / a + keyError ≤
      (5 - 8 * sigma1) * theta +
        2 * sigma2 * (1 - theta) := by
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hrewritten :
      X ^ (1 / a + keyError) ≤
        X ^ ((5 - 8 * sigma1) * theta +
          2 * sigma2 * (1 - theta)) := by
    calc
      X ^ (1 / a + keyError) ≤
          (X ^ theta) ^ (5 - 8 * sigma1) *
            (X ^ (1 - theta)) ^ (2 * sigma2) := hpower
      _ = X ^ ((5 - 8 * sigma1) * theta +
            2 * sigma2 * (1 - theta)) := by
        rw [← Real.rpow_mul hXpos.le, ← Real.rpow_mul hXpos.le,
          ← Real.rpow_add hXpos]
        congr 1
        ring
  exact (Real.strictMono_rpow_of_base_gt_one hX).le_iff_le.mp hrewritten

/-- The exact second-branch coordinate transfer.  Its budget has a transparent
interpretation: `4*epsilon` is the analytic saving required by the literal
five-block estimate, and `2*sigma2*productLoss` replaces the ideal
complementary coordinate `1-theta` by the actual coordinate `phi`. -/
theorem secondBranch_coordinateTransfer_of_errorReserve
    {X a epsilon keyError theta phi sigma1 sigma2 productLoss : ℝ}
    (hX : 1 < X) (hsigma2 : 0 ≤ sigma2)
    (hproductLoss : 1 - theta - phi ≤ productLoss)
    (hreserve : 4 * epsilon + 2 * sigma2 * productLoss ≤ keyError) :
    X ^ (1 / a + keyError) ≤
          (X ^ theta) ^ (5 - 8 * sigma1) *
            (X ^ (1 - theta)) ^ (2 * sigma2) →
      1 / a + 4 * epsilon ≤
        (5 - 8 * sigma1) * theta + 2 * sigma2 * phi := by
  intro hpower
  have hideal := secondBranch_idealExponent_of_powerCondition hX hpower
  have hcoordinate :
      2 * sigma2 * (1 - theta) ≤
        2 * sigma2 * phi + 2 * sigma2 * productLoss := by
    have hloss : 1 - theta ≤ phi + productLoss := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hloss
      (show 0 ≤ 2 * sigma2 by positivity)]
  linarith

/-- The product loss used in the moving package has its literal value
`epsilon^2/100`.  This convenience theorem records the exact reserve which
remains to be chosen in the endpoint-error box. -/
theorem secondBranch_coordinateTransfer_of_paperLoss
    {X a epsilon keyError theta phi sigma1 sigma2 : ℝ}
    (hX : 1 < X) (hsigma2 : 0 ≤ sigma2)
    (hproductLoss : 1 - theta - phi ≤ epsilon ^ 2 / 100)
    (hreserve :
      4 * epsilon + 2 * sigma2 * (epsilon ^ 2 / 100) ≤ keyError) :
    X ^ (1 / a + keyError) ≤
          (X ^ theta) ^ (5 - 8 * sigma1) *
            (X ^ (1 - theta)) ^ (2 * sigma2) →
      1 / a + 4 * epsilon ≤
        (5 - 8 * sigma1) * theta + 2 * sigma2 * phi := by
  exact secondBranch_coordinateTransfer_of_errorReserve hX hsigma2
    hproductLoss hreserve

/-- Both coordinate implications required by
`sparsePropagation_fixedScale_powerSaving_package`, obtained together from
the explicit paper-scale reserves. -/
theorem sparseCoordinateTransfers_of_paperReserves
    {X M M1 a epsilon mu theta phi sigma1 sigma2
      firstError keyError : ℝ}
    (hX : 1 < X) (hMcoord : M = X ^ mu)
    (hM1coord : M1 = X ^ theta)
    (hfirstReserve : epsilon / 3 ≤ firstError)
    (hsigma2 : 0 ≤ sigma2)
    (hproductLoss : 1 - theta - phi ≤ epsilon ^ 2 / 100)
    (hsecondReserve :
      4 * epsilon + 2 * sigma2 * (epsilon ^ 2 / 100) ≤ keyError) :
    (M1 ^ (1 - 2 * sigma1) ≤
          X ^ (-firstError) * M ^ (1 - 1 / a) →
        theta * (1 - 2 * sigma1) ≤
          -epsilon / 3 + mu * (1 - 1 / a)) ∧
      (X ^ (1 / a + keyError) ≤
          (X ^ theta) ^ (5 - 8 * sigma1) *
            (X ^ (1 - theta)) ^ (2 * sigma2) →
        1 / a + 4 * epsilon ≤
          (5 - 8 * sigma1) * theta + 2 * sigma2 * phi) := by
  exact ⟨
    firstBranch_coordinateTransfer_of_errorReserve
      hX hMcoord hM1coord hfirstReserve,
    secondBranch_coordinateTransfer_of_paperLoss
      hX hsigma2 hproductLoss hsecondReserve⟩

/-- The real/imaginary coefficient loss in the moving package is already
uniformly absorbed by the locally proved global divisor-subpower theorem.
This natural-scale form matches the eventual quantifier used in the final
application. -/
theorem eventually_sparseFirstCoefficientLoss
    {beta : ℕ → ℂ} {B A CRe CIm epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hCRe : 0 ≤ CRe) (hCIm : 0 ≤ CIm)
    (hbeta : IsDivisorBoundedByConstant B A beta) :
    ∀ᶠ X : ℕ in atTop, ∀ M2 : ℝ,
      1 ≤ M2 → M2 ≤ (X : ℝ) →
      4 * (CRe *
            (dyadicRealCoefficientSup (fun n ↦ (beta n).re) M2) ^
              (2 : ℕ) +
          CIm *
            (dyadicRealCoefficientSup (fun n ↦ (beta n).im) M2) ^
              (2 : ℕ)) ≤
        (X : ℝ) ^ (epsilon ^ 2 / 100) := by
  exact eventually_four_weighted_beta_parts_dyadicSup_sq_le_natCast_rpow
    Hybrid.globalDivisorSubpower (by positivity) hCRe hCIm hbeta

/-- Family-uniform coefficient loss in the real ambient-height variable.

Unlike `eventually_sparseFirstCoefficientLoss`, the coefficient sequence is
quantified after the eventual height.  The threshold is therefore common to
every moving sequence carrying the fixed divisor-bound witnesses `B,A`, as
required for the decomposition family in Proposition 2.2. -/
theorem eventually_sparseFirstCoefficientLoss_uniform
    {B A CRe CIm epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hB : 0 ≤ B) (hA : 0 < A)
    (hCRe : 0 ≤ CRe) (hCIm : 0 ≤ CIm) :
    ∀ᶠ X : ℝ in atTop, ∀ (beta : ℕ → ℂ) (M2 : ℝ),
      IsDivisorBoundedByConstant B A beta →
      1 ≤ M2 → M2 ≤ X →
      4 * (CRe *
            (dyadicRealCoefficientSup (fun n ↦ (beta n).re) M2) ^
              (2 : ℕ) +
          CIm *
            (dyadicRealCoefficientSup (fun n ↦ (beta n).im) M2) ^
              (2 : ℕ)) ≤
        X ^ (epsilon ^ 2 / 100) := by
  exact eventually_four_weighted_beta_parts_dyadicSup_sq_le_rpow_uniform
    Hybrid.globalDivisorSubpower (by positivity) hB hA hCRe hCIm

/-- Coordinate form of the family-uniform absorption theorem.  It derives
`M2 ≤ X` from the exact logarithmic coordinate used by sparse propagation,
so its hypotheses are already present in the moving package. -/
theorem eventually_sparseFirstCoefficientLoss_uniform_of_coordinate
    {B A CRe CIm epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hB : 0 ≤ B) (hA : 0 < A)
    (hCRe : 0 ≤ CRe) (hCIm : 0 ≤ CIm) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (beta : ℕ → ℂ) (M2 phi : ℝ),
        IsDivisorBoundedByConstant B A beta →
        1 ≤ M2 → M2 = X ^ phi → phi ≤ 1 →
        4 * (CRe *
              (dyadicRealCoefficientSup (fun n ↦ (beta n).re) M2) ^
                (2 : ℕ) +
            CIm *
              (dyadicRealCoefficientSup (fun n ↦ (beta n).im) M2) ^
                (2 : ℕ)) ≤
          X ^ (epsilon ^ 2 / 100) := by
  have hraw := eventually_sparseFirstCoefficientLoss_uniform
    hepsilon hB hA hCRe hCIm
  filter_upwards [hraw, eventually_ge_atTop (1 : ℝ)] with X hbound hX
  intro beta M2 phi hbeta hM2 hM2coord hphi
  apply hbound beta M2 hbeta hM2
  rw [hM2coord]
  simpa using Real.rpow_le_rpow_of_exponent_le hX hphi

/-! ## Uniform moving-scale analytic package -/

/-- Moving-scale form of sparse propagation with the analytic constants in
the correct order.

For fixed `epsilon` and common divisor witnesses `B,A`, all four constants
are chosen before `X`, all polynomial scales and coordinates, the
coefficients, and the large-value set.  The conclusion returns, for those
same witnesses, the family-uniform eventual coefficient absorption together
with the fixed-scale power-saving implication. -/
theorem sparsePropagation_uniformConstants_powerSaving_package
    (inputs : ExternalInputs) {epsilon B A : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1 / 10)
    (hB : 0 ≤ B) (hA : 0 < A) :
    ∃ CRe CIm C D : ℝ,
      0 < CRe ∧ 0 < CIm ∧ 0 < C ∧ 1 ≤ D ∧
      (∀ᶠ X : ℝ in atTop,
        ∀ (beta : ℕ → ℂ) (M2 phi : ℝ),
        IsDivisorBoundedByConstant B A beta →
        1 ≤ M2 → M2 = X ^ phi → phi ≤ 1 →
        4 * (CRe *
              (dyadicRealCoefficientSup (fun n ↦ (beta n).re) M2) ^
                (2 : ℕ) +
            CIm *
              (dyadicRealCoefficientSup (fun n ↦ (beta n).im) M2) ^
                (2 : ℕ)) ≤
          X ^ (epsilon ^ 2 / 100)) ∧
      ∀ {X P M M1 M2 A0 a theta phi mu sigma1 sigma2
          scaleError firstError residualError keyError : ℝ}
          {k : ℕ} {beta : ℕ → ℂ} {b : ℕ → ℝ} {E : Set ℝ},
        1 < X → P = (Real.log X) ^ a → 1 < a →
        k = ⌊Real.log X / Real.log (2 * P)⌋₊ →
        1 ≤ Real.log (2 * P) → M = P ^ k →
        1 ≤ M → M ≤ X → 0 < M1 → 2 ≤ M2 →
        X ^ (epsilon / 2) ≤ M1 →
        1 / 5 + 2 * epsilon ≤ sigma1 →
        (∀ m ∈ primePowerSupport (dyadicPrimes P) k,
          M ≤ (m : ℝ) ∧ (m : ℝ) ≤ X) →
        ((primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
          X ^ (1 / 3 : ℝ) →
        IsDivisorBoundedByConstant B A0 (fun n ↦ (b n : ℂ)) →
        (∀ j ∈ Finset.range 5,
          2 ≤ (2 : ℝ) ^ j * M1 ^ (5 : ℕ)) →
        MeasurableSet E → E ⊆ Set.Icc (-X) X →
        (∀ t ∈ E,
          P ^ (-epsilon / 10) ≤
            ‖primeBasePolynomial (dyadicPrimes P) (onePlusIT t)‖) →
        (∀ t ∈ E,
          M1 ^ (-sigma1) ≤
            ‖dyadicDirichletPolynomial (fun n ↦ (b n : ℂ)) M1
              (onePlusIT t)‖) →
        (∀ t ∈ E,
          M2 ^ (-sigma2) ≤
            ‖dyadicDirichletPolynomial beta M2 (onePlusIT t)‖) →
        Real.log M1 / Real.log X = theta →
        1 - scaleError ≤ Real.log M / Real.log X →
        0 ≤ theta → theta ≤ 1 →
        residualError = firstError + scaleError * (1 - 1 / a) →
        (1 - 1 / a - residualError ≤ theta * (1 - 2 * sigma1) →
          1 / a + keyError < secondBranchKeyExponent theta sigma1 sigma2) →
        M = X ^ mu → M1 = X ^ theta → M2 = X ^ phi →
        ((primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
          M ^ (1 - 1 / a + epsilon ^ 2 / 100) →
        ((primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
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
                (dyadicRealCoefficientSup (fun n ↦ (beta n).re) M2) ^
                  (2 : ℕ) +
              CIm *
                (dyadicRealCoefficientSup (fun n ↦ (beta n).im) M2) ^
                  (2 : ℕ)) ≤
            X ^ (epsilon ^ 2 / 100) →
        (volume.real E ≤
            2 * sparsePropagationScaleTarget M1 M2 sigma1 sigma2 *
              X ^ (-epsilon ^ 2) ∨
          volume.real E ≤
            secondBranchPowerConstant C D A0 epsilon *
              sparsePropagationScaleTarget M1 M2 sigma1 sigma2 *
              X ^ (-3 * epsilon)) := by
  have hepsilonSq : 0 < epsilon ^ 2 / 100 := by positivity
  have hepsilonLinear : 0 < epsilon / 100 := by positivity
  obtain ⟨CRe, CIm, hCRe, hCIm, hfirstUniform⟩ :=
    measure_set_le_firstBranchRaw_complex_uniform
      inputs.matomakiTeravainenLemmaThreeFour hepsilonSq
  obtain ⟨C, hC, hsecondC⟩ :=
    secondBranch_fifthPower_largeValueMeasure inputs
      hepsilonLinear hepsilonLinear
  obtain ⟨D, hD, hsecondUniform⟩ := hsecondC B hB
  refine ⟨CRe, CIm, C, D, hCRe, hCIm, hC, hD, ?_, ?_⟩
  · exact eventually_sparseFirstCoefficientLoss_uniform_of_coordinate
      hepsilon hB hA hCRe.le hCIm.le
  intro X P M M1 M2 A0 a theta phi mu sigma1 sigma2 scaleError
    firstError residualError keyError k beta b E
    hX hPdef ha hk hden hMdef hM hMX hM1 hM2 hM1lower
    hsigmaStrong hsupport hcard hb hblocks hEmeas hEsub hU
    hM1lowerOnE hM2lowerOnE htheta hMExponent htheta0 htheta1
    hresidualError hkey hMcoord hM1coord hM2coord
    hRboundFirst hRboundSecond haLower haUpper hmuLower hmuUpper
    hthetaLower hthetaUpper hphiUpper hproductLoss hfirstTransfer
    hsecondTransfer hcoefficientLoss
  have hPpos : 0 < P := by
    rw [hPdef]
    exact Real.rpow_pos_of_pos (Real.log_pos hX) a
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hM2pos : 0 < M2 := lt_of_lt_of_le (by norm_num) hM2
  have hSprime : ∀ p ∈ dyadicPrimes P, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hQlower : ∀ t ∈ E,
      M ^ (-epsilon / 10 - 1 / a) ≤
        ‖primePowerPolynomial (dyadicPrimes P) k (onePlusIT t)‖ := by
    intro t ht
    have hfloor := paper_Q_lower_bound_for_floor_choice
      (z := primeBasePolynomial (dyadicPrimes P) (onePlusIT t))
      hX (by linarith : 0 < a) hPdef hden
      (by simpa [hk] using hMdef) (hU t ht)
    simpa [primePowerPolynomial, factorialNormalizedPower, hk] using hfloor
  have hdeleteFirst :
      M2 ≥ X ^ (2 / 3 : ℝ) ∨
        ((primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
          X ^ (1 / 3 : ℝ) := Or.inr hcard
  have hfirstBound := hfirstUniform hM hMX hM2
    (Real.rpow_pos_of_pos hMpos _) (Real.rpow_pos_of_pos hM2pos _)
    hSprime hsupport hdeleteFirst hEmeas hEsub hQlower hM2lowerOnE
  have hfirstRaw :
      volume.real E ≤
        firstBranchComplexMajorant CRe CIm
          ((primePowerSupport (dyadicPrimes P) k).card : ℝ)
          M M2 X (epsilon ^ 2 / 100)
          (dyadicRealCoefficientSup (fun n ↦ (beta n).re) M2)
          (dyadicRealCoefficientSup (fun n ↦ (beta n).im) M2)
          (M ^ (-epsilon / 10 - 1 / a))
          (M2 ^ (-sigma2)) := by
    simpa [firstBranchComplexMajorant] using hfirstBound
  have hcoeff : ∀ m ∈ primePowerSupport (dyadicPrimes P) k,
      ‖(primePowerCoefficient (dyadicPrimes P) k m : ℂ)‖ ≤ 1 := by
    intro m hm
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (primePowerCoefficient_nonneg _ _ _)]
    exact primePowerCoefficient_le_one hSprime
  have hbaseSupport : ∀ n ∈ dyadicInterval M1, InDyadicRange M1 n := by
    intro n hn
    exact (mem_dyadicInterval hM1.le).mp hn
  have hdeleteSecond : ∀ j ∈ Finset.range 5,
      (2 : ℝ) ^ j * M1 ^ (5 : ℕ) ≥ X ^ (2 / 3 : ℝ) ∨
        ((primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
          X ^ (1 / 3 : ℝ) := by
    intro j hj
    exact Or.inr hcard
  have hQpoly (t : ℝ) :
      dirichletPolynomial
          (fun n ↦ (primePowerCoefficient (dyadicPrimes P) k n : ℂ))
          (primePowerSupport (dyadicPrimes P) k) (onePlusIT t) =
        primePowerPolynomial (dyadicPrimes P) k (onePlusIT t) := by
    symm
    exact primePowerPolynomial_eq_supportSum _ _ _
  have hsecondLower : ∀ t ∈ E,
      (M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) *
          ((M1 ^ (-sigma1)) ^ (5 : ℕ)) ^ (2 : ℕ) ≤
        ‖dirichletPolynomial
            (fun n ↦ (primePowerCoefficient (dyadicPrimes P) k n : ℂ))
            (primePowerSupport (dyadicPrimes P) k) (onePlusIT t)‖ ^
              (2 : ℕ) *
          ‖dirichletPolynomial (fun n ↦ (b n : ℂ))
              (dyadicInterval M1) (onePlusIT t) ^ (5 : ℕ)‖ ^
            (2 : ℕ) := by
    intro t ht
    apply fifthPower_integrand_lower
      (Real.rpow_nonneg hMpos.le _) (Real.rpow_nonneg hM1.le _)
    · rw [hQpoly]
      exact hQlower t ht
    · exact hM1lowerOnE t ht
  have hsecondBound := hsecondUniform X M M1 A0
    (primePowerSupport (dyadicPrimes P) k) (dyadicInterval M1)
    (fun n ↦ (primePowerCoefficient (dyadicPrimes P) k n : ℂ)) b E
    ((M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) *
      ((M1 ^ (-sigma1)) ^ (5 : ℕ)) ^ (2 : ℕ))
    hM1 hb hbaseSupport hM hMX hsupport hcoeff hblocks hdeleteSecond
    hEmeas hEsub (by positivity) hsecondLower
  have hsecondRaw :
      volume.real E *
          ((M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) *
            ((M1 ^ (-sigma1)) ^ (5 : ℕ)) ^ (2 : ℕ)) ≤
        secondBranchFiveBlockMajorant C D (epsilon / 100)
          (epsilon / 100) X M M1 A0
            ((primePowerSupport (dyadicPrimes P) k).card : ℝ) := by
    simpa [secondBranchFiveBlockMajorant] using hsecondBound
  have hdichotomy := firstOrSecondBranch_exactPowerDichotomy_of_key
    hX hMpos hM1 ha htheta hMExponent hresidualError hkey
  exact sparseBranchMajorants_measure_powerSaving
    hCRe hCIm hC hX hMpos hM1 (by linarith : 0 < M2)
    (Nat.cast_nonneg _) hMcoord hM1coord hM2coord
    hRboundFirst hRboundSecond hepsilon hepsilonUpper
    (lt_trans zero_lt_one ha) haLower haUpper hmuLower hmuUpper
    hthetaLower htheta0 hthetaUpper hphiUpper hsigmaStrong hproductLoss
    hfirstRaw hsecondRaw hdichotomy hfirstTransfer hsecondTransfer
    hcoefficientLoss

def propagationParametersModule : ProofModule :=
  { name := "Sparse.PropagationParameters"
    paperLocation := "Section 6.1, moving-coordinate error budget"
    purpose :=
      "Discharge both fixed-to-moving coordinate implications and the eventual complex coefficient loss, and assemble both sparse branches with all analytic constants selected uniformly before the moving height, scales, coefficients, and large-value set."
    dependsOn := ["Sparse.PropagationMoving", "Hybrid.HybridDensity"]
    status := .proved }

end
end Sparse
end ExactSemiprimes
