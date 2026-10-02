import ExactSemiprimes.Sparse.Propagation

/-! # Fixed-to-moving closure of the sparse propagation estimate

This module is a leaf above `Sparse.Propagation`.  It performs no new
analytic estimate.  Its first theorem combines the two literal branch
majorants with their proved power budgets.  Its second theorem obtains the
raw branch bounds from `sparsePropagation_fixedScale_package` (at the two
different small exponents needed by the two branches).  The final theorem
turns either fixed power saving into the logarithmic-exponential saving used
in the paper.

The coefficient loss in the complex first branch and the two implications
which translate the package's power dichotomy into the exponent hypotheses
of the branch budgets are deliberately left explicit.  They are moving-scale
parameter facts, not consequences of the fixed-scale analytic package.
-/

namespace ExactSemiprimes
namespace Sparse

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section

/-- The common scale factor which occurs in both sparse branches. -/
def sparsePropagationScaleTarget
    (M1 M2 sigma1 sigma2 : ℝ) : ℝ :=
  M1 ^ (2 * sigma1) * M2 ^ (2 * sigma2)

/-- The fixed coefficient left by the five-block second branch. -/
def secondBranchPowerConstant
    (C D A0 epsilon : ℝ) : ℝ :=
  25 * C *
    (((A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) *
          (32 : ℝ) ^ (epsilon / 50)) +
      (16 : ℝ) ^ (epsilon / 100) *
        ((A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) *
          (32 : ℝ) ^ (epsilon / 50)))

/-- Logarithmic coordinates convert the model target into the literal
product of the two Dirichlet-polynomial scales. -/
theorem coordinateTarget_eq_sparsePropagationScaleTarget
    {X M1 M2 theta phi sigma1 sigma2 : ℝ}
    (hX : 0 < X) (hM1 : M1 = X ^ theta) (hM2 : M2 = X ^ phi) :
    X ^ (2 * sigma1 * theta) * X ^ (2 * sigma2 * phi) =
      sparsePropagationScaleTarget M1 M2 sigma1 sigma2 := by
  rw [hM1, hM2]
  unfold sparsePropagationScaleTarget
  rw [← Real.rpow_mul hX.le, ← Real.rpow_mul hX.le]
  congr 2 <;> ring

/-- Algebraic leaf of sparse propagation.

Given the two raw measure bounds and the package's exact power dichotomy,
the already-proved branch budgets yield one of two genuine power-saving
measure estimates.  The first-branch coefficient loss is an explicit
hypothesis because its eventual absorption is a separate moving-parameter
statement. -/
theorem sparseBranchMajorants_measure_powerSaving
    {CRe CIm C D R M M1 M2 X ARe AIm A0 a epsilon mu theta phi
      sigma1 sigma2 firstError keyError : ℝ}
    {E : Set ℝ}
    (hCRe : 0 < CRe) (hCIm : 0 < CIm) (hC : 0 < C)
    (hX : 1 < X) (hM : 0 < M) (hM1 : 0 < M1) (hM2 : 0 < M2)
    (hR : 0 ≤ R)
    (hMcoord : M = X ^ mu) (hM1coord : M1 = X ^ theta)
    (hM2coord : M2 = X ^ phi)
    (hRboundFirst :
      R ≤ M ^ (1 - 1 / a + epsilon ^ 2 / 100))
    (hRboundSecond : R ≤ M ^ (1 - 1 / a + epsilon / 100))
    (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1 / 10)
    (ha : 0 < a) (haLower : 12 / 11 ≤ a) (haUpper : a ≤ 11 / 10)
    (hmuLower : 1 - epsilon / 100 ≤ mu) (hmuUpper : mu ≤ 1)
    (hthetaLower : epsilon / 2 ≤ theta)
    (htheta0 : 0 ≤ theta) (hthetaUpper : theta ≤ 2 / 11)
    (hphiUpper : phi ≤ 1)
    (hsigmaStrong : 1 / 5 + 2 * epsilon ≤ sigma1)
    (hproductLoss : 1 - theta - phi ≤ epsilon ^ 2 / 100)
    (hfirstRaw :
      volume.real E ≤
        firstBranchComplexMajorant CRe CIm R M M2 X
          (epsilon ^ 2 / 100) ARe AIm
          (M ^ (-epsilon / 10 - 1 / a)) (M2 ^ (-sigma2)))
    (hsecondRaw :
      volume.real E *
          ((M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) *
            ((M1 ^ (-sigma1)) ^ (5 : ℕ)) ^ (2 : ℕ)) ≤
        secondBranchFiveBlockMajorant C D (epsilon / 100)
          (epsilon / 100) X M M1 A0 R)
    (hdichotomy :
      M1 ^ (1 - 2 * sigma1) ≤
          X ^ (-firstError) * M ^ (1 - 1 / a) ∨
        X ^ (1 / a + keyError) ≤
          (X ^ theta) ^ (5 - 8 * sigma1) *
            (X ^ (1 - theta)) ^ (2 * sigma2))
    (hfirstTransfer :
      M1 ^ (1 - 2 * sigma1) ≤
          X ^ (-firstError) * M ^ (1 - 1 / a) →
        theta * (1 - 2 * sigma1) ≤
          -epsilon / 3 + mu * (1 - 1 / a))
    (hsecondTransfer :
      X ^ (1 / a + keyError) ≤
          (X ^ theta) ^ (5 - 8 * sigma1) *
            (X ^ (1 - theta)) ^ (2 * sigma2) →
        1 / a + 4 * epsilon ≤
          (5 - 8 * sigma1) * theta + 2 * sigma2 * phi)
    (hcoefficientLoss :
      4 * (CRe * ARe ^ (2 : ℕ) + CIm * AIm ^ (2 : ℕ)) ≤
        X ^ (epsilon ^ 2 / 100)) :
    volume.real E ≤
        2 * sparsePropagationScaleTarget M1 M2 sigma1 sigma2 *
          X ^ (-epsilon ^ 2) ∨
      volume.real E ≤
        secondBranchPowerConstant C D A0 epsilon *
          sparsePropagationScaleTarget M1 M2 sigma1 sigma2 *
          X ^ (-3 * epsilon) := by
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hcoordinate := coordinateTarget_eq_sparsePropagationScaleTarget
    (sigma1 := sigma1) (sigma2 := sigma2)
    hXpos hM1coord hM2coord
  rcases hdichotomy with hfirstPower | hsecondPower
  · left
    have hfirstExponent := hfirstTransfer hfirstPower
    have hcoefficientNonneg :
        0 ≤ 4 * (CRe * ARe ^ (2 : ℕ) +
          CIm * AIm ^ (2 : ℕ)) := by positivity
    have hmajorant := firstBranchComplexMajorant_fixedPowerSaving
      (sigma2 := sigma2)
      hX hM hM2 hR hMcoord hM2coord hcoefficientNonneg
      hcoefficientLoss hRboundFirst hepsilon hepsilonUpper hmuUpper
      hthetaLower hphiUpper hsigmaStrong hproductLoss hfirstExponent
    calc
      volume.real E ≤
          firstBranchComplexMajorant CRe CIm R M M2 X
            (epsilon ^ 2 / 100) ARe AIm
            (M ^ (-epsilon / 10 - 1 / a)) (M2 ^ (-sigma2)) :=
        hfirstRaw
      _ ≤ 2 *
            (X ^ (2 * sigma1 * theta) * X ^ (2 * sigma2 * phi)) *
            X ^ (-epsilon ^ 2) := hmajorant
      _ = 2 * sparsePropagationScaleTarget M1 M2 sigma1 sigma2 *
            X ^ (-epsilon ^ 2) := by rw [hcoordinate]
  · right
    have hkey := hsecondTransfer hsecondPower
    have hdenominator : 0 <
        (M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) *
          ((M1 ^ (-sigma1)) ^ (5 : ℕ)) ^ (2 : ℕ) := by
      positivity
    have hnormalized :
        volume.real E ≤
          secondBranchFiveBlockMajorant C D (epsilon / 100)
              (epsilon / 100) X M M1 A0 R /
            ((M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) *
              ((M1 ^ (-sigma1)) ^ (5 : ℕ)) ^ (2 : ℕ)) :=
      (le_div_iff₀ hdenominator).2 hsecondRaw
    have hmajorant :=
      normalizedSecondBranchFiveBlockMajorant_fixedPowerSaving_model
        (D := D) (A0 := A0)
        hC.le hX hM hM1 hM2 hR hRboundSecond hepsilon hepsilonUpper
        ha haLower haUpper hMcoord hM1coord hM2coord hmuLower hmuUpper
        htheta0 hthetaUpper hkey
    calc
      volume.real E ≤
          secondBranchFiveBlockMajorant C D (epsilon / 100)
              (epsilon / 100) X M M1 A0 R /
            ((M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) *
              ((M1 ^ (-sigma1)) ^ (5 : ℕ)) ^ (2 : ℕ)) :=
        hnormalized
      _ ≤ 25 * C *
          (((A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) *
                (32 : ℝ) ^ (epsilon / 50)) +
            (16 : ℝ) ^ (epsilon / 100) *
              ((A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) *
                (32 : ℝ) ^ (epsilon / 50))) *
          (M1 ^ (2 * sigma1) * M2 ^ (2 * sigma2)) *
          X ^ (-3 * epsilon) := hmajorant
      _ = secondBranchPowerConstant C D A0 epsilon *
            sparsePropagationScaleTarget M1 M2 sigma1 sigma2 *
            X ^ (-3 * epsilon) := by
        unfold secondBranchPowerConstant sparsePropagationScaleTarget
        ring

/-- Complete fixed-scale wrapper.

The existing analytic package is invoked twice because the optimized first
branch uses `eta = epsilon^2/100`, whereas the five-block branch uses
`eta = rho = epsilon/100`.  The returned implication is the exact remaining
coefficient-subpower obligation for the witnesses supplied by the cited
first-branch theorem. -/
theorem sparsePropagation_fixedScale_powerSaving_package
    (inputs : ExternalInputs)
    {X P M M1 M2 A0 B epsilon a theta phi mu sigma1 sigma2
      scaleError firstError residualError keyError : ℝ}
    {k : ℕ} {beta : ℕ → ℂ} {b : ℕ → ℝ} {E : Set ℝ}
    (hX : 1 < X) (hPdef : P = (Real.log X) ^ a)
    (ha : 1 < a)
    (hk : k = ⌊Real.log X / Real.log (2 * P)⌋₊)
    (hden : 1 ≤ Real.log (2 * P))
    (hMdef : M = P ^ k)
    (hM : 1 ≤ M) (hMX : M ≤ X)
    (hM1 : 0 < M1) (hM2 : 2 ≤ M2)
    (hM1lower : X ^ (epsilon / 2) ≤ M1)
    (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1 / 10)
    (hsigmaStrong : 1 / 5 + 2 * epsilon ≤ sigma1)
    (hsupport : ∀ m ∈ primePowerSupport (dyadicPrimes P) k,
      M ≤ (m : ℝ) ∧ (m : ℝ) ≤ X)
    (hcard :
      ((primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
        X ^ (1 / 3 : ℝ))
    (hb : IsDivisorBoundedByConstant B A0 (fun n ↦ (b n : ℂ)))
    (hblocks : ∀ j ∈ Finset.range 5,
      2 ≤ (2 : ℝ) ^ j * M1 ^ (5 : ℕ))
    (hEmeas : MeasurableSet E) (hEsub : E ⊆ Set.Icc (-X) X)
    (hU : ∀ t ∈ E,
      P ^ (-epsilon / 10) ≤
        ‖primeBasePolynomial (dyadicPrimes P) (onePlusIT t)‖)
    (hM1lowerOnE : ∀ t ∈ E,
      M1 ^ (-sigma1) ≤
        ‖dyadicDirichletPolynomial (fun n ↦ (b n : ℂ)) M1
          (onePlusIT t)‖)
    (hM2lowerOnE : ∀ t ∈ E,
      M2 ^ (-sigma2) ≤
        ‖dyadicDirichletPolynomial beta M2 (onePlusIT t)‖)
    (htheta : Real.log M1 / Real.log X = theta)
    (hMExponent : 1 - scaleError ≤ Real.log M / Real.log X)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hresidualError :
      residualError = firstError + scaleError * (1 - 1 / a))
    (hkey : 1 - 1 / a - residualError ≤ theta * (1 - 2 * sigma1) →
      1 / a + keyError < secondBranchKeyExponent theta sigma1 sigma2)
    (hMcoord : M = X ^ mu) (hM1coord : M1 = X ^ theta)
    (hM2coord : M2 = X ^ phi)
    (hRboundFirst :
      ((primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
        M ^ (1 - 1 / a + epsilon ^ 2 / 100))
    (hRboundSecond :
      ((primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
        M ^ (1 - 1 / a + epsilon / 100))
    (haLower : 12 / 11 ≤ a) (haUpper : a ≤ 11 / 10)
    (hmuLower : 1 - epsilon / 100 ≤ mu) (hmuUpper : mu ≤ 1)
    (hthetaLower : epsilon / 2 ≤ theta)
    (hthetaUpper : theta ≤ 2 / 11)
    (hphiUpper : phi ≤ 1)
    (hproductLoss : 1 - theta - phi ≤ epsilon ^ 2 / 100)
    (hfirstTransfer :
      M1 ^ (1 - 2 * sigma1) ≤
          X ^ (-firstError) * M ^ (1 - 1 / a) →
        theta * (1 - 2 * sigma1) ≤
          -epsilon / 3 + mu * (1 - 1 / a))
    (hsecondTransfer :
      X ^ (1 / a + keyError) ≤
          (X ^ theta) ^ (5 - 8 * sigma1) *
            (X ^ (1 - theta)) ^ (2 * sigma2) →
        1 / a + 4 * epsilon ≤
          (5 - 8 * sigma1) * theta + 2 * sigma2 * phi) :
    ∃ CRe CIm C D : ℝ,
      0 < CRe ∧ 0 < CIm ∧ 0 < C ∧ 1 ≤ D ∧
      (4 * (CRe *
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
              X ^ (-3 * epsilon))) := by
  have hepsilonSq : 0 < epsilon ^ 2 / 100 := by positivity
  have hepsilonLinear : 0 < epsilon / 100 := by positivity
  have hfirstPackage := sparsePropagation_fixedScale_package
    inputs hepsilonSq hepsilonLinear hX hPdef ha hk hden hMdef hM hMX
    hM1 hM2 hM1lower hepsilon.le hsigmaStrong hsupport hcard hb hblocks
    hEmeas hEsub hU hM1lowerOnE hM2lowerOnE htheta hMExponent htheta0
    htheta1 hresidualError hkey
  have hsecondPackage := sparsePropagation_fixedScale_package
    inputs hepsilonLinear hepsilonLinear hX hPdef ha hk hden hMdef hM hMX
    hM1 hM2 hM1lower hepsilon.le hsigmaStrong hsupport hcard hb hblocks
    hEmeas hEsub hU hM1lowerOnE hM2lowerOnE htheta hMExponent htheta0
    htheta1 hresidualError hkey
  rcases hfirstPackage with
    ⟨⟨CRe, CIm, hCRe, hCIm, hfirstRaw⟩, _, _, hdichotomy⟩
  rcases hsecondPackage with
    ⟨_, ⟨C, D, hC, hD, hsecondRaw⟩, _, _⟩
  refine ⟨CRe, CIm, C, D, hCRe, hCIm, hC, hD, ?_⟩
  intro hcoefficientLoss
  exact sparseBranchMajorants_measure_powerSaving
    hCRe hCIm hC hX (zero_lt_one.trans_le hM) hM1
    (by linarith : 0 < M2) (Nat.cast_nonneg _) hMcoord hM1coord hM2coord
    hRboundFirst hRboundSecond hepsilon hepsilonUpper
    (lt_trans zero_lt_one ha) haLower haUpper hmuLower hmuUpper
    hthetaLower htheta0 hthetaUpper hphiUpper hsigmaStrong hproductLoss
    hfirstRaw hsecondRaw hdichotomy hfirstTransfer hsecondTransfer
    hcoefficientLoss

/-- Either branch's fixed power saving eventually dominates the exact
`exp (-(log log X)^7)` factor.  The constants may differ between the two
branches, but must be fixed before the moving parameter `X` tends to infinity.
-/
theorem eventually_sparsePowerSavingDisjunction_le_loglog
    {K1 K2 epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℝ in atTop, ∀ value target : ℝ,
      0 ≤ target →
      (value ≤ K1 * target * X ^ (-epsilon ^ 2) ∨
        value ≤ K2 * target * X ^ (-3 * epsilon)) →
      value ≤ target *
        Real.exp (-(Real.log (Real.log X)) ^ (7 : ℕ)) := by
  have hquadratic : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  have hlinear : 0 < 3 * epsilon := mul_pos (by norm_num) hepsilon
  have hfirst := eventually_majorant_le_target_mul_exp_of_powerSaving
    (K := K1) hquadratic
  have hsecond := eventually_majorant_le_target_mul_exp_of_powerSaving
    (K := K2) hlinear
  filter_upwards [hfirst, hsecond] with X hfirstX hsecondX
  intro value target htarget hbranches
  rcases hbranches with hbranch | hbranch
  · exact hfirstX value target htarget hbranch
  · apply hsecondX value target htarget
    simpa only [show -(3 * epsilon) = -3 * epsilon by ring] using hbranch

def propagationMovingModule : ProofModule :=
  { name := "Sparse.PropagationMoving"
    paperLocation := "Section 6.1, fixed-to-moving sparse propagation"
    purpose :=
      "Combine the fixed-scale sparse analytic package with both literal branch power budgets, preserve the first-branch coefficient loss and coordinate transfers as explicit obligations, and convert either fixed power saving to the paper's logarithmic-exponential saving."
    dependsOn := ["Sparse.Propagation"]
    status := .proved }

end

end Sparse
end ExactSemiprimes
