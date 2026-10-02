import ExactSemiprimes.Completion.ParameterizedReduction
import ExactSemiprimes.Completion.DyadicPrimeBlocks
import ExactSemiprimes.TypeII.PolynomialLengthRanges

/-! # Summing the variance estimate across prime blocks -/

namespace ExactSemiprimes
namespace Completion

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

/-- Finite Cauchy--Schwarz in the exact form used when summing the variance
over dyadic prime blocks. -/
theorem norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*}
    (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have hnorm : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le s f
  have hsq : ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
    nlinarith [norm_nonneg (∑ i ∈ s, f i),
      Finset.sum_nonneg (s := s) (fun i _ ↦ norm_nonneg (f i))]
  exact hsq.trans (sq_sum_le_card_mul_sum_sq (s := s) (f := fun i ↦ ‖f i‖))

/-- If every block has squared size at most `V`, summing `r` blocks costs at
most `r²`.  This is the exact finite loss which is later absorbed by the
reserved logarithmic saving. -/
theorem norm_sum_sq_le_card_sq_mul {ι : Type*}
    (s : Finset ι) (f : ι → ℂ) {V : ℝ} (_hV : 0 ≤ V)
    (hf : ∀ i ∈ s, ‖f i‖ ^ 2 ≤ V) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) ^ 2 * V := by
  calc
    ‖∑ i ∈ s, f i‖ ^ 2
        ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 :=
      norm_sum_sq_le_card_mul_sum_norm_sq s f
    _ ≤ (s.card : ℝ) * ∑ _i ∈ s, V := by
      gcongr with i hi
      exact hf i hi
    _ = (s.card : ℝ) ^ 2 * V := by
      simp [pow_two]
      ring

/-- Version with an external real upper bound for the number of blocks. -/
theorem norm_sum_sq_le_blockBound_sq_mul {ι : Type*}
    (s : Finset ι) (f : ι → ℂ) {R V : ℝ}
    (hR : (s.card : ℝ) ≤ R) (hV : 0 ≤ V)
    (hf : ∀ i ∈ s, ‖f i‖ ^ 2 ≤ V) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ R ^ 2 * V := by
  have hR0 : 0 ≤ R := (Nat.cast_nonneg s.card).trans hR
  calc
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) ^ 2 * V :=
      norm_sum_sq_le_card_sq_mul s f hV hf
    _ ≤ R ^ 2 * V := by
      gcongr

/-- Pointwise logarithmic absorption.  If the square of the number of
blocks is at most `L^η`, then a bound `X/L^(2+ε)` remains
`X/L^(2+ε-η)` after Cauchy--Schwarz. -/
theorem absorb_block_square_into_logSaving {X L ε η R : ℝ}
    (hX : 0 ≤ X) (hL : 0 < L) (_hR : 0 ≤ R)
    (hblocks : R ^ 2 ≤ L ^ η) :
    R ^ 2 * (X / L ^ (2 + ε)) ≤ X / L ^ (2 + ε - η) := by
  have hLpow : 0 < L ^ (2 + ε) := Real.rpow_pos_of_pos hL _
  calc
    R ^ 2 * (X / L ^ (2 + ε))
        ≤ L ^ η * (X / L ^ (2 + ε)) :=
      mul_le_mul_of_nonneg_right hblocks (div_nonneg hX hLpow.le)
    _ = X / L ^ (2 + ε - η) := by
      have hLeta : L ^ η ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hL η)
      rw [Real.rpow_sub hL]
      field_simp [hLeta, ne_of_gt hLpow]

/-!
## Integrated block errors

For disjoint prime blocks, the error belonging to their union is the sum of
the individual block errors.  The following statements formalize exactly the
finite bookkeeping used in Section 7.2.  Integrability is kept explicit; in
the paper it follows from the finite Dirichlet-polynomial expressions, and no
analytic estimate is hidden here.
-/

/-- The error obtained by summing a finite family of block errors. -/
def summedBlockError {α ι : Type*} (s : Finset ι)
    (error : ι → α → ℂ) (x : α) : ℂ :=
  ∑ i ∈ s, error i x

/-- Integrated finite Cauchy--Schwarz.  This is the sharper `r` loss times
the sum of the individual integrated square errors. -/
theorem integral_summedBlockError_sq_le_card_mul_sum_integral
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) (s : Finset ι)
    (error : ι → α → ℂ)
    (hE : MeasurableSet E)
    (htotal : IntegrableOn
      (fun x ↦ ‖summedBlockError s error x‖ ^ 2) E μ)
    (hblock : ∀ i ∈ s,
      IntegrableOn (fun x ↦ ‖error i x‖ ^ 2) E μ) :
    (∫ x in E, ‖summedBlockError s error x‖ ^ 2 ∂μ) ≤
      (s.card : ℝ) *
        ∑ i ∈ s, ∫ x in E, ‖error i x‖ ^ 2 ∂μ := by
  have hsum : IntegrableOn
      (fun x ↦ ∑ i ∈ s, ‖error i x‖ ^ 2) E μ := by
    rw [IntegrableOn]
    exact (integrable_finsetSum' s hblock).congr
      (Filter.Eventually.of_forall fun x ↦ by simp)
  have hright : IntegrableOn
      (fun x ↦ (s.card : ℝ) * ∑ i ∈ s, ‖error i x‖ ^ 2) E μ :=
    hsum.integrable.const_mul (s.card : ℝ)
  calc
    (∫ x in E, ‖summedBlockError s error x‖ ^ 2 ∂μ) ≤
        ∫ x in E,
          (s.card : ℝ) * ∑ i ∈ s, ‖error i x‖ ^ 2 ∂μ := by
      exact setIntegral_mono_on htotal hright hE fun x _ ↦ by
        simpa [summedBlockError] using
          norm_sum_sq_le_card_mul_sum_norm_sq s (fun i ↦ error i x)
    _ = (s.card : ℝ) *
          ∑ i ∈ s, ∫ x in E, ‖error i x‖ ^ 2 ∂μ := by
      rw [integral_const_mul, integral_finsetSum s hblock]

/-- If the sum of the individual block variances is at most `Vsum`, the
summed error costs only the sharp factor `r`. -/
theorem integral_summedBlockError_sq_le_card_mul_totalBound
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) (s : Finset ι)
    (error : ι → α → ℂ) {Vsum : ℝ}
    (hE : MeasurableSet E)
    (htotal : IntegrableOn
      (fun x ↦ ‖summedBlockError s error x‖ ^ 2) E μ)
    (hblock : ∀ i ∈ s,
      IntegrableOn (fun x ↦ ‖error i x‖ ^ 2) E μ)
    (_hVsum : 0 ≤ Vsum)
    (hsumBound :
      (∑ i ∈ s, ∫ x in E, ‖error i x‖ ^ 2 ∂μ) ≤ Vsum) :
    (∫ x in E, ‖summedBlockError s error x‖ ^ 2 ∂μ) ≤
      (s.card : ℝ) * Vsum := by
  calc
    _ ≤ (s.card : ℝ) *
        ∑ i ∈ s, ∫ x in E, ‖error i x‖ ^ 2 ∂μ :=
      integral_summedBlockError_sq_le_card_mul_sum_integral
        μ E s error hE htotal hblock
    _ ≤ (s.card : ℝ) * Vsum :=
      mul_le_mul_of_nonneg_left hsumBound (Nat.cast_nonneg s.card)

/-- If every one of the `r` blocks has variance at most `V`, finite
Cauchy--Schwarz gives the advertised `r² V` bound. -/
theorem integral_summedBlockError_sq_le_card_sq_mul
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) (s : Finset ι)
    (error : ι → α → ℂ) {V : ℝ}
    (hE : MeasurableSet E)
    (htotal : IntegrableOn
      (fun x ↦ ‖summedBlockError s error x‖ ^ 2) E μ)
    (hblock : ∀ i ∈ s,
      IntegrableOn (fun x ↦ ‖error i x‖ ^ 2) E μ)
    (_hV : 0 ≤ V)
    (heach : ∀ i ∈ s,
      (∫ x in E, ‖error i x‖ ^ 2 ∂μ) ≤ V) :
    (∫ x in E, ‖summedBlockError s error x‖ ^ 2 ∂μ) ≤
      (s.card : ℝ) ^ 2 * V := by
  calc
    _ ≤ (s.card : ℝ) *
        ∑ i ∈ s, ∫ x in E, ‖error i x‖ ^ 2 ∂μ :=
      integral_summedBlockError_sq_le_card_mul_sum_integral
        μ E s error hE htotal hblock
    _ ≤ (s.card : ℝ) * ∑ _i ∈ s, V := by
      gcongr with i hi
      exact heach i hi
    _ = (s.card : ℝ) ^ 2 * V := by
      simp [pow_two]
      ring

/-- Version of the integrated `r²` estimate with a real upper bound `R` for
the number of prime blocks. -/
theorem integral_summedBlockError_sq_le_blockBound_sq_mul
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) (s : Finset ι)
    (error : ι → α → ℂ) {R V : ℝ}
    (hE : MeasurableSet E)
    (htotal : IntegrableOn
      (fun x ↦ ‖summedBlockError s error x‖ ^ 2) E μ)
    (hblock : ∀ i ∈ s,
      IntegrableOn (fun x ↦ ‖error i x‖ ^ 2) E μ)
    (hR : (s.card : ℝ) ≤ R) (hV : 0 ≤ V)
    (heach : ∀ i ∈ s,
      (∫ x in E, ‖error i x‖ ^ 2 ∂μ) ≤ V) :
    (∫ x in E, ‖summedBlockError s error x‖ ^ 2 ∂μ) ≤
      R ^ 2 * V := by
  have hR0 : 0 ≤ R := (Nat.cast_nonneg s.card).trans hR
  calc
    _ ≤ (s.card : ℝ) ^ 2 * V :=
      integral_summedBlockError_sq_le_card_sq_mul
        μ E s error hE htotal hblock hV heach
    _ ≤ R ^ 2 * V := by gcongr

/-- Normalized form of the blockwise statement.  It applies directly when
`scale = X` and the measure is Lebesgue measure on `[X,2X]`. -/
theorem normalized_integral_summedBlockError_sq_le_card_sq_mul
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) (s : Finset ι)
    (error : ι → α → ℂ) {scale V : ℝ}
    (hscale : 0 < scale) (hV : 0 ≤ V)
    (hE : MeasurableSet E)
    (htotal : IntegrableOn
      (fun x ↦ ‖summedBlockError s error x‖ ^ 2) E μ)
    (hblock : ∀ i ∈ s,
      IntegrableOn (fun x ↦ ‖error i x‖ ^ 2) E μ)
    (heach : ∀ i ∈ s,
      (∫ x in E, ‖error i x‖ ^ 2 ∂μ) / scale ≤ V) :
    (∫ x in E, ‖summedBlockError s error x‖ ^ 2 ∂μ) / scale ≤
      (s.card : ℝ) ^ 2 * V := by
  have heach' : ∀ i ∈ s,
      (∫ x in E, ‖error i x‖ ^ 2 ∂μ) ≤ scale * V := by
    intro i hi
    have h := (div_le_iff₀ hscale).mp (heach i hi)
    nlinarith
  have hraw := integral_summedBlockError_sq_le_card_sq_mul
    μ E s error hE htotal hblock (mul_nonneg hscale.le hV) heach'
  apply (div_le_iff₀ hscale).2
  calc
    (∫ x in E, ‖summedBlockError s error x‖ ^ 2 ∂μ) ≤
        (s.card : ℝ) ^ 2 * (scale * V) := hraw
    _ = ((s.card : ℝ) ^ 2 * V) * scale := by ring

/-!
## Absorbing `O(log log X)` blocks

The next lemma supplies the precise elementary fact used in the paper:
the square of a fixed multiple of `log log X` is eventually smaller than
any prescribed positive power of `log X`.
-/

theorem eventually_const_mul_log_log_sq_le_log_rpow
    (A : ℝ) (_hA : 0 ≤ A) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop,
      (A * Real.log (Real.log X)) ^ 2 ≤ (Real.log X) ^ η := by
  have hhalf : 0 < η / 2 := by positivity
  have hlogPartAtTop :
      ∀ᶠ Y : ℝ in atTop, (Real.log Y) ^ (2 : ℝ) ≤ Y ^ (η / 2) :=
    TypeII.eventually_log_rpow_le_rpow 2 hhalf
  have hconstPartAtTop :
      ∀ᶠ Y : ℝ in atTop, A ^ 2 ≤ Y ^ (η / 2) :=
    (tendsto_rpow_atTop hhalf).eventually_ge_atTop (A ^ 2)
  have hlogPart := Real.tendsto_log_atTop.eventually hlogPartAtTop
  have hconstPart := Real.tendsto_log_atTop.eventually hconstPartAtTop
  filter_upwards [hlogPart, hconstPart,
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with
      X hlogPartX hconstPartX hlogXpos
  have hloglogSq :
      (Real.log (Real.log X)) ^ 2 ≤ (Real.log X) ^ (η / 2) := by
    simpa only [Real.rpow_two] using hlogPartX
  have hright0 : 0 ≤ (Real.log X) ^ (η / 2) :=
    Real.rpow_nonneg hlogXpos.le _
  calc
    (A * Real.log (Real.log X)) ^ 2 =
        A ^ 2 * (Real.log (Real.log X)) ^ 2 := by ring
    _ ≤ (Real.log X) ^ (η / 2) * (Real.log X) ^ (η / 2) :=
      mul_le_mul hconstPartX hloglogSq (sq_nonneg _) hright0
    _ = (Real.log X) ^ η := by
      rw [← Real.rpow_add hlogXpos]
      congr 1
      ring

/-- Consequently, any nonnegative block count bounded by
`A log log X` has square at most `(log X)^η` for all sufficiently large
`X`. -/
theorem eventually_blockCount_sq_le_log_rpow
    (A : ℝ) (hA : 0 ≤ A) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ X : ℝ in atTop, ∀ R : ℝ,
      0 ≤ R → R ≤ A * Real.log (Real.log X) →
        R ^ 2 ≤ (Real.log X) ^ η := by
  filter_upwards [eventually_const_mul_log_log_sq_le_log_rpow A hA hη]
    with X hX
  intro R hR hRbound
  have hupper0 : 0 ≤ A * Real.log (Real.log X) := hR.trans hRbound
  exact ((sq_le_sq₀ hR hupper0).mpr hRbound).trans hX

/-- Section 7.2's deterministic conclusion.  If every normalized block
variance saves `(log X)^(2+ε)`, the number of blocks is at most `R`, and
`R² ≤ (log X)^η`, the summed variance still saves
`(log X)^(2+ε-η)`. -/
theorem normalized_summedBlockVariance_logSaving
    {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (E : Set α) (s : Finset ι)
    (error : ι → α → ℂ)
    {scale X C ε η R : ℝ}
    (hscale : 0 < scale) (hX : 1 < X) (hC : 0 ≤ C)
    (hE : MeasurableSet E)
    (htotal : IntegrableOn
      (fun x ↦ ‖summedBlockError s error x‖ ^ 2) E μ)
    (hblock : ∀ i ∈ s,
      IntegrableOn (fun x ↦ ‖error i x‖ ^ 2) E μ)
    (hR : (s.card : ℝ) ≤ R)
    (hblockSquare : R ^ 2 ≤ (Real.log X) ^ η)
    (heach : ∀ i ∈ s,
      (∫ x in E, ‖error i x‖ ^ 2 ∂μ) / scale ≤
        C / (Real.log X) ^ (2 + ε)) :
    (∫ x in E, ‖summedBlockError s error x‖ ^ 2 ∂μ) / scale ≤
      C / (Real.log X) ^ (2 + ε - η) := by
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hV : 0 ≤ C / (Real.log X) ^ (2 + ε) :=
    div_nonneg hC (Real.rpow_nonneg hlog.le _)
  have hcardBound :=
    normalized_integral_summedBlockError_sq_le_card_sq_mul
      μ E s error hscale hV hE htotal hblock heach
  have hR0 : 0 ≤ R := (Nat.cast_nonneg s.card).trans hR
  calc
    (∫ x in E, ‖summedBlockError s error x‖ ^ 2 ∂μ) / scale ≤
        (s.card : ℝ) ^ 2 *
          (C / (Real.log X) ^ (2 + ε)) := hcardBound
    _ ≤ R ^ 2 * (C / (Real.log X) ^ (2 + ε)) := by
      gcongr
    _ ≤ C / (Real.log X) ^ (2 + ε - η) :=
      absorb_block_square_into_logSaving hC hlog hR0 hblockSquare

def varianceBlockSummationModule : ProofModule :=
  { name := "Completion.VarianceBlockSummation"
    paperLocation := "Section 7.2, Cauchy--Schwarz over the blocks"
    purpose := "Preserve a logarithmic power saving after summing O(log log X) variances."
    dependsOn :=
      [ "Completion.ParameterizedReduction",
        "Completion.DyadicPrimeBlocks",
        "TypeII.PolynomialLengthRanges",
        "Mathlib Cauchy--Schwarz" ]
    status := .proved }

end

end Completion
end ExactSemiprimes
