import ExactSemiprimes.Sparse.EndpointSaturation
import ExactSemiprimes.Sparse.SupportGeometry
import ExactSemiprimes.Sparse.FirstBranch
import ExactSemiprimes.Sparse.MagnitudeBins
import ExactSemiprimes.Sparse.ComplexCoefficientSplit
import ExactSemiprimes.Sparse.SecondBranch
import ExactSemiprimes.TypeII.PolynomialLengthRanges

/-! # Propagation through the complete sparse Type-II range

The first section records the single-threshold endpoint algebra
(`endpointKeyInequality_with_errors` and its corollaries), which gives
`a > 35/32` when both large-value exponents are only known to exceed `17/70`.
The two-branch packages below take the key inequality of the second branch as
a hypothesis (`hkey`); the final proof supplies it, for `a > 1925/1763`, from
the three-case analysis in `Final/TypeIIDensityBins.lean`. -/

namespace ExactSemiprimes
namespace Sparse

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section

/-! ## Error-budgeted endpoint algebra -/

/-- Robust form of the numerical heart of Section 6.  The hypotheses expose
the two `O(ε)` losses in the paper: `residualError` in the residual inequality
and `sigmaError` in the lower bounds for the two large-value exponents.  A
separate `keyError` is the amount needed to absorb logarithmic factors in the
second Heath--Brown branch. -/
theorem endpointKeyInequality_with_errors
    {a s σ₁ σ₂ θ residualError sigmaError keyError : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hσ₁ : s - sigmaError ≤ σ₁)
    (hσ₂ : s - sigmaError ≤ σ₂)
    (hres : 1 - 1 / a - residualError ≤ θ * (1 - 2 * σ₁))
    (hbudget :
      1 / a + keyError <
        5 * (1 - 1 / a - residualError) +
          2 * (s - sigmaError)) :
    1 / a + keyError < secondBranchKeyExponent θ σ₁ σ₂ := by
  have hθcompl : 0 ≤ 1 - θ := by linarith
  have hsigma1term :
      θ * (1 - 2 * σ₁) ≤ θ * (1 - 2 * (s - sigmaError)) := by
    have := mul_le_mul_of_nonneg_left hσ₁ hθ0
    nlinarith
  have hsigma2term :
      2 * (s - sigmaError) * (1 - θ) ≤
        2 * σ₂ * (1 - θ) := by
    have := mul_le_mul_of_nonneg_right hσ₂ hθcompl
    nlinarith
  dsimp [secondBranchKeyExponent]
  nlinarith

/-- Any strict endpoint margin contains a uniform positive box of admissible
error parameters.  The weights `5`, `2`, and `1` are exactly those occurring
when `hbudget` is expanded. -/
theorem exists_endpoint_error_budget {a s : ℝ}
    (hstrict : 1 / a < 5 * (1 - 1 / a) + 2 * s) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ residualError sigmaError keyError : ℝ,
        0 ≤ residualError → residualError ≤ δ →
        0 ≤ sigmaError → sigmaError ≤ δ →
        0 ≤ keyError → keyError ≤ δ →
        1 / a + keyError <
          5 * (1 - 1 / a - residualError) +
            2 * (s - sigmaError) := by
  let margin : ℝ :=
    5 * (1 - 1 / a) + 2 * s - 1 / a
  have hmargin : 0 < margin := by
    dsimp [margin]
    linarith
  refine ⟨margin / 16, by positivity, ?_⟩
  intro residualError sigmaError keyError
    _hresNonneg hres hsigmaNonneg hsigma hkeyNonneg hkey
  have htotal :
      5 * residualError + 2 * sigmaError + keyError ≤
        8 * (margin / 16) := by
    nlinarith
  dsimp [margin] at hmargin ⊢
  nlinarith

/-- At the paper's value `s=17/70`, every strict inequality
`a>35/32` therefore leaves a positive uniform error budget. -/
theorem exists_error_budget_above_thirtyFive_over_thirtyTwo
    {a : ℝ} (ha : (35 : ℝ) / 32 < a) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ residualError sigmaError keyError : ℝ,
        0 ≤ residualError → residualError ≤ δ →
        0 ≤ sigmaError → sigmaError ≤ δ →
        0 ≤ keyError → keyError ≤ δ →
        1 / a + keyError <
          5 * (1 - 1 / a - residualError) +
            2 * ((17 : ℝ) / 70 - sigmaError) := by
  have hapos : 0 < a := lt_trans (by norm_num) ha
  have hthreshold :
      6 / (5 + 2 * ((17 : ℝ) / 70)) < a := by
    norm_num at ⊢
    exact ha
  have hstrict :
      1 / a < 5 * (1 - 1 / a) + 2 * ((17 : ℝ) / 70) :=
    (endpointThresholdIff hapos (by norm_num)).2 hthreshold
  exact exists_endpoint_error_budget hstrict

/-- Exact two-branch propagation in the power model.  No analytic theorem
is hidden here: the left disjunct is the first-branch sufficient condition,
and the right disjunct is precisely the power inequality consumed by the
second branch. -/
theorem firstOrSecondBranch_exactPowerDichotomy_of_key
    {X M M₁ a theta sigma₁ sigma₂ scaleError firstError
      residualError keyError : ℝ}
    (hX : 1 < X) (hM : 0 < M) (hM₁ : 0 < M₁) (ha : 1 < a)
    (htheta : Real.log M₁ / Real.log X = theta)
    (hMExponent : 1 - scaleError ≤ Real.log M / Real.log X)
    (hresidualError :
      residualError = firstError + scaleError * (1 - 1 / a))
    (hkey : 1 - 1 / a - residualError ≤ theta * (1 - 2 * sigma₁) →
      1 / a + keyError < secondBranchKeyExponent theta sigma₁ sigma₂) :
    M₁ ^ (1 - 2 * sigma₁) ≤
        X ^ (-firstError) * M ^ (1 - 1 / a) ∨
      X ^ (1 / a + keyError) ≤
        (X ^ theta) ^ (5 - 8 * sigma₁) *
          (X ^ (1 - theta)) ^ (2 * sigma₂) := by
  by_cases hfirst : M₁ ^ (1 - 2 * sigma₁) ≤
      X ^ (-firstError) * M ^ (1 - 1 / a)
  · exact Or.inl hfirst
  · right
    have hres := firstBranch_residual_of_second_condition_failure
      hX hM hM₁ ha htheta hMExponent hfirst
    rw [← hresidualError] at hres
    have hk := hkey hres
    rw [secondBranch_power_identity (lt_trans zero_lt_one hX)]
    exact Real.rpow_le_rpow_of_exponent_le hX.le hk.le

/-- The uniform-budget form of the dichotomy (the published argument). -/
theorem firstOrSecondBranch_exactPowerDichotomy
    {X M M₁ a theta sigma₁ sigma₂ s scaleError firstError
      residualError sigmaError keyError : ℝ}
    (hX : 1 < X) (hM : 0 < M) (hM₁ : 0 < M₁) (ha : 1 < a)
    (htheta : Real.log M₁ / Real.log X = theta)
    (hMExponent : 1 - scaleError ≤ Real.log M / Real.log X)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hsigma₁ : s - sigmaError ≤ sigma₁)
    (hsigma₂ : s - sigmaError ≤ sigma₂)
    (hresidualError :
      residualError = firstError + scaleError * (1 - 1 / a))
    (hbudget :
      1 / a + keyError <
        5 * (1 - 1 / a - residualError) +
          2 * (s - sigmaError)) :
    M₁ ^ (1 - 2 * sigma₁) ≤
        X ^ (-firstError) * M ^ (1 - 1 / a) ∨
      X ^ (1 / a + keyError) ≤
        (X ^ theta) ^ (5 - 8 * sigma₁) *
          (X ^ (1 - theta)) ^ (2 * sigma₂) :=
  firstOrSecondBranch_exactPowerDichotomy_of_key hX hM hM₁ ha htheta hMExponent
    hresidualError (fun hres ↦
      endpointKeyInequality_with_errors htheta0 htheta1 hsigma₁ hsigma₂ hres hbudget)

/-- Convert the first alternative of the power dichotomy into the exponent
inequality consumed by the first-branch majorant budget. -/
theorem firstBranch_exponentCondition_of_powerCondition
    {X M M1 a epsilon mu theta sigma1 : ℝ}
    (hX : 1 < X) (hMcoord : M = X ^ mu) (hM1coord : M1 = X ^ theta)
    (hpower :
      M1 ^ (1 - 2 * sigma1) ≤
        X ^ (-epsilon / 3) * M ^ (1 - 1 / a)) :
    theta * (1 - 2 * sigma1) ≤
      -epsilon / 3 + mu * (1 - 1 / a) := by
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hrewritten :
      X ^ (theta * (1 - 2 * sigma1)) ≤
        X ^ (-epsilon / 3 + mu * (1 - 1 / a)) := by
    calc
      X ^ (theta * (1 - 2 * sigma1)) = M1 ^ (1 - 2 * sigma1) := by
        rw [hM1coord]
        exact Real.rpow_mul hXpos.le theta (1 - 2 * sigma1)
      _ ≤ X ^ (-epsilon / 3) * M ^ (1 - 1 / a) := hpower
      _ = X ^ (-epsilon / 3 + mu * (1 - 1 / a)) := by
        rw [hMcoord]
        calc
          X ^ (-epsilon / 3) * (X ^ mu) ^ (1 - 1 / a) =
              X ^ (-epsilon / 3) * X ^ (mu * (1 - 1 / a)) := by
                rw [← Real.rpow_mul hXpos.le]
          _ = X ^ (-epsilon / 3 + mu * (1 - 1 / a)) :=
            (Real.rpow_add hXpos _ _).symm
  exact (Real.strictMono_rpow_of_base_gt_one hX).le_iff_le.mp hrewritten

/-- Convert the second alternative of the power dichotomy into the key
exponent inequality consumed by the literal five-block budget. -/
theorem secondBranch_keyExponent_of_powerCondition
    {X M1 M2 a epsilon theta phi sigma1 sigma2 : ℝ}
    (hX : 1 < X) (hM1coord : M1 = X ^ theta)
    (hM2coord : M2 = X ^ phi)
    (hpower :
      X ^ (1 / a + 4 * epsilon) ≤
        M1 ^ (5 - 8 * sigma1) * M2 ^ (2 * sigma2)) :
    1 / a + 4 * epsilon ≤
      (5 - 8 * sigma1) * theta + 2 * sigma2 * phi := by
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hrewritten :
      X ^ (1 / a + 4 * epsilon) ≤
        X ^ ((5 - 8 * sigma1) * theta + 2 * sigma2 * phi) := by
    calc
      X ^ (1 / a + 4 * epsilon) ≤
          M1 ^ (5 - 8 * sigma1) * M2 ^ (2 * sigma2) := hpower
      _ = X ^ ((5 - 8 * sigma1) * theta + 2 * sigma2 * phi) := by
        rw [hM1coord, hM2coord]
        calc
          (X ^ theta) ^ (5 - 8 * sigma1) *
                (X ^ phi) ^ (2 * sigma2) =
              X ^ (theta * (5 - 8 * sigma1)) *
                X ^ (phi * (2 * sigma2)) := by
                  rw [← Real.rpow_mul hXpos.le,
                    ← Real.rpow_mul hXpos.le]
          _ = X ^ (theta * (5 - 8 * sigma1) +
                phi * (2 * sigma2)) :=
            (Real.rpow_add hXpos _ _).symm
          _ = X ^ ((5 - 8 * sigma1) * theta +
                2 * sigma2 * phi) := by
            congr 1
            ring
  exact (Real.strictMono_rpow_of_base_gt_one hX).le_iff_le.mp hrewritten

/-- Deterministic logarithmic lower bound for a powered scale whose exponent
is the natural floor of `log X / log (2P)`.  The two error terms isolate the
factor two in the denominator and the loss of less than one from the floor. -/
theorem log_pow_floor_ratio_lower
    {X P epsilon : ℝ}
    (hX : 1 < X) (hP : 1 < P)
    (hconst : Real.log 2 / Real.log P ≤ epsilon / 2)
    (hscale : Real.log P / Real.log X ≤ epsilon / 2) :
    let k : ℕ := ⌊Real.log X / Real.log (2 * P)⌋₊
    let M : ℝ := P ^ k
    1 - epsilon ≤ Real.log M / Real.log X := by
  dsimp only
  let L : ℝ := Real.log X
  let A : ℝ := Real.log P
  let d : ℝ := Real.log (2 * P)
  let k : ℕ := ⌊L / d⌋₊
  have hL : 0 < L := Real.log_pos hX
  have hA : 0 < A := Real.log_pos hP
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdEq : d = Real.log 2 + A := by
    dsimp [d, A]
    rw [Real.log_mul (by norm_num)
      (ne_of_gt (lt_trans zero_lt_one hP))]
  have hd : 0 < d := by rw [hdEq]; positivity
  have hfloor : L / d - 1 ≤ (k : ℝ) :=
    (Nat.sub_one_lt_floor (L / d)).le
  have hfactor : 0 ≤ A / L := div_nonneg hA.le hL.le
  have hfloorMul :
      (L / d - 1) * (A / L) ≤ (k : ℝ) * (A / L) :=
    mul_le_mul_of_nonneg_right hfloor hfactor
  have hconst' : Real.log 2 / A ≤ epsilon / 2 := by
    simpa only [A] using hconst
  have hscale' : A / L ≤ epsilon / 2 := by
    simpa only [A, L] using hscale
  have hdenomCompare :
      Real.log 2 / d ≤ Real.log 2 / A := by
    apply div_le_div_of_nonneg_left hlogTwo.le hA
    rw [hdEq]
    linarith
  have hAd : 1 - epsilon / 2 ≤ A / d := by
    have hid : A / d = 1 - Real.log 2 / d := by
      rw [hdEq]
      field_simp [ne_of_gt hA, ne_of_gt hd]
      ring
    rw [hid]
    linarith
  have hraw : 1 - epsilon ≤ A / d - A / L := by
    linarith
  have hrewrite :
      (L / d - 1) * (A / L) = A / d - A / L := by
    field_simp [ne_of_gt hL, ne_of_gt hd]
  have hkRewrite :
      (k : ℝ) * (A / L) = ((k : ℝ) * A) / L := by ring
  rw [hrewrite, hkRewrite] at hfloorMul
  have hmain : 1 - epsilon ≤ ((k : ℝ) * A) / L :=
    hraw.trans hfloorMul
  simpa only [k, L, A, Real.log_pow] using hmain

/-- For the moving paper scale `P=(log X)^a` and
`k=floor(log X/log(2P))`, the resulting length `M=P^k` has logarithmic
exponent arbitrarily close to one from below. -/
theorem eventually_log_paperSparseScale_ratio
    {a scaleError : ℝ} (ha : 0 < a) (hscaleError : 0 < scaleError) :
    ∀ᶠ X : ℕ in Filter.atTop,
      let P : ℝ := (Real.log (X : ℝ)) ^ a
      let k : ℕ := ⌊Real.log (X : ℝ) / Real.log (2 * P)⌋₊
      let M : ℝ := P ^ k
      1 - scaleError ≤ Real.log M / Real.log (X : ℝ) := by
  have hlogNat :
      Filter.Tendsto (fun X : ℕ ↦ Real.log (X : ℝ))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglogNat :
      Filter.Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ)))
        Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp hlogNat
  let c : ℝ := scaleError / (2 * a)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hsmall : ∀ᶠ X : ℕ in Filter.atTop,
      ‖Real.log (Real.log (X : ℝ))‖ ≤
        c * ‖Real.log (X : ℝ)‖ :=
    (Real.isLittleO_log_id_atTop.comp_tendsto hlogNat).bound hc
  have hlargeLog : ∀ᶠ X : ℕ in Filter.atTop,
      Real.exp 1 ≤ Real.log (X : ℝ) :=
    hlogNat.eventually_ge_atTop (Real.exp 1)
  have hlargeLogLog : ∀ᶠ X : ℕ in Filter.atTop,
      2 * Real.log 2 / (a * scaleError) ≤
        Real.log (Real.log (X : ℝ)) :=
    hloglogNat.eventually_ge_atTop
      (2 * Real.log 2 / (a * scaleError))
  filter_upwards [hsmall, hlargeLog, hlargeLogLog] with
      X hsmallX hLX hLLX
  dsimp only
  let L : ℝ := Real.log (X : ℝ)
  let P : ℝ := L ^ a
  have hLpos : 0 < L := (Real.exp_pos 1).trans_le hLX
  have hLone : 1 < L :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hLX
  have hlogLpos : 0 < Real.log L := Real.log_pos hLone
  have hPone : 1 < P := by
    dsimp [P]
    exact Real.one_lt_rpow hLone ha
  have hlogP : Real.log P = a * Real.log L := by
    dsimp [P]
    rw [Real.log_rpow hLpos]
  have hsmallPlain : Real.log L ≤ c * L := by
    simpa only [L, Real.norm_of_nonneg hlogLpos.le,
      Real.norm_of_nonneg hLpos.le] using hsmallX
  have hscale : Real.log P / L ≤ scaleError / 2 := by
    rw [hlogP]
    apply (div_le_iff₀ hLpos).2
    calc
      a * Real.log L ≤ a * (c * L) :=
        mul_le_mul_of_nonneg_left hsmallPlain ha.le
      _ = scaleError / 2 * L := by
        dsimp [c]
        field_simp [ne_of_gt ha]
  have hpositiveProduct : 0 < a * scaleError :=
    mul_pos ha hscaleError
  have hlargeMul :
      (2 * Real.log 2 / (a * scaleError)) * (a * scaleError) ≤
        Real.log L * (a * scaleError) :=
    mul_le_mul_of_nonneg_right (by simpa only [L] using hLLX)
      hpositiveProduct.le
  have hlogTwoBound :
      Real.log 2 ≤ scaleError / 2 * (a * Real.log L) := by
    have hcancel :
        (2 * Real.log 2 / (a * scaleError)) * (a * scaleError) =
          2 * Real.log 2 := by
      field_simp [ne_of_gt hpositiveProduct]
    rw [hcancel] at hlargeMul
    nlinarith
  have hconst : Real.log 2 / Real.log P ≤ scaleError / 2 := by
    rw [hlogP]
    exact (div_le_iff₀ (mul_pos ha hlogLpos)).2 hlogTwoBound
  have hXone : 1 < (X : ℝ) := by
    have hlogXpos : 0 < Real.log (X : ℝ) := by
      simpa only [L] using hLpos
    exact (Real.log_pos_iff
      (by positivity : 0 ≤ (X : ℝ))).mp hlogXpos
  simpa only [L, P] using
    log_pow_floor_ratio_lower hXone hPone hconst hscale

/-- The moving sparse support is small relative to its actual Dirichlet
polynomial length `M`, with any prescribed positive exponent slack. -/
theorem eventually_card_paperSparseSupport_le_relativeLength
    (hHT : HildebrandTenenbaumCorollaryOneThreeStatement)
    {a supportSlack : ℝ} (ha : 1 < a) (_haUpper : a < 3 / 2)
    (hSupportSlack : 0 < supportSlack) :
    ∀ᶠ X : ℕ in atTop,
      let P : ℝ := (Real.log (X : ℝ)) ^ a
      let k : ℕ :=
        ⌊Real.log (X : ℝ) / Real.log (2 * P)⌋₊
      let M : ℝ := P ^ k
      ((primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
        M ^ (1 - 1 / a + supportSlack) := by
  let supportExponent : ℝ := 1 - 1 / a + supportSlack
  let smoothSlack : ℝ := supportSlack / 4
  let scaleError : ℝ := supportSlack / (4 * supportExponent)
  have haPos : 0 < a := lt_trans zero_lt_one ha
  have hbaseExponent : 0 < 1 - 1 / a := by
    rw [sub_pos, div_lt_one haPos]
    exact ha
  have hSupportExponent : 0 < supportExponent := by
    dsimp [supportExponent]
    linarith
  have hSmoothSlack : 0 < smoothSlack := by
    dsimp [smoothSlack]
    positivity
  have hScaleError : 0 < scaleError := by
    dsimp [scaleError]
    positivity
  have hcard := eventually_card_paperSparseSupport_le
    hHT ha hSmoothSlack
  have hscale := eventually_log_paperSparseScale_ratio
    haPos hScaleError
  filter_upwards [hcard, hscale, eventually_ge_atTop (2 : ℕ)] with
      X hcardX hscaleX hX
  dsimp only at hcardX hscaleX ⊢
  let P : ℝ := (Real.log (X : ℝ)) ^ a
  let k : ℕ :=
    ⌊Real.log (X : ℝ) / Real.log (2 * P)⌋₊
  let M : ℝ := P ^ k
  have hXReal : 1 < (X : ℝ) := by
    exact_mod_cast (show 1 < X by omega)
  have hXpos : 0 < (X : ℝ) := lt_trans zero_lt_one hXReal
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hXReal
  have hPpos : 0 < P := by
    dsimp [P]
    exact Real.rpow_pos_of_pos hlogX a
  have hMpos : 0 < M := by
    dsimp [M]
    positivity
  have hScaleMul : scaleError * supportExponent = supportSlack / 4 := by
    dsimp [scaleError]
    field_simp [ne_of_gt hSupportExponent]
  have hExponentBudget :
      1 - 1 / a + smoothSlack ≤
        (1 - scaleError) * supportExponent := by
    dsimp [smoothSlack, supportExponent] at hScaleMul ⊢
    nlinarith
  have hlogM :
      (1 - scaleError) * Real.log (X : ℝ) ≤ Real.log M := by
    change 1 - scaleError ≤
      Real.log M / Real.log (X : ℝ) at hscaleX
    exact (le_div_iff₀ hlogX).mp hscaleX
  have hpowCompare :
      (X : ℝ) ^ (1 - 1 / a + smoothSlack) ≤
        M ^ supportExponent := by
    rw [Real.rpow_def_of_pos hXpos, Real.rpow_def_of_pos hMpos]
    apply Real.exp_le_exp.mpr
    calc
      Real.log (X : ℝ) * (1 - 1 / a + smoothSlack) ≤
          Real.log (X : ℝ) *
            ((1 - scaleError) * supportExponent) :=
        mul_le_mul_of_nonneg_left hExponentBudget hlogX.le
      _ = supportExponent *
            ((1 - scaleError) * Real.log (X : ℝ)) := by ring
      _ ≤ supportExponent * Real.log M :=
        mul_le_mul_of_nonneg_left hlogM hSupportExponent.le
      _ = Real.log M * supportExponent := by ring
  exact hcardX.trans (by simpa [supportExponent] using hpowCompare)

/-! ## The structured real coefficient at the first Type-II scale -/

/-- The real coefficient obtained by restricting the structured source
coefficient to the literal Type-II `m₁` range. -/
noncomputable def structuredTypeIIRealCoefficient
    (delta M₁ : ℝ) (R : ℕ) (Q : Fin R → ℝ) (m : ℕ) : ℝ :=
  if M₁ < (m : ℝ) ∧ (m : ℝ) ≤ (1 + delta) ^ R * M₁ then
    (matomakiTeravainenStructuredTypeIICoefficient delta R Q m).re
  else 0

theorem structuredTypeIIRealCoefficient_cast
    (delta M₁ : ℝ) (R : ℕ) (Q : Fin R → ℝ) (m : ℕ) :
    (structuredTypeIIRealCoefficient delta M₁ R Q m : ℂ) =
      if M₁ < (m : ℝ) ∧ (m : ℝ) ≤ (1 + delta) ^ R * M₁ then
        matomakiTeravainenStructuredTypeIICoefficient delta R Q m
      else 0 := by
  classical
  by_cases hm : M₁ < (m : ℝ) ∧
      (m : ℝ) ≤ (1 + delta) ^ R * M₁
  · simp only [structuredTypeIIRealCoefficient, hm]
    simp [matomakiTeravainenStructuredTypeIICoefficient]
  · simp [structuredTypeIIRealCoefficient, hm]

/-- The source's uniform divisor bound passes to the truncated real
coefficient with exactly the same witnesses. -/
theorem structuredTypeIIRealCoefficient_divisorBound
    {delta M₁ B A : ℝ} {R : ℕ} {Q : Fin R → ℝ}
    (hstructured : IsDivisorBoundedByConstant B A
      (matomakiTeravainenStructuredTypeIICoefficient delta R Q)) :
    IsDivisorBoundedByConstant B A
      (fun m ↦ (structuredTypeIIRealCoefficient delta M₁ R Q m : ℂ)) := by
  refine ⟨hstructured.1, hstructured.2.1, ?_⟩
  intro m hm
  by_cases hrange : M₁ < (m : ℝ) ∧
      (m : ℝ) ≤ (1 + delta) ^ R * M₁
  · simp only [structuredTypeIIRealCoefficient, hrange]
    calc
      ‖((matomakiTeravainenStructuredTypeIICoefficient
          delta R Q m).re : ℂ)‖ =
          |(matomakiTeravainenStructuredTypeIICoefficient
            delta R Q m).re| := by simp
      _ ≤ ‖matomakiTeravainenStructuredTypeIICoefficient delta R Q m‖ :=
        Complex.abs_re_le_norm _
      _ ≤ A * (divisorCount m : ℝ) ^ B := hstructured.2.2 m hm
  · simp [structuredTypeIIRealCoefficient, hrange,
      mul_nonneg hstructured.2.1.le
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

/-- Once the narrow upper endpoint is at most `2M₁`, the truncated
coefficient is supported on the dyadic interval used by the sparse theorem. -/
theorem structuredTypeIIRealCoefficient_eq_zero_of_not_mem_dyadic
    {delta M₁ : ℝ} {R : ℕ} {Q : Fin R → ℝ} {m : ℕ}
    (hM₁ : 0 ≤ M₁) (hupper : (1 + delta) ^ R ≤ 2)
    (hm : m ∉ dyadicInterval M₁) :
    structuredTypeIIRealCoefficient delta M₁ R Q m = 0 := by
  rw [structuredTypeIIRealCoefficient]
  split_ifs with hrange
  · exfalso
    apply hm
    rw [mem_dyadicInterval hM₁]
    refine ⟨hrange.1, ?_⟩
    calc
      (m : ℝ) ≤ (1 + delta) ^ R * M₁ := hrange.2
      _ ≤ 2 * M₁ := mul_le_mul_of_nonneg_right hupper hM₁
  · rfl

/-- Summing the truncated real coefficient over the dyadic interval is
exactly the narrow structured source polynomial. -/
theorem dyadicPolynomial_structuredTypeIIRealCoefficient_eq
    {delta M₁ : ℝ} {R : ℕ} {Q : Fin R → ℝ} (s : ℂ) :
    dyadicDirichletPolynomial
        (fun m ↦ (structuredTypeIIRealCoefficient delta M₁ R Q m : ℂ))
        M₁ s =
      dirichletPolynomial
        (matomakiTeravainenStructuredTypeIICoefficient delta R Q)
        ((dyadicInterval M₁).filter fun m ↦
          M₁ < (m : ℝ) ∧
            (m : ℝ) ≤ (1 + delta) ^ R * M₁) s := by
  classical
  unfold dyadicDirichletPolynomial dirichletPolynomial
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hrange : M₁ < (m : ℝ) ∧
      (m : ℝ) ≤ (1 + delta) ^ R * M₁
  · simp [hrange, structuredTypeIIRealCoefficient_cast]
  · simp [hrange, structuredTypeIIRealCoefficient_cast]

/-- The elementary exponential criterion behind `(1+delta)^R ≤ 2`. -/
theorem one_add_pow_le_two_of_nat_mul_le_log_two
    {delta : ℝ} {R : ℕ} (hdelta : 0 ≤ delta)
    (hsmall : (R : ℝ) * delta ≤ Real.log 2) :
    (1 + delta) ^ R ≤ 2 := by
  have hbase : 1 + delta ≤ Real.exp delta := by
    linarith [Real.add_one_le_exp delta]
  calc
    (1 + delta) ^ R ≤ (Real.exp delta) ^ R :=
      pow_le_pow_left₀ (by linarith) hbase R
    _ = Real.exp ((R : ℝ) * delta) := by
      rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hsmall
    _ = 2 := Real.exp_log (by norm_num)

/-- The logarithmic product controlling the source's structured multiplicity
tends to zero. -/
theorem tendsto_loglog_cube_mul_log_rpow_neg_atTop
    {A : ℝ} (hA : 0 < A) :
    Tendsto
      (fun X : ℝ ↦
        (Real.log (Real.log X)) ^ (3 : ℕ) *
          (Real.log X) ^ (-10 * A))
      atTop (nhds 0) := by
  have hpower : 0 < 10 * A := mul_pos (by norm_num) hA
  have hratio : Tendsto
      (fun u : ℝ ↦ (Real.log u) ^ (3 : ℝ) / u ^ (10 * A))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (3 : ℝ) hpower).tendsto_div_nhds_zero
  have hsame : ∀ᶠ u : ℝ in atTop,
      (Real.log u) ^ (3 : ℕ) * u ^ (-10 * A) =
        (Real.log u) ^ (3 : ℝ) / u ^ (10 * A) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [← Real.rpow_natCast]
    rw [show -10 * A = -(10 * A) by ring]
    rw [Real.rpow_neg hu.le]
    rfl
  exact (hratio.congr' (Filter.EventuallyEq.symm hsame)).comp
    Real.tendsto_log_atTop

/-- Hence the source-scale product is eventually below any prescribed
positive constant. -/
theorem eventually_loglog_cube_mul_log_rpow_neg_le
    {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop,
      (Real.log (Real.log X)) ^ (3 : ℕ) *
          (Real.log X) ^ (-10 * A) ≤ c := by
  have hnhds : Set.Iio c ∈ nhds (0 : ℝ) := Iio_mem_nhds hc
  filter_upwards
    [(tendsto_loglog_cube_mul_log_rpow_neg_atTop hA).eventually hnhds]
      with X hX
  exact hX.le

theorem source_structured_log_ratio_eq
    {X : ℝ} (hX : Real.exp 1 < X) :
    Real.log (X ^ (2 / 11 : ℝ)) /
        Real.log
          (Real.exp
            (Real.log X / (Real.log (Real.log X)) ^ (3 : ℕ))) =
      (2 / 11 : ℝ) * (Real.log (Real.log X)) ^ (3 : ℕ) := by
  have hXpos : 0 < X := (Real.exp_pos 1).trans hX
  have hlogX : 1 < Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log (Real.exp_pos 1) hXpos hX
  have hloglog : 0 < Real.log (Real.log X) := Real.log_pos hlogX
  rw [Real.log_rpow hXpos, Real.log_exp]
  field_simp

/-- At the literal source scales, the Type-II `m₁` window is eventually
contained in a dyadic interval, uniformly over every admissible `R`. -/
theorem eventually_source_one_add_delta_pow_R_le_two
    {A : ℝ} (hA : 0 < A) :
    ∀ᶠ X : ℝ in atTop, ∀ R : ℕ,
      R ≤ ⌊Real.log (X ^ (2 / 11 : ℝ)) /
          Real.log
            (Real.exp
              (Real.log X /
                (Real.log (Real.log X)) ^ (3 : ℕ)))⌋₊ →
      (1 + (Real.log X) ^ (-10 * A)) ^ R ≤ 2 := by
  have hlogtwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  filter_upwards
      [eventually_gt_atTop (Real.exp 1),
        eventually_loglog_cube_mul_log_rpow_neg_le hA hlogtwo]
      with X hX hsmall
  intro R hR
  have hXpos : 0 < X := (Real.exp_pos 1).trans hX
  have hlogX : 1 < Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log (Real.exp_pos 1) hXpos hX
  have hloglog : 0 < Real.log (Real.log X) := Real.log_pos hlogX
  have hdelta : 0 ≤ (Real.log X) ^ (-10 * A) :=
    Real.rpow_nonneg (by linarith) _
  let K : ℝ := Real.log (X ^ (2 / 11 : ℝ)) /
    Real.log
      (Real.exp
        (Real.log X / (Real.log (Real.log X)) ^ (3 : ℕ)))
  have hK : K = (2 / 11 : ℝ) *
      (Real.log (Real.log X)) ^ (3 : ℕ) :=
    source_structured_log_ratio_eq hX
  have hKnonneg : 0 ≤ K := by
    rw [hK]
    positivity
  have hRreal : (R : ℝ) ≤ K := by
    calc
      (R : ℝ) ≤ (⌊K⌋₊ : ℝ) := by exact_mod_cast hR
      _ ≤ K := Nat.floor_le hKnonneg
  apply one_add_pow_le_two_of_nat_mul_le_log_two hdelta
  calc
    (R : ℝ) * (Real.log X) ^ (-10 * A) ≤
        K * (Real.log X) ^ (-10 * A) :=
      mul_le_mul_of_nonneg_right hRreal hdelta
    _ = (2 / 11 : ℝ) *
        ((Real.log (Real.log X)) ^ (3 : ℕ) *
          (Real.log X) ^ (-10 * A)) := by rw [hK]; ring
    _ ≤ 1 *
        ((Real.log (Real.log X)) ^ (3 : ℕ) *
          (Real.log X) ^ (-10 * A)) := by
      gcongr
      · norm_num
    _ ≤ Real.log 2 := by simpa using hsmall

/-! ## Uniform coefficient-supremum losses -/

/-- One global divisor-subpower witness controls both componentwise dyadic
suprema, uniformly in the real dyadic scale. -/
theorem beta_parts_dyadicSup_subpower
    (hglobal : Hybrid.GlobalDivisorSubpowerStatement)
    {beta : ℕ → ℂ} {B A rho : ℝ}
    (hrho : 0 < rho)
    (hbeta : IsDivisorBoundedByConstant B A beta) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ N : ℝ, 1 ≤ N →
      dyadicRealCoefficientSup (fun n ↦ (beta n).re) N ≤
          A * D * (2 * N) ^ rho ∧
      dyadicRealCoefficientSup (fun n ↦ (beta n).im) N ≤
          A * D * (2 * N) ^ rho := by
  obtain ⟨D, hD, hDbound⟩ := hglobal B rho hbeta.1 hrho
  refine ⟨D, hD, ?_⟩
  intro N hN
  have hN0 : 0 ≤ N := by linarith
  have hA0 : 0 ≤ A := hbeta.2.1.le
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hK0 : 0 ≤ A * D * (2 * N) ^ rho := by positivity
  constructor
  · apply dyadicRealCoefficientSup_le hK0
    intro n hn
    have hnrange := (mem_dyadicInterval hN0).mp hn
    have hnpos : 0 < n := by
      have : (0 : ℝ) < n := lt_of_le_of_lt hN0 hnrange.1
      exact_mod_cast this
    have hnorm := hbeta.2.2 n hnpos
    have hdiv := hDbound n hnpos
    have hnpow : (n : ℝ) ^ rho ≤ (2 * N) ^ rho :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) hnrange.2 hrho.le
    calc
      |(beta n).re| ≤ ‖beta n‖ := Complex.abs_re_le_norm _
      _ ≤ A * (divisorCount n : ℝ) ^ B := hnorm
      _ ≤ A * (D * (n : ℝ) ^ rho) :=
        mul_le_mul_of_nonneg_left hdiv hA0
      _ ≤ A * (D * (2 * N) ^ rho) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hnpow hD0) hA0
      _ = A * D * (2 * N) ^ rho := by ring
  · apply dyadicRealCoefficientSup_le hK0
    intro n hn
    have hnrange := (mem_dyadicInterval hN0).mp hn
    have hnpos : 0 < n := by
      have : (0 : ℝ) < n := lt_of_le_of_lt hN0 hnrange.1
      exact_mod_cast this
    have hnorm := hbeta.2.2 n hnpos
    have hdiv := hDbound n hnpos
    have hnpow : (n : ℝ) ^ rho ≤ (2 * N) ^ rho :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) hnrange.2 hrho.le
    calc
      |(beta n).im| ≤ ‖beta n‖ := Complex.abs_im_le_norm _
      _ ≤ A * (divisorCount n : ℝ) ^ B := hnorm
      _ ≤ A * (D * (n : ℝ) ^ rho) :=
        mul_le_mul_of_nonneg_left hdiv hA0
      _ ≤ A * (D * (2 * N) ^ rho) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hnpow hD0) hA0
      _ = A * D * (2 * N) ^ rho := by ring

/-- Family-uniform form of the componentwise dyadic-supremum bound.

The divisor-subpower witness `D` is selected from the fixed exponents
`B,rho` before the coefficient sequence.  Thus the same `D` controls every
member of a moving family whose divisor-bound witnesses `B,A` are common. -/
theorem beta_parts_dyadicSup_subpower_uniform
    (hglobal : Hybrid.GlobalDivisorSubpowerStatement)
    {B A rho : ℝ} (hB : 0 ≤ B) (hA : 0 < A) (hrho : 0 < rho) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (beta : ℕ → ℂ),
      IsDivisorBoundedByConstant B A beta →
      ∀ N : ℝ, 1 ≤ N →
        dyadicRealCoefficientSup (fun n ↦ (beta n).re) N ≤
            A * D * (2 * N) ^ rho ∧
        dyadicRealCoefficientSup (fun n ↦ (beta n).im) N ≤
            A * D * (2 * N) ^ rho := by
  obtain ⟨D, hD, hDbound⟩ := hglobal B rho hB hrho
  refine ⟨D, hD, ?_⟩
  intro beta hbeta N hN
  have hN0 : 0 ≤ N := by linarith
  have hA0 : 0 ≤ A := hA.le
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hK0 : 0 ≤ A * D * (2 * N) ^ rho := by positivity
  constructor
  · apply dyadicRealCoefficientSup_le hK0
    intro n hn
    have hnrange := (mem_dyadicInterval hN0).mp hn
    have hnpos : 0 < n := by
      have : (0 : ℝ) < n := lt_of_le_of_lt hN0 hnrange.1
      exact_mod_cast this
    have hnorm := hbeta.2.2 n hnpos
    have hdiv := hDbound n hnpos
    have hnpow : (n : ℝ) ^ rho ≤ (2 * N) ^ rho :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) hnrange.2 hrho.le
    calc
      |(beta n).re| ≤ ‖beta n‖ := Complex.abs_re_le_norm _
      _ ≤ A * (divisorCount n : ℝ) ^ B := hnorm
      _ ≤ A * (D * (n : ℝ) ^ rho) :=
        mul_le_mul_of_nonneg_left hdiv hA0
      _ ≤ A * (D * (2 * N) ^ rho) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hnpow hD0) hA0
      _ = A * D * (2 * N) ^ rho := by ring
  · apply dyadicRealCoefficientSup_le hK0
    intro n hn
    have hnrange := (mem_dyadicInterval hN0).mp hn
    have hnpos : 0 < n := by
      have : (0 : ℝ) < n := lt_of_le_of_lt hN0 hnrange.1
      exact_mod_cast this
    have hnorm := hbeta.2.2 n hnpos
    have hdiv := hDbound n hnpos
    have hnpow : (n : ℝ) ^ rho ≤ (2 * N) ^ rho :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) hnrange.2 hrho.le
    calc
      |(beta n).im| ≤ ‖beta n‖ := Complex.abs_im_le_norm _
      _ ≤ A * (divisorCount n : ℝ) ^ B := hnorm
      _ ≤ A * (D * (n : ℝ) ^ rho) :=
        mul_le_mul_of_nonneg_left hdiv hA0
      _ ≤ A * (D * (2 * N) ^ rho) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hnpow hD0) hA0
      _ = A * D * (2 * N) ^ rho := by ring

/-- Uniform coefficient-loss absorption for a moving family.

The eventual threshold depends only on the fixed divisor witnesses, the two
source constants, and `delta`; it is independent of `beta` and of the dyadic
scale `N`.  This is the quantifier order furnished by Proposition 2.2, whose
`Bcoeff,Acoeff` are fixed before the principal scale and the decomposition
family. -/
theorem eventually_four_weighted_beta_parts_dyadicSup_sq_le_rpow_uniform
    (hglobal : Hybrid.GlobalDivisorSubpowerStatement)
    {B A CRe CIm delta : ℝ}
    (hdelta : 0 < delta) (hB : 0 ≤ B) (hA : 0 < A)
    (hCRe : 0 ≤ CRe) (hCIm : 0 ≤ CIm) :
    ∀ᶠ X : ℝ in atTop, ∀ (beta : ℕ → ℂ) (N : ℝ),
      IsDivisorBoundedByConstant B A beta →
      1 ≤ N → N ≤ X →
      4 * (CRe *
          (dyadicRealCoefficientSup (fun n ↦ (beta n).re) N) ^
            (2 : ℕ) +
        CIm *
          (dyadicRealCoefficientSup (fun n ↦ (beta n).im) N) ^
            (2 : ℕ)) ≤
        X ^ delta := by
  let rho : ℝ := delta / 4
  have hrho : 0 < rho := by dsimp [rho]; positivity
  obtain ⟨D, hD, hsup⟩ :=
    beta_parts_dyadicSup_subpower_uniform hglobal hB hA hrho
  let L : ℝ := A * D * (2 : ℝ) ^ rho
  let K : ℝ := (4 * CRe + 4 * CIm) * L ^ (2 : ℕ)
  have hhalf : 0 < delta / 2 := by positivity
  have heventK : ∀ᶠ X : ℝ in atTop,
      K ≤ X ^ (delta / 2) :=
    (tendsto_rpow_atTop hhalf).eventually_ge_atTop K
  filter_upwards [heventK, eventually_ge_atTop (1 : ℝ)] with X hK hX
  intro beta N hbeta hN hNX
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hA0 : 0 ≤ A := hA.le
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hL0 : 0 ≤ L := by
    dsimp [L]
    positivity
  have hNXpow : N ^ rho ≤ X ^ rho :=
    Real.rpow_le_rpow hN0 hNX hrho.le
  have hscale : A * D * (2 * N) ^ rho ≤ L * X ^ rho := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hN0]
    dsimp [L]
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hNXpow
        (mul_nonneg (mul_nonneg hA0 hD0)
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) rho)))
  rcases hsup beta hbeta N hN with ⟨hRe, hIm⟩
  have hRe' :
      dyadicRealCoefficientSup (fun n ↦ (beta n).re) N ≤
        L * X ^ rho := hRe.trans hscale
  have hIm' :
      dyadicRealCoefficientSup (fun n ↦ (beta n).im) N ≤
        L * X ^ rho := hIm.trans hscale
  have hRe0 :
      0 ≤ dyadicRealCoefficientSup (fun n ↦ (beta n).re) N := by
    unfold dyadicRealCoefficientSup
    positivity
  have hIm0 :
      0 ≤ dyadicRealCoefficientSup (fun n ↦ (beta n).im) N := by
    unfold dyadicRealCoefficientSup
    positivity
  have hReSq := pow_le_pow_left₀ hRe0 hRe' 2
  have hImSq := pow_le_pow_left₀ hIm0 hIm' 2
  have hweighted :
      4 * CRe *
          (dyadicRealCoefficientSup (fun n ↦ (beta n).re) N) ^
            (2 : ℕ) +
        4 * CIm *
          (dyadicRealCoefficientSup (fun n ↦ (beta n).im) N) ^
            (2 : ℕ) ≤
        K * X ^ (delta / 2) := by
    calc
      4 * CRe *
            (dyadicRealCoefficientSup (fun n ↦ (beta n).re) N) ^
              (2 : ℕ) +
          4 * CIm *
            (dyadicRealCoefficientSup (fun n ↦ (beta n).im) N) ^
              (2 : ℕ) ≤
          4 * CRe * (L * X ^ rho) ^ (2 : ℕ) +
            4 * CIm * (L * X ^ rho) ^ (2 : ℕ) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hReSq (by positivity))
          (mul_le_mul_of_nonneg_left hImSq (by positivity))
      _ = K * X ^ (delta / 2) := by
        have hpow : (X ^ rho) ^ (2 : ℕ) =
            X ^ (delta / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
          congr 1
          dsimp [rho]
          ring
        simp only [mul_pow, hpow]
        dsimp [K]
        ring
  calc
    4 * (CRe *
          (dyadicRealCoefficientSup (fun n ↦ (beta n).re) N) ^
            (2 : ℕ) +
        CIm *
          (dyadicRealCoefficientSup (fun n ↦ (beta n).im) N) ^
            (2 : ℕ)) =
        4 * CRe *
            (dyadicRealCoefficientSup (fun n ↦ (beta n).re) N) ^
              (2 : ℕ) +
          4 * CIm *
            (dyadicRealCoefficientSup (fun n ↦ (beta n).im) N) ^
              (2 : ℕ) := by ring
    _ ≤ K * X ^ (delta / 2) := hweighted
    _ ≤ X ^ (delta / 2) * X ^ (delta / 2) :=
      mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hXpos.le _)
    _ = X ^ delta := by
      rw [← Real.rpow_add hXpos]
      congr 1
      ring

/-- Fixed nonnegative weights and both component suprema are absorbed into an
arbitrarily small power of the ambient height, uniformly for `1≤N≤X`.
The divisor-bound witnesses remain outside the eventual quantifier. -/
theorem eventually_weighted_beta_parts_dyadicSup_sq_le_natCast_rpow
    (hglobal : Hybrid.GlobalDivisorSubpowerStatement)
    {beta : ℕ → ℂ} {B A delta CRe CIm : ℝ}
    (hdelta : 0 < delta)
    (hCRe : 0 ≤ CRe) (hCIm : 0 ≤ CIm)
    (hbeta : IsDivisorBoundedByConstant B A beta) :
    ∀ᶠ X : ℕ in atTop, ∀ N : ℝ, 1 ≤ N → N ≤ (X : ℝ) →
      CRe *
          (dyadicRealCoefficientSup (fun n ↦ (beta n).re) N) ^
            (2 : ℕ) +
        CIm *
          (dyadicRealCoefficientSup (fun n ↦ (beta n).im) N) ^
            (2 : ℕ) ≤
        (X : ℝ) ^ delta := by
  let rho : ℝ := delta / 4
  have hrho : 0 < rho := by dsimp [rho]; positivity
  obtain ⟨D, hD, hsup⟩ :=
    beta_parts_dyadicSup_subpower hglobal hrho hbeta
  let L : ℝ := A * D * (2 : ℝ) ^ rho
  let K : ℝ := (CRe + CIm) * L ^ (2 : ℕ)
  have hhalf : 0 < delta / 2 := by positivity
  have heventK : ∀ᶠ X : ℕ in atTop,
      K ≤ (X : ℝ) ^ (delta / 2) :=
    Hybrid.eventually_const_le_natCast_rpow K hhalf
  have heventOne : ∀ᶠ X : ℕ in atTop, 1 ≤ X :=
    Filter.eventually_atTop.2 ⟨1, fun _ h ↦ h⟩
  filter_upwards [heventK, heventOne] with X hK hX
  intro N hN hNX
  have hXreal : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < X := zero_lt_one.trans_le hXreal
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hA0 : 0 ≤ A := hbeta.2.1.le
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hL0 : 0 ≤ L := by
    dsimp [L]
    positivity
  have hNXpow : N ^ rho ≤ (X : ℝ) ^ rho :=
    Real.rpow_le_rpow hN0 hNX hrho.le
  have hscale : A * D * (2 * N) ^ rho ≤
      L * (X : ℝ) ^ rho := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hN0]
    dsimp [L]
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hNXpow
        (mul_nonneg (mul_nonneg hA0 hD0)
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) rho)))
  rcases hsup N hN with ⟨hRe, hIm⟩
  have hRe' :
      dyadicRealCoefficientSup (fun n ↦ (beta n).re) N ≤
        L * (X : ℝ) ^ rho := hRe.trans hscale
  have hIm' :
      dyadicRealCoefficientSup (fun n ↦ (beta n).im) N ≤
        L * (X : ℝ) ^ rho := hIm.trans hscale
  have hRe0 :
      0 ≤ dyadicRealCoefficientSup (fun n ↦ (beta n).re) N := by
    unfold dyadicRealCoefficientSup
    positivity
  have hIm0 :
      0 ≤ dyadicRealCoefficientSup (fun n ↦ (beta n).im) N := by
    unfold dyadicRealCoefficientSup
    positivity
  have htarget0 : 0 ≤ L * (X : ℝ) ^ rho := by positivity
  have hReSq := pow_le_pow_left₀ hRe0 hRe' 2
  have hImSq := pow_le_pow_left₀ hIm0 hIm' 2
  have hweighted :
      CRe *
          (dyadicRealCoefficientSup (fun n ↦ (beta n).re) N) ^
            (2 : ℕ) +
        CIm *
          (dyadicRealCoefficientSup (fun n ↦ (beta n).im) N) ^
            (2 : ℕ) ≤
        K * (X : ℝ) ^ (delta / 2) := by
    calc
      CRe *
            (dyadicRealCoefficientSup (fun n ↦ (beta n).re) N) ^
              (2 : ℕ) +
          CIm *
            (dyadicRealCoefficientSup (fun n ↦ (beta n).im) N) ^
              (2 : ℕ) ≤
          CRe * (L * (X : ℝ) ^ rho) ^ (2 : ℕ) +
            CIm * (L * (X : ℝ) ^ rho) ^ (2 : ℕ) :=
        add_le_add
          (mul_le_mul_of_nonneg_left hReSq hCRe)
          (mul_le_mul_of_nonneg_left hImSq hCIm)
      _ = K * (X : ℝ) ^ (delta / 2) := by
        have hpow : ((X : ℝ) ^ rho) ^ (2 : ℕ) =
            (X : ℝ) ^ (delta / 2) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
          congr 1
          dsimp [rho]
          ring
        simp only [mul_pow, hpow]
        dsimp [K]
        ring
  refine hweighted.trans ?_
  calc
    K * (X : ℝ) ^ (delta / 2) ≤
        (X : ℝ) ^ (delta / 2) * (X : ℝ) ^ (delta / 2) :=
      mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hXpos.le _)
    _ = (X : ℝ) ^ delta := by
      rw [← Real.rpow_add hXpos]
      congr 1
      ring

/-- Unweighted form used when the source constants have been absorbed
separately. -/
theorem eventually_beta_parts_dyadicSup_sq_add_sq_le_natCast_rpow
    (hglobal : Hybrid.GlobalDivisorSubpowerStatement)
    {beta : ℕ → ℂ} {B A delta : ℝ}
    (hdelta : 0 < delta)
    (hbeta : IsDivisorBoundedByConstant B A beta) :
    ∀ᶠ X : ℕ in atTop, ∀ N : ℝ, 1 ≤ N → N ≤ (X : ℝ) →
      (dyadicRealCoefficientSup (fun n ↦ (beta n).re) N) ^ (2 : ℕ) +
        (dyadicRealCoefficientSup (fun n ↦ (beta n).im) N) ^
          (2 : ℕ) ≤
      (X : ℝ) ^ delta := by
  simpa using eventually_weighted_beta_parts_dyadicSup_sq_le_natCast_rpow
    hglobal hdelta (CRe := (1 : ℝ)) (CIm := (1 : ℝ))
      (by norm_num) (by norm_num) hbeta

/-- Form with the normalization factor four appearing in the complex first
branch already absorbed into the two fixed real/imaginary constants. -/
theorem eventually_four_weighted_beta_parts_dyadicSup_sq_le_natCast_rpow
    (hglobal : Hybrid.GlobalDivisorSubpowerStatement)
    {beta : ℕ → ℂ} {B A CRe CIm delta : ℝ}
    (hdelta : 0 < delta) (hCRe : 0 ≤ CRe) (hCIm : 0 ≤ CIm)
    (hbeta : IsDivisorBoundedByConstant B A beta) :
    ∀ᶠ X : ℕ in atTop, ∀ N : ℝ, 1 ≤ N → N ≤ (X : ℝ) →
      4 * (CRe *
          (dyadicRealCoefficientSup (fun n ↦ (beta n).re) N) ^
            (2 : ℕ) +
        CIm *
          (dyadicRealCoefficientSup (fun n ↦ (beta n).im) N) ^
            (2 : ℕ)) ≤
      (X : ℝ) ^ delta := by
  have h := eventually_weighted_beta_parts_dyadicSup_sq_le_natCast_rpow
    hglobal hdelta (CRe := 4 * CRe) (CIm := 4 * CIm)
      (by positivity) (by positivity) hbeta
  filter_upwards [h] with X hX
  intro N hN hNX
  have := hX N hN hNX
  nlinarith

/-! ## The literal structured product scale -/

/-- The exact lower product inequality in the structured Type-II case gives
the complementary scale after division by the first scale. -/
theorem complement_lower_of_structured_product
    {X P M1 M2 : ℝ}
    (hP : 0 < P) (hM1 : 0 < M1)
    (hprod : X / (2 * P) ≤ M1 * M2) :
    X / M1 / (2 * P) ≤ M2 := by
  have hden : 0 < 2 * P := mul_pos (by norm_num) hP
  have hdiv : X / (2 * P) / M1 ≤ M2 := by
    apply (div_le_iff₀ hM1).2
    calc
      X / (2 * P) ≤ M1 * M2 := hprod
      _ = M2 * M1 := by ring
  calc
    X / M1 / (2 * P) = X / (2 * P) / M1 := by
      field_simp [ne_of_gt hden, ne_of_gt hM1]
    _ ≤ M2 := hdiv

/-- The preceding bound in the paper's logarithmic exponent coordinates. -/
theorem complement_lower_of_structured_product_logarithmic
    {X P M1 M2 theta : ℝ}
    (hX : 1 < X) (hP : 0 < P) (hM1 : 0 < M1)
    (htheta : Real.log M1 / Real.log X = theta)
    (hprod : X / (2 * P) ≤ M1 * M2) :
    X ^ (1 - theta) / (2 * P) ≤ M2 := by
  have hM1eq : M1 = X ^ theta := by
    have h := Hybrid.eq_rpow_logarithmicLengthExponent hX hM1
    rw [Hybrid.logarithmicLengthExponent, htheta] at h
    exact h
  have hbase := complement_lower_of_structured_product hP hM1 hprod
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hpow : X / M1 = X ^ (1 - theta) := by
    calc
      X / M1 = X / X ^ theta := by rw [hM1eq]
      _ = X ^ (1 : ℝ) / X ^ theta := by rw [Real.rpow_one]
      _ = X ^ (1 - theta) := (Real.rpow_sub hXpos 1 theta).symm
  rwa [hpow] at hbase

/-- The literal source relation `X/(2P)<M1*M2≤4X/P`, after inserting
`P=(log X)^a`; this is the rigorous content of `(X/P)(log X)^{O(1)}` here. -/
theorem structured_product_log_window
    {X P M1 M2 a : ℝ}
    (hPdef : P = (Real.log X) ^ a)
    (hlower : X / (2 * P) < M1 * M2)
    (hupper : M1 * M2 ≤ 4 * X / P) :
    X / (2 * (Real.log X) ^ a) < M1 * M2 ∧
      M1 * M2 ≤ 4 * X / (Real.log X) ^ a := by
  simpa only [hPdef] using And.intro hlower hupper

/-- Fixed logarithmic powers and fixed constants are absorbed by every
positive power of the principal scale. -/
theorem eventually_two_mul_log_rpow_le_rpow
    {a delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ X : ℝ in atTop,
      2 * (Real.log X) ^ a ≤ X ^ delta := by
  have hlog := TypeII.eventually_log_rpow_le_rpow a (half_pos hdelta)
  have htwo := (tendsto_rpow_atTop (half_pos hdelta)).eventually
    (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hlog, htwo, eventually_gt_atTop (1 : ℝ)] with
      X hlogX htwoX hX
  have hnonneg : 0 ≤ (Real.log X) ^ a :=
    Real.rpow_nonneg (Real.log_nonneg hX.le) _
  calc
    2 * (Real.log X) ^ a ≤ X ^ (delta / 2) * X ^ (delta / 2) :=
      mul_le_mul htwoX hlogX hnonneg
        (Real.rpow_nonneg (by positivity) _)
    _ = X ^ delta := by
      rw [← Real.rpow_add (by positivity : 0 < X)]
      congr 1
      ring

/-- After spending `delta` in the exponent, the literal structured-product
lower bound supplies the ideal complementary power. -/
theorem eventually_complement_lower_rpow
    {a delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ X : ℝ in atTop, ∀ P M1 M2 theta : ℝ,
      1 < X → P = (Real.log X) ^ a → 0 < M1 →
      X / (2 * P) ≤ M1 * M2 →
      Real.log M1 / Real.log X = theta →
      X ^ (1 - theta - delta) ≤ M2 := by
  filter_upwards [eventually_two_mul_log_rpow_le_rpow
      (a := a) hdelta] with X habsorb
  intro P M1 M2 theta hX hP hM1 hprod htheta
  have hPpos : 0 < P := by
    rw [hP]
    exact Real.rpow_pos_of_pos (Real.log_pos hX) _
  have hcomp := complement_lower_of_structured_product_logarithmic
    hX hPpos hM1 htheta hprod
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hdenpos : 0 < 2 * P := mul_pos (by norm_num) hPpos
  have habsorb' : 2 * P ≤ X ^ delta := by
    simpa [hP] using habsorb
  calc
    X ^ (1 - theta - delta) = X ^ (1 - theta) / X ^ delta := by
      rw [Real.rpow_sub hXpos]
    _ ≤ X ^ (1 - theta) / (2 * P) := by
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hXpos.le _)
        hdenpos habsorb'
    _ ≤ M2 := hcomp

/-- The actual second factor may replace the ideal power `X^(1-theta)`.
Only a fixed lower threshold for `sigma2` is used; no upper bound on the
moving magnitude-bin exponent is needed. -/
theorem actual_second_factor_lower_of_threshold
    {X M2 theta delta sigmaLower sigma2 : ℝ}
    (hX : 1 ≤ X) (hdeltaTheta : delta ≤ 1 - theta)
    (hM2 : X ^ (1 - theta - delta) ≤ M2)
    (hsigmaLower : 0 ≤ sigmaLower)
    (hsigma2 : sigmaLower ≤ sigma2) :
    (X ^ (1 - theta - delta)) ^ (2 * sigmaLower) ≤
      M2 ^ (2 * sigma2) := by
  have hbaseOne : 1 ≤ X ^ (1 - theta - delta) :=
    Real.one_le_rpow hX (by linarith)
  have hM2one : 1 ≤ M2 := hbaseOne.trans hM2
  calc
    (X ^ (1 - theta - delta)) ^ (2 * sigmaLower) ≤
        M2 ^ (2 * sigmaLower) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hM2
        (mul_nonneg (by norm_num) hsigmaLower)
    _ ≤ M2 ^ (2 * sigma2) :=
      Real.rpow_le_rpow_of_exponent_le hM2one (by linarith)

/-- End-to-end product-scale bridge.  A positive exponent reserve pays for
the constant and logarithmic factor in the literal source product range. -/
theorem eventually_structured_product_keyError_bridge
    {a spentError sigmaLower : ℝ}
    (hspent : 0 < spentError) (hsigmaLower : 0 ≤ sigmaLower) :
    ∀ᶠ X : ℝ in atTop,
      ∀ P M1 M2 theta sigma1 sigma2 keyExponent : ℝ,
      1 < X → P = (Real.log X) ^ a → 0 < M1 →
      X / (2 * P) ≤ M1 * M2 →
      Real.log M1 / Real.log X = theta →
      spentError ≤ 1 - theta → sigmaLower ≤ sigma2 →
      keyExponent + 2 * sigmaLower * spentError ≤
        (5 - 8 * sigma1) * theta +
          2 * sigmaLower * (1 - theta) →
      X ^ keyExponent ≤
        M1 ^ (5 - 8 * sigma1) * M2 ^ (2 * sigma2) := by
  filter_upwards [eventually_complement_lower_rpow
      (a := a) hspent] with X hcomp
  intro P M1 M2 theta sigma1 sigma2 keyExponent hX hP hM1 hprod
    htheta hspentTheta hsigma2 hkey
  have hM1eq : M1 = X ^ theta := by
    have h := Hybrid.eq_rpow_logarithmicLengthExponent hX hM1
    rw [Hybrid.logarithmicLengthExponent, htheta] at h
    exact h
  have hM2lower := hcomp P M1 M2 theta hX hP hM1 hprod htheta
  have hsecond := actual_second_factor_lower_of_threshold hX.le hspentTheta
    hM2lower hsigmaLower hsigma2
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hpower :
      X ^ keyExponent ≤
        (X ^ theta) ^ (5 - 8 * sigma1) *
          (X ^ (1 - theta - spentError)) ^ (2 * sigmaLower) := by
    rw [← Real.rpow_mul hXpos.le, ← Real.rpow_mul hXpos.le,
      ← Real.rpow_add hXpos]
    apply Real.rpow_le_rpow_of_exponent_le hX.le
    nlinarith
  calc
    X ^ keyExponent ≤
        (X ^ theta) ^ (5 - 8 * sigma1) *
          (X ^ (1 - theta - spentError)) ^ (2 * sigmaLower) := hpower
    _ ≤ (X ^ theta) ^ (5 - 8 * sigma1) *
        M2 ^ (2 * sigma2) := by
      exact mul_le_mul_of_nonneg_left hsecond
        (Real.rpow_nonneg (Real.rpow_nonneg hXpos.le _) _)
    _ = M1 ^ (5 - 8 * sigma1) * M2 ^ (2 * sigma2) := by
      rw [hM1eq]

/-- Endpoint algebra with the explicit extra reserve required to replace the
ideal complementary scale by the literal source scale. -/
theorem endpointKeyInequality_with_product_spend
    {a s sigma1 theta residualError sigmaError targetError
      spentError : ℝ}
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (hsigma1 : s - sigmaError ≤ sigma1)
    (hres : 1 - 1 / a - residualError ≤
      theta * (1 - 2 * sigma1))
    (hbudget :
      1 / a + targetError +
          2 * (s - sigmaError) * spentError <
        5 * (1 - 1 / a - residualError) +
          2 * (s - sigmaError)) :
    1 / a + targetError + 2 * (s - sigmaError) * spentError ≤
      (5 - 8 * sigma1) * theta +
        2 * (s - sigmaError) * (1 - theta) := by
  have h := endpointKeyInequality_with_errors
    (a := a) (s := s) (σ₁ := sigma1)
    (σ₂ := s - sigmaError) (θ := theta)
    (residualError := residualError) (sigmaError := sigmaError)
    (keyError := targetError + 2 * (s - sigmaError) * spentError)
    htheta0 htheta1 hsigma1 le_rfl hres (by nlinarith)
  dsimp [secondBranchKeyExponent] at h
  simpa [add_assoc] using h.le

/-- Full source-scale substitution: the endpoint budget pays separately for
the desired analytic error and for the fixed logarithmic product loss. -/
theorem eventually_structured_product_endpoint_bridge
    {a s residualError sigmaError targetError spentError : ℝ}
    (hspent : 0 < spentError)
    (hsigmaLower : 0 ≤ s - sigmaError) :
    ∀ᶠ X : ℝ in atTop,
      ∀ P M1 M2 theta sigma1 sigma2 : ℝ,
        1 < X → P = (Real.log X) ^ a → 0 < M1 →
        X / (2 * P) ≤ M1 * M2 →
        Real.log M1 / Real.log X = theta →
        spentError ≤ 1 - theta →
        0 ≤ theta → theta ≤ 1 →
        s - sigmaError ≤ sigma1 →
        s - sigmaError ≤ sigma2 →
        1 - 1 / a - residualError ≤ theta * (1 - 2 * sigma1) →
        1 / a + targetError +
              2 * (s - sigmaError) * spentError <
            5 * (1 - 1 / a - residualError) +
              2 * (s - sigmaError) →
        X ^ (1 / a + targetError) ≤
          M1 ^ (5 - 8 * sigma1) * M2 ^ (2 * sigma2) := by
  have hbridge := eventually_structured_product_keyError_bridge
    (a := a) (spentError := spentError)
    (sigmaLower := s - sigmaError) hspent hsigmaLower
  filter_upwards [hbridge] with X hXbridge
  intro P M1 M2 theta sigma1 sigma2 hX hP hM1 hprod htheta
    hspentTheta htheta0 htheta1 hsigma1 hsigma2 hres hbudget
  apply hXbridge P M1 M2 theta sigma1 sigma2
    (1 / a + targetError) hX hP hM1 hprod htheta hspentTheta
      hsigma2
  exact endpointKeyInequality_with_product_spend htheta0 htheta1
    hsigma1 hres hbudget

/-- Reserve form: a pre-existing positive `keyError` pays for both the target
analytic exponent and the logarithmic product loss. -/
theorem eventually_structured_product_endpoint_bridge_of_keyError
    {a s residualError sigmaError targetError spentError keyError : ℝ}
    (hspent : 0 < spentError)
    (hsigmaLower : 0 ≤ s - sigmaError)
    (hspend : targetError +
        2 * (s - sigmaError) * spentError ≤ keyError) :
    ∀ᶠ X : ℝ in atTop,
      ∀ P M1 M2 theta sigma1 sigma2 : ℝ,
        1 < X → P = (Real.log X) ^ a → 0 < M1 →
        X / (2 * P) ≤ M1 * M2 →
        Real.log M1 / Real.log X = theta →
        spentError ≤ 1 - theta →
        0 ≤ theta → theta ≤ 1 →
        s - sigmaError ≤ sigma1 →
        s - sigmaError ≤ sigma2 →
        1 - 1 / a - residualError ≤ theta * (1 - 2 * sigma1) →
        1 / a + keyError <
            5 * (1 - 1 / a - residualError) +
              2 * (s - sigmaError) →
        X ^ (1 / a + targetError) ≤
          M1 ^ (5 - 8 * sigma1) * M2 ^ (2 * sigma2) := by
  have hmain := eventually_structured_product_endpoint_bridge
    (a := a) (s := s) (residualError := residualError)
    (sigmaError := sigmaError) (targetError := targetError)
    (spentError := spentError) hspent hsigmaLower
  filter_upwards [hmain] with X hXmain
  intro P M1 M2 theta sigma1 sigma2 hX hP hM1 hprod htheta
    hspentTheta htheta0 htheta1 hsigma1 hsigma2 hres hbudget
  apply hXmain P M1 M2 theta sigma1 sigma2 hX hP hM1 hprod htheta
    hspentTheta htheta0 htheta1 hsigma1 hsigma2 hres
  nlinarith

/-! ## Exact finite Type-II convolution factorization -/

def typeIIFirstSupport (delta M₁ : ℝ) (R : ℕ) : Finset ℕ :=
  natOpenClosedInterval M₁ ((1 + delta) ^ R * M₁)

def typeIISecondSupport (M₂ : ℝ) : Finset ℕ :=
  dyadicInterval M₂

def typeIIProductSupport (delta M₁ M₂ : ℝ) (R : ℕ) : Finset ℕ :=
  ((typeIIFirstSupport delta M₁ R).product
    (typeIISecondSupport M₂)).image fun p ↦ p.1 * p.2

def binaryConvolutionCoefficient
    (alpha beta : ℕ → ℂ) (S₁ S₂ : Finset ℕ) (n : ℕ) : ℂ :=
  ∑ p ∈ (S₁.product S₂).filter (fun p ↦ p.1 * p.2 = n),
    alpha p.1 * beta p.2

/-- A finite Dirichlet polynomial product equals the polynomial of the
corresponding binary convolution on the product-image support. -/
theorem dirichletPolynomial_mul_eq_binaryConvolution
    (alpha beta : ℕ → ℂ) (S₁ S₂ : Finset ℕ) (s : ℂ) :
    dirichletPolynomial alpha S₁ s * dirichletPolynomial beta S₂ s =
      dirichletPolynomial (binaryConvolutionCoefficient alpha beta S₁ S₂)
        ((S₁.product S₂).image fun p ↦ p.1 * p.2) s := by
  classical
  simp only [dirichletPolynomial]
  rw [Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  calc
    (∑ p ∈ S₁.product S₂,
        (alpha p.1 * (p.1 : ℂ) ^ (-s)) *
          (beta p.2 * (p.2 : ℂ) ^ (-s))) =
      ∑ p ∈ S₁.product S₂,
        (alpha p.1 * beta p.2) *
          ((p.1 * p.2 : ℕ) : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [show (((p.1 * p.2 : ℕ) : ℂ) ^ (-s)) =
          (p.1 : ℂ) ^ (-s) * (p.2 : ℂ) ^ (-s) by
        simpa only [Nat.cast_mul] using
          Complex.natCast_mul_natCast_cpow p.1 p.2 (-s)]
      ring
    _ = ∑ n ∈ (S₁.product S₂).image (fun p ↦ p.1 * p.2),
        ∑ p ∈ S₁.product S₂ with p.1 * p.2 = n,
          (alpha p.1 * beta p.2) *
            ((p.1 * p.2 : ℕ) : ℂ) ^ (-s) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (s := S₁.product S₂)
        (t := (S₁.product S₂).image (fun p ↦ p.1 * p.2))
        (g := fun p ↦ p.1 * p.2)
        (fun p hp ↦ Finset.mem_image.mpr ⟨p, hp, rfl⟩)
        (fun p ↦
          (alpha p.1 * beta p.2) *
            ((p.1 * p.2 : ℕ) : ℂ) ^ (-s))
    _ = ∑ n ∈ (S₁.product S₂).image (fun p ↦ p.1 * p.2),
        binaryConvolutionCoefficient alpha beta S₁ S₂ n *
          (n : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [binaryConvolutionCoefficient, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]

theorem mem_typeIIFirstSupport_iff
    {delta M₁ : ℝ} {R m : ℕ} (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) :
    m ∈ typeIIFirstSupport delta M₁ R ↔
      M₁ < (m : ℝ) ∧
        (m : ℝ) ≤ (1 + delta) ^ R * M₁ := by
  apply mem_natOpenClosedInterval hM₁.le
  exact mul_nonneg (pow_nonneg (by linarith) R) hM₁.le

theorem mem_typeIISecondSupport_iff
    {M₂ : ℝ} {m : ℕ} (hM₂ : 0 < M₂) :
    m ∈ typeIISecondSupport M₂ ↔ InDyadicRange M₂ m := by
  exact mem_dyadicInterval hM₂.le

def typeIIRangePairs
    (delta M₁ M₂ : ℝ) (R n : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (n + 1)).product
    (Finset.range (n + 1))).filter
      (fun p ↦ p.1 * p.2 = n ∧
        M₁ < (p.1 : ℝ) ∧
        (p.1 : ℝ) ≤ (1 + delta) ^ R * M₁ ∧
        InDyadicRange M₂ p.2)

def typeIISupportPairs
    (delta M₁ M₂ : ℝ) (R n : ℕ) : Finset (ℕ × ℕ) :=
  (((typeIIFirstSupport delta M₁ R).product
    (typeIISecondSupport M₂)).filter (fun p ↦ p.1 * p.2 = n))

theorem typeII_pair_filter_eq
    {delta M₁ M₂ : ℝ} {R n : ℕ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) :
    typeIIRangePairs delta M₁ M₂ R n =
      typeIISupportPairs delta M₁ M₂ R n := by
  classical
  ext p
  simp only [typeIIRangePairs, typeIISupportPairs]
  rw [Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨hpairs, hprod, hp₁low, hp₁up, hp₂⟩
    exact ⟨Finset.mem_product.mpr
      ⟨(mem_typeIIFirstSupport_iff hdelta hM₁).2 ⟨hp₁low, hp₁up⟩,
        (mem_typeIISecondSupport_iff hM₂).2 hp₂⟩, hprod⟩
  · rintro ⟨hpairs, hprod⟩
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hpairs
    have hp₁data := (mem_typeIIFirstSupport_iff hdelta hM₁).1 hp₁
    have hp₂data := (mem_typeIISecondSupport_iff hM₂).1 hp₂
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
      ⟨Finset.mem_range.mpr (by omega),
        Finset.mem_range.mpr (by omega)⟩,
      hprod, hp₁data.1, hp₁data.2, hp₂data⟩

theorem matomakiTeravainenTypeIIValue_eq_binaryConvolution
    {delta M₁ M₂ : ℝ} {R n : ℕ} {alpha beta : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) :
    matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta n =
      binaryConvolutionCoefficient alpha beta
        (typeIIFirstSupport delta M₁ R) (typeIISecondSupport M₂) n := by
  classical
  rw [matomakiTeravainenTypeIIValue, binaryConvolutionCoefficient]
  rw [← Finset.sum_product']
  change (∑ p ∈ (Finset.range (n + 1)).product
      (Finset.range (n + 1)),
      if p.1 * p.2 = n ∧
          M₁ < (p.1 : ℝ) ∧
          (p.1 : ℝ) ≤ (1 + delta) ^ R * M₁ ∧
          InDyadicRange M₂ p.2 then
        alpha p.1 * beta p.2
      else 0) = _
  rw [← Finset.sum_filter]
  change (∑ p ∈ typeIIRangePairs delta M₁ M₂ R n,
      alpha p.1 * beta p.2) = _
  rw [typeII_pair_filter_eq hdelta hM₁ hM₂]
  rfl

/-- Exact factorization of the finite polynomial generated by a source
Type-II component. -/
theorem matomakiTeravainenTypeII_polynomial_factorization
    {delta M₁ M₂ : ℝ} {R : ℕ} {alpha beta : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (s : ℂ) :
    dirichletPolynomial
        (matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta)
        (typeIIProductSupport delta M₁ M₂ R) s =
      dirichletPolynomial alpha (typeIIFirstSupport delta M₁ R) s *
        dyadicDirichletPolynomial beta M₂ s := by
  rw [dyadicDirichletPolynomial]
  symm
  calc
    dirichletPolynomial alpha (typeIIFirstSupport delta M₁ R) s *
          dirichletPolynomial beta (typeIISecondSupport M₂) s =
        dirichletPolynomial
          (binaryConvolutionCoefficient alpha beta
            (typeIIFirstSupport delta M₁ R) (typeIISecondSupport M₂))
          (((typeIIFirstSupport delta M₁ R).product
            (typeIISecondSupport M₂)).image fun p ↦ p.1 * p.2) s :=
      dirichletPolynomial_mul_eq_binaryConvolution _ _ _ _ s
    _ = dirichletPolynomial
          (matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta)
          (typeIIProductSupport delta M₁ M₂ R) s := by
      unfold dirichletPolynomial typeIIProductSupport
      apply Finset.sum_congr rfl
      intro n hn
      rw [matomakiTeravainenTypeIIValue_eq_binaryConvolution
        hdelta hM₁ hM₂]

/-- A component represented by the source Type-II convolution has the same
polynomial on the literal product support. -/
theorem representedTypeII_polynomial_factorization
    {delta M₁ M₂ : ℝ} {R : ℕ}
    {alpha beta f : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hf : ∀ n, f n =
      matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta n)
    (s : ℂ) :
    dirichletPolynomial f (typeIIProductSupport delta M₁ M₂ R) s =
      dirichletPolynomial alpha (typeIIFirstSupport delta M₁ R) s *
        dyadicDirichletPolynomial beta M₂ s := by
  calc
    dirichletPolynomial f (typeIIProductSupport delta M₁ M₂ R) s =
        dirichletPolynomial
          (matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta)
          (typeIIProductSupport delta M₁ M₂ R) s := by
      unfold dirichletPolynomial
      apply Finset.sum_congr rfl
      intro n hn
      rw [hf n]
    _ = _ := matomakiTeravainenTypeII_polynomial_factorization
      hdelta hM₁ hM₂ s

/-- A large-value lower bound for a represented source component transfers
directly to the product of its two factor norms. -/
theorem representedTypeII_factor_norm_product_lower
    {delta M₁ M₂ v : ℝ} {R : ℕ}
    {alpha beta f : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hf : ∀ n, f n =
      matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta n)
    {s : ℂ}
    (hlarge : v ≤
      ‖dirichletPolynomial f (typeIIProductSupport delta M₁ M₂ R) s‖) :
    v ≤ ‖dirichletPolynomial alpha
        (typeIIFirstSupport delta M₁ R) s‖ *
      ‖dyadicDirichletPolynomial beta M₂ s‖ := by
  rw [representedTypeII_polynomial_factorization hdelta hM₁ hM₂ hf,
    norm_mul] at hlarge
  exact hlarge

theorem typeIIFirstSupport_eq_dyadicFilter
    {delta M₁ : ℝ} {R : ℕ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁)
    (hupper : (1 + delta) ^ R ≤ 2) :
    typeIIFirstSupport delta M₁ R =
      (dyadicInterval M₁).filter (fun m : ℕ ↦
        M₁ < (m : ℝ) ∧
          (m : ℝ) ≤ (1 + delta) ^ R * M₁) := by
  classical
  ext m
  rw [mem_typeIIFirstSupport_iff hdelta hM₁, Finset.mem_filter]
  constructor
  · intro hm
    refine ⟨(mem_dyadicInterval hM₁.le).2 ⟨hm.1, ?_⟩, hm⟩
    exact hm.2.trans (mul_le_mul_of_nonneg_right hupper hM₁.le)
  · exact fun hm ↦ hm.2

/-- The actual structured first factor is exactly the real dyadic
coefficient polynomial consumed by the sparse package. -/
theorem structured_firstFactor_eq_realDyadic
    {delta M₁ : ℝ} {R : ℕ} {Q : Fin R → ℝ} {alpha : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁)
    (hupper : (1 + delta) ^ R ≤ 2)
    (halpha : ∀ m, alpha m =
      matomakiTeravainenStructuredTypeIICoefficient delta R Q m)
    (s : ℂ) :
    dirichletPolynomial alpha (typeIIFirstSupport delta M₁ R) s =
      dyadicDirichletPolynomial
        (fun m ↦
          (structuredTypeIIRealCoefficient delta M₁ R Q m : ℂ))
        M₁ s := by
  calc
    dirichletPolynomial alpha (typeIIFirstSupport delta M₁ R) s =
        dirichletPolynomial
          (matomakiTeravainenStructuredTypeIICoefficient delta R Q)
          (typeIIFirstSupport delta M₁ R) s := by
      unfold dirichletPolynomial
      apply Finset.sum_congr rfl
      intro m hm
      rw [halpha m]
    _ = dirichletPolynomial
          (matomakiTeravainenStructuredTypeIICoefficient delta R Q)
          ((dyadicInterval M₁).filter fun m : ℕ ↦
            M₁ < (m : ℝ) ∧
              (m : ℝ) ≤ (1 + delta) ^ R * M₁) s := by
      rw [← typeIIFirstSupport_eq_dyadicFilter hdelta hM₁ hupper]
    _ = dyadicDirichletPolynomial
          (fun m ↦
            (structuredTypeIIRealCoefficient delta M₁ R Q m : ℂ))
          M₁ s :=
      (dyadicPolynomial_structuredTypeIIRealCoefficient_eq s).symm

/-- Exact structured factorization in the normalization expected by
`sparsePropagation_fixedScale_package`. -/
theorem representedStructuredTypeII_polynomial_factorization
    {delta M₁ M₂ : ℝ} {R : ℕ} {Q : Fin R → ℝ}
    {alpha beta f : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hupper : (1 + delta) ^ R ≤ 2)
    (halpha : ∀ m, alpha m =
      matomakiTeravainenStructuredTypeIICoefficient delta R Q m)
    (hf : ∀ n, f n =
      matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta n)
    (s : ℂ) :
    dirichletPolynomial f (typeIIProductSupport delta M₁ M₂ R) s =
      dyadicDirichletPolynomial
          (fun m ↦
            (structuredTypeIIRealCoefficient delta M₁ R Q m : ℂ))
          M₁ s *
        dyadicDirichletPolynomial beta M₂ s := by
  rw [representedTypeII_polynomial_factorization hdelta hM₁ hM₂ hf,
    structured_firstFactor_eq_realDyadic hdelta hM₁ hupper halpha]

/-- A large value of an actual structured Type-II component transfers
directly to the product of the two dyadic factor norms. -/
theorem representedStructuredTypeII_factor_norm_product_lower
    {delta M₁ M₂ v : ℝ} {R : ℕ} {Q : Fin R → ℝ}
    {alpha beta f : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hupper : (1 + delta) ^ R ≤ 2)
    (halpha : ∀ m, alpha m =
      matomakiTeravainenStructuredTypeIICoefficient delta R Q m)
    (hf : ∀ n, f n =
      matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta n)
    {s : ℂ}
    (hlarge : v ≤
      ‖dirichletPolynomial f
        (typeIIProductSupport delta M₁ M₂ R) s‖) :
    v ≤
      ‖dyadicDirichletPolynomial
          (fun m ↦
            (structuredTypeIIRealCoefficient delta M₁ R Q m : ℂ))
          M₁ s‖ *
        ‖dyadicDirichletPolynomial beta M₂ s‖ := by
  rw [representedStructuredTypeII_polynomial_factorization
    hdelta hM₁ hM₂ hupper halpha hf, norm_mul] at hlarge
  exact hlarge

/-! ## Exact comparison with the ambient Perron support -/

/-- Every integer in the literal Type-II product support lies between the
product of the two base scales and the product of their upper endpoints. -/
theorem mem_typeIIProductSupport_bounds
    {delta M₁ M₂ : ℝ} {R n : ℕ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hn : n ∈ typeIIProductSupport delta M₁ M₂ R) :
    M₁ * M₂ < (n : ℝ) ∧
      (n : ℝ) ≤ 2 * (1 + delta) ^ R * (M₁ * M₂) := by
  classical
  rw [typeIIProductSupport, Finset.mem_image] at hn
  obtain ⟨p, hp, rfl⟩ := hn
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
  have hp₁data := (mem_typeIIFirstSupport_iff hdelta hM₁).1 hp₁
  have hp₂data := (mem_typeIISecondSupport_iff hM₂).1 hp₂
  have hp₁pos : 0 < (p.1 : ℝ) := hM₁.trans hp₁data.1
  have hp₂nonneg : 0 ≤ (p.2 : ℝ) := Nat.cast_nonneg _
  have hfirstNonneg : 0 ≤ (1 + delta) ^ R * M₁ :=
    mul_nonneg (pow_nonneg (by linarith) R) hM₁.le
  constructor
  · rw [Nat.cast_mul]
    calc
      M₁ * M₂ < (p.1 : ℝ) * M₂ :=
        mul_lt_mul_of_pos_right hp₁data.1 hM₂
      _ < (p.1 : ℝ) * (p.2 : ℝ) :=
        mul_lt_mul_of_pos_left hp₂data.1 hp₁pos
  · rw [Nat.cast_mul]
    calc
      (p.1 : ℝ) * (p.2 : ℝ) ≤
          ((1 + delta) ^ R * M₁) * (2 * M₂) :=
        mul_le_mul hp₁data.2 hp₂data.2 hp₂nonneg hfirstNonneg
      _ = 2 * (1 + delta) ^ R * (M₁ * M₂) := by ring

theorem binaryConvolutionCoefficient_eq_zero_of_not_mem_productSupport
    (alpha beta : ℕ → ℂ) (S₁ S₂ : Finset ℕ) (n : ℕ)
    (hn : n ∉ (S₁.product S₂).image fun p ↦ p.1 * p.2) :
    binaryConvolutionCoefficient alpha beta S₁ S₂ n = 0 := by
  classical
  rw [binaryConvolutionCoefficient]
  apply Finset.sum_eq_zero
  intro p hp
  have hprod := (Finset.mem_filter.mp hp).2
  exfalso
  apply hn
  exact Finset.mem_image.mpr ⟨p, (Finset.mem_filter.mp hp).1, hprod⟩

theorem matomakiTeravainenTypeIIValue_eq_zero_of_not_mem_productSupport
    {delta M₁ M₂ : ℝ} {R n : ℕ} {alpha beta : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hn : n ∉ typeIIProductSupport delta M₁ M₂ R) :
    matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta n = 0 := by
  rw [matomakiTeravainenTypeIIValue_eq_binaryConvolution hdelta hM₁ hM₂]
  exact binaryConvolutionCoefficient_eq_zero_of_not_mem_productSupport
    alpha beta _ _ n hn

theorem representedTypeII_eq_zero_of_not_mem_productSupport
    {delta M₁ M₂ : ℝ} {R n : ℕ} {alpha beta f : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hf : ∀ n, f n =
      matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta n)
    (hn : n ∉ typeIIProductSupport delta M₁ M₂ R) :
    f n = 0 := by
  rw [hf n]
  exact matomakiTeravainenTypeIIValue_eq_zero_of_not_mem_productSupport
    hdelta hM₁ hM₂ hn

theorem dirichletPolynomial_eq_inter_of_zero_outside
    {f : ℕ → ℂ} {S A : Finset ℕ} {s : ℂ}
    (hf : ∀ n, n ∉ S → f n = 0) :
    dirichletPolynomial f A s = dirichletPolynomial f (S ∩ A) s := by
  unfold dirichletPolynomial
  symm
  apply Finset.sum_subset Finset.inter_subset_right
  intro n hnA hnInter
  have hnS : n ∉ S := by
    intro hnS
    exact hnInter (Finset.mem_inter.mpr ⟨hnS, hnA⟩)
  simp [hf n hnS]

theorem representedTypeII_ambientPolynomial_eq_inter
    {delta M₁ M₂ Y : ℝ} {R : ℕ} {alpha beta f : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (_hY : 0 ≤ Y)
    (hf : ∀ n, f n =
      matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta n)
    (s : ℂ) :
    dirichletPolynomial f (natOpenClosedInterval (Y / 2) (4 * Y)) s =
      dirichletPolynomial f
        (typeIIProductSupport delta M₁ M₂ R ∩
          natOpenClosedInterval (Y / 2) (4 * Y)) s := by
  apply dirichletPolynomial_eq_inter_of_zero_outside
  intro n hn
  exact representedTypeII_eq_zero_of_not_mem_productSupport
    hdelta hM₁ hM₂ hf hn

/-- Once the source scale lower bound `Y/2 < M₁M₂` is imposed, the
ambient cutoff only removes the upper tail of the literal product support. -/
theorem typeIIProductSupport_inter_ambient_eq_upperFilter
    {delta M₁ M₂ Y : ℝ} {R : ℕ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hY : 0 ≤ Y) (hproductLower : Y / 2 < M₁ * M₂) :
    typeIIProductSupport delta M₁ M₂ R ∩
        natOpenClosedInterval (Y / 2) (4 * Y) =
      (typeIIProductSupport delta M₁ M₂ R).filter
        (fun n : ℕ ↦ (n : ℝ) ≤ 4 * Y) := by
  classical
  ext n
  rw [Finset.mem_inter, Finset.mem_filter,
    mem_natOpenClosedInterval (by positivity) (by positivity)]
  constructor
  · exact fun hn ↦ ⟨hn.1, hn.2.2⟩
  · rintro ⟨hn, hnUpper⟩
    have hnBounds := mem_typeIIProductSupport_bounds
      hdelta hM₁ hM₂ hn
    exact ⟨hn, hproductLower.trans hnBounds.1, hnUpper⟩

/-- The ambient Perron polynomial is exactly the upper-truncated Type-II
product polynomial.  This is the strongest unconditional support bridge
available from the source scale inequalities. -/
theorem representedTypeII_ambientPolynomial_eq_upperFilter
    {delta M₁ M₂ Y : ℝ} {R : ℕ} {alpha beta f : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hY : 0 ≤ Y) (hproductLower : Y / 2 < M₁ * M₂)
    (hf : ∀ n, f n =
      matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta n)
    (s : ℂ) :
    dirichletPolynomial f (natOpenClosedInterval (Y / 2) (4 * Y)) s =
      dirichletPolynomial f
        ((typeIIProductSupport delta M₁ M₂ R).filter
          (fun n : ℕ ↦ (n : ℝ) ≤ 4 * Y)) s := by
  rw [representedTypeII_ambientPolynomial_eq_inter
    hdelta hM₁ hM₂ hY hf s,
    typeIIProductSupport_inter_ambient_eq_upperFilter
      hdelta hM₁ hM₂ hY hproductLower]

/-- Exact correction to the naïve factorization: ambient polynomial plus
the omitted upper tail equals the full product of the two factors. -/
theorem representedTypeII_ambient_add_upperTail_eq_factorization
    {delta M₁ M₂ Y : ℝ} {R : ℕ} {alpha beta f : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hY : 0 ≤ Y) (hproductLower : Y / 2 < M₁ * M₂)
    (hf : ∀ n, f n =
      matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta n)
    (s : ℂ) :
    dirichletPolynomial f (natOpenClosedInterval (Y / 2) (4 * Y)) s +
        dirichletPolynomial f
          ((typeIIProductSupport delta M₁ M₂ R).filter
            (fun n : ℕ ↦ 4 * Y < (n : ℝ))) s =
      dirichletPolynomial alpha (typeIIFirstSupport delta M₁ R) s *
        dyadicDirichletPolynomial beta M₂ s := by
  rw [representedTypeII_ambientPolynomial_eq_upperFilter
    hdelta hM₁ hM₂ hY hproductLower hf s]
  rw [← representedTypeII_polynomial_factorization
    hdelta hM₁ hM₂ hf s]
  unfold dirichletPolynomial
  simpa only [not_le] using
    Finset.sum_filter_add_sum_filter_not
      (typeIIProductSupport delta M₁ M₂ R)
      (fun n : ℕ ↦ (n : ℝ) ≤ 4 * Y)
      (fun n ↦ f n * (n : ℂ) ^ (-s))

/-- A lower bound for the ambient polynomial loses exactly the norm of its
omitted upper tail before it transfers to the two factor norms. -/
theorem representedTypeII_factor_norm_lower_up_to_upperTail
    {delta M₁ M₂ Y v : ℝ} {R : ℕ} {alpha beta f : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hY : 0 ≤ Y) (hproductLower : Y / 2 < M₁ * M₂)
    (hf : ∀ n, f n =
      matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta n)
    {s : ℂ}
    (hlarge : v ≤
      ‖dirichletPolynomial f
        (natOpenClosedInterval (Y / 2) (4 * Y)) s‖) :
    v - ‖dirichletPolynomial f
        ((typeIIProductSupport delta M₁ M₂ R).filter
          (fun n : ℕ ↦ 4 * Y < (n : ℝ))) s‖ ≤
      ‖dirichletPolynomial alpha (typeIIFirstSupport delta M₁ R) s‖ *
        ‖dyadicDirichletPolynomial beta M₂ s‖ := by
  let ambient := dirichletPolynomial f
    (natOpenClosedInterval (Y / 2) (4 * Y)) s
  let tail := dirichletPolynomial f
    ((typeIIProductSupport delta M₁ M₂ R).filter
      (fun n : ℕ ↦ 4 * Y < (n : ℝ))) s
  let product :=
    dirichletPolynomial alpha (typeIIFirstSupport delta M₁ R) s *
      dyadicDirichletPolynomial beta M₂ s
  have hfactor : ambient + tail = product := by
    exact representedTypeII_ambient_add_upperTail_eq_factorization
      hdelta hM₁ hM₂ hY hproductLower hf s
  have hambient : ambient = product - tail := by
    linear_combination hfactor
  have hnorm : ‖ambient‖ ≤ ‖product‖ + ‖tail‖ := by
    rw [hambient]
    exact norm_sub_le product tail
  rw [norm_mul] at hnorm
  dsimp only [ambient, tail, product] at hnorm
  linarith

/-- Structured specialization of the exact ambient-plus-tail identity in
the normalization consumed by sparse propagation. -/
theorem representedStructuredTypeII_ambient_add_upperTail_eq_factorization
    {delta M₁ M₂ Y : ℝ} {R : ℕ} {Q : Fin R → ℝ}
    {alpha beta f : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hY : 0 ≤ Y) (hproductLower : Y / 2 < M₁ * M₂)
    (hupper : (1 + delta) ^ R ≤ 2)
    (halpha : ∀ m, alpha m =
      matomakiTeravainenStructuredTypeIICoefficient delta R Q m)
    (hf : ∀ n, f n =
      matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta n)
    (s : ℂ) :
    dirichletPolynomial f (natOpenClosedInterval (Y / 2) (4 * Y)) s +
        dirichletPolynomial f
          ((typeIIProductSupport delta M₁ M₂ R).filter
            (fun n : ℕ ↦ 4 * Y < (n : ℝ))) s =
      dyadicDirichletPolynomial
          (fun m ↦
            (structuredTypeIIRealCoefficient delta M₁ R Q m : ℂ))
          M₁ s *
        dyadicDirichletPolynomial beta M₂ s := by
  calc
    _ = dirichletPolynomial alpha (typeIIFirstSupport delta M₁ R) s *
          dyadicDirichletPolynomial beta M₂ s :=
      representedTypeII_ambient_add_upperTail_eq_factorization
        hdelta hM₁ hM₂ hY hproductLower hf s
    _ = _ := by
      rw [structured_firstFactor_eq_realDyadic
        hdelta hM₁ hupper halpha s]

/-- Consequently, sparse propagation receives the ambient large value only
after paying the norm of the upper tail. -/
theorem representedStructuredTypeII_factor_norm_lower_up_to_upperTail
    {delta M₁ M₂ Y v : ℝ} {R : ℕ} {Q : Fin R → ℝ}
    {alpha beta f : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hY : 0 ≤ Y) (hproductLower : Y / 2 < M₁ * M₂)
    (hupper : (1 + delta) ^ R ≤ 2)
    (halpha : ∀ m, alpha m =
      matomakiTeravainenStructuredTypeIICoefficient delta R Q m)
    (hf : ∀ n, f n =
      matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta n)
    {s : ℂ}
    (hlarge : v ≤
      ‖dirichletPolynomial f
        (natOpenClosedInterval (Y / 2) (4 * Y)) s‖) :
    v - ‖dirichletPolynomial f
        ((typeIIProductSupport delta M₁ M₂ R).filter
          (fun n : ℕ ↦ 4 * Y < (n : ℝ))) s‖ ≤
      ‖dyadicDirichletPolynomial
          (fun m ↦
            (structuredTypeIIRealCoefficient delta M₁ R Q m : ℂ))
          M₁ s‖ *
        ‖dyadicDirichletPolynomial beta M₂ s‖ := by
  have hgeneric := representedTypeII_factor_norm_lower_up_to_upperTail
    hdelta hM₁ hM₂ hY hproductLower hf hlarge
  rw [structured_firstFactor_eq_realDyadic
    hdelta hM₁ hupper halpha s] at hgeneric
  exact hgeneric

/-- Under the genuinely stronger scale inequality that puts the whole
product box below `4Y`, the expected ambient factorization is valid. -/
theorem representedTypeII_ambientPolynomial_factorization_of_fullSupport
    {delta M₁ M₂ Y : ℝ} {R : ℕ} {alpha beta f : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hY : 0 ≤ Y) (hproductLower : Y / 2 < M₁ * M₂)
    (hproductUpper :
      2 * (1 + delta) ^ R * (M₁ * M₂) ≤ 4 * Y)
    (hf : ∀ n, f n =
      matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta n)
    (s : ℂ) :
    dirichletPolynomial f (natOpenClosedInterval (Y / 2) (4 * Y)) s =
      dirichletPolynomial alpha (typeIIFirstSupport delta M₁ R) s *
        dyadicDirichletPolynomial beta M₂ s := by
  rw [representedTypeII_ambientPolynomial_eq_inter
    hdelta hM₁ hM₂ hY hf s]
  have hinter :
      typeIIProductSupport delta M₁ M₂ R ∩
          natOpenClosedInterval (Y / 2) (4 * Y) =
        typeIIProductSupport delta M₁ M₂ R := by
    classical
    ext n
    rw [Finset.mem_inter]
    constructor
    · exact fun hn ↦ hn.1
    · intro hn
      have hnBounds := mem_typeIIProductSupport_bounds
        hdelta hM₁ hM₂ hn
      refine ⟨hn, (mem_natOpenClosedInterval
        (by positivity) (by positivity)).2 ⟨?_, ?_⟩⟩
      · exact hproductLower.trans hnBounds.1
      · exact hnBounds.2.trans hproductUpper
  rw [hinter]
  exact representedTypeII_polynomial_factorization
    hdelta hM₁ hM₂ hf s

/-- The literal inclusion needed for the naïve bridge is false even when
`(1+delta)^R ≤ 2` and the source scale obeys
`Y/2 < M₁M₂ ≤ 4Y`. -/
theorem typeIIProductSupport_not_subset_ambient_example :
    ¬ typeIIProductSupport (1 / 10 : ℝ) 10 40 1 ⊆
      natOpenClosedInterval 50 400 := by
  intro hsubset
  have hn : 880 ∈ typeIIProductSupport (1 / 10 : ℝ) 10 40 1 := by
    rw [typeIIProductSupport, Finset.mem_image]
    refine ⟨(11, 80), Finset.mem_product.mpr ⟨?_, ?_⟩, by norm_num⟩
    · exact (mem_typeIIFirstSupport_iff (by norm_num) (by norm_num)).2
        (by norm_num)
    · exact (mem_typeIISecondSupport_iff (by norm_num)).2
        ⟨by norm_num, by norm_num⟩
  have := hsubset hn
  have hrange := (mem_natOpenClosedInterval (by norm_num) (by norm_num)).1 this
  norm_num at hrange

/-- Uniform fixed-parameter support estimate for every dyadic-prime power
whose elementary upper-support geometry has been verified.  This is the
direct composition of the finite support containment with the cited
Hildebrand--Tenenbaum asymptotic; `P` and `k` may still vary with `X`. -/
theorem eventually_card_dyadicPrimePowerSupport_le_rpow_uniform
    (inputs : ExternalInputs) {a cutoffSlack powerSlack : ℝ}
    (ha : 1 < a) (hcutoffSlack : 0 < cutoffSlack)
    (hpowerSlack : 0 < powerSlack) :
    ∀ᶠ X : ℕ in Filter.atTop,
      ∀ (P : ℝ) (k : ℕ),
        P = (Real.log (X : ℝ)) ^ a →
        1 ≤ ⌊2 * P⌋₊ → ⌊2 * P⌋₊ ^ k ≤ X →
        ((primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
          (X : ℝ) ^
            (1 - 1 / (a + cutoffSlack) + powerSlack) := by
  have haSlack : 1 < a + cutoffSlack := by linarith
  have hcutReal :=
    eventually_floor_two_mul_log_rpow_le_floor_log_rpow_add
      a hcutoffSlack
  have hcutNat :
      ∀ᶠ X : ℕ in Filter.atTop,
        ⌊2 * (Real.log (X : ℝ)) ^ a⌋₊ ≤
          ⌊(Real.log (X : ℝ)) ^ (a + cutoffSlack)⌋₊ :=
    Filter.Tendsto.eventually tendsto_natCast_atTop_atTop hcutReal
  have hHT := eventually_logPowerSmoothNumberCount_le_rpow
    inputs.hildebrandTenenbaumCorollaryOneThree
    haSlack hpowerSlack
  filter_upwards [hcutNat, hHT, Filter.eventually_ge_atTop (2 : ℕ)] with
      X hcut hHTX hX P k hP hY hPower
  have hPnonneg : 0 ≤ P := by
    rw [hP]
    exact Real.rpow_nonneg
      (Real.log_nonneg (by
        exact_mod_cast (show 1 ≤ X by omega))) a
  have hcard := card_dyadicPrimePowerSupport_le_smoothNumberCount
    hPnonneg hY hPower
  have hcutP : ⌊2 * P⌋₊ ≤
      ⌊(Real.log (X : ℝ)) ^ (a + cutoffSlack)⌋₊ := by
    simpa [hP] using hcut
  have hmono := smoothNumberCount_mono_right (X := X) hcutP
  have hnat :
      (primePowerSupport (dyadicPrimes P) k).card ≤
        logPowerSmoothNumberCount (a + cutoffSlack) X := by
    exact hcard.trans hmono
  exact (by exact_mod_cast hnat :
    ((primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
      (logPowerSmoothNumberCount (a + cutoffSlack) X : ℝ)).trans hHTX

/-- The deletion condition actually used by both sparse mean-value calls.
The only numerical requirement is that the two chosen smooth-number slacks
keep the support exponent at most `1/3`. -/
theorem eventually_card_dyadicPrimePowerSupport_le_oneThird_uniform
    (inputs : ExternalInputs) {a cutoffSlack powerSlack : ℝ}
    (ha : 1 < a) (hcutoffSlack : 0 < cutoffSlack)
    (hpowerSlack : 0 < powerSlack)
    (hexponent :
      1 - 1 / (a + cutoffSlack) + powerSlack ≤ 1 / 3) :
    ∀ᶠ X : ℕ in Filter.atTop,
      ∀ (P : ℝ) (k : ℕ),
        P = (Real.log (X : ℝ)) ^ a →
        1 ≤ ⌊2 * P⌋₊ → ⌊2 * P⌋₊ ^ k ≤ X →
        ((primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
          (X : ℝ) ^ (1 / 3 : ℝ) := by
  have hmain := eventually_card_dyadicPrimePowerSupport_le_rpow_uniform
    inputs ha hcutoffSlack hpowerSlack
  filter_upwards [hmain, Filter.eventually_ge_atTop (1 : ℕ)] with
      X hbound hX P k hP hY hPower
  exact (hbound P k hP hY hPower).trans
    (Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hX : (1 : ℝ) ≤ X) hexponent)

/-- The explicit right side returned by the complex-coefficient first
Heath--Brown branch. -/
def firstBranchComplexMajorant
    (CRe CIm R M N T eta ARe AIm q v : ℝ) : ℝ :=
  (CRe *
      ((R / M) ^ (2 : ℕ) +
        (N * T) ^ eta * (R * T / (M ^ (2 : ℕ) * N))) *
      ARe ^ (2 : ℕ)) /
      (q ^ (2 : ℕ) * (v / 2) ^ (2 : ℕ)) +
    (CIm *
      ((R / M) ^ (2 : ℕ) +
        (N * T) ^ eta * (R * T / (M ^ (2 : ℕ) * N))) *
      AIm ^ (2 : ℕ)) /
      (q ^ (2 : ℕ) * (v / 2) ^ (2 : ℕ))

/-- The explicit five-block right side returned by the powered second
Heath--Brown branch. -/
def secondBranchFiveBlockMajorant
    (C D rho eta T sparseScale baseScale A0 R : ℝ) : ℝ :=
  5 * ∑ j ∈ Finset.range 5,
    C *
      (((R / sparseScale) ^ (2 : ℕ) +
        (((2 : ℝ) ^ j * baseScale ^ (5 : ℕ)) * T) ^ eta *
          (R * T /
            (sparseScale ^ (2 : ℕ) *
              ((2 : ℝ) ^ j * baseScale ^ (5 : ℕ))))) *
        (A0 ^ (5 : ℕ) * D *
          (2 * ((2 : ℝ) ^ j * baseScale ^ (5 : ℕ))) ^ rho) ^
            (2 : ℕ))

/-- Squaring a support bound and dividing by a squared power threshold
subtracts twice the threshold exponent. -/
theorem supportRatio_sq_div_rpow_sq_le
    {R M supportExponent thresholdExponent : ℝ}
    (hM : 0 < M) (hR : 0 ≤ R)
    (hRbound : R ≤ M ^ supportExponent) :
    (R / M) ^ (2 : ℕ) /
        (M ^ thresholdExponent) ^ (2 : ℕ) ≤
      M ^ (2 * (supportExponent - 1 - thresholdExponent)) := by
  have hratioNonneg : 0 ≤ R / M := div_nonneg hR hM.le
  have hratio : R / M ≤ M ^ (supportExponent - 1) := by
    calc
      R / M ≤ M ^ supportExponent / M :=
        div_le_div_of_nonneg_right hRbound hM.le
      _ = M ^ (supportExponent - 1) := by
        rw [Real.rpow_sub hM, Real.rpow_one]
  have hsquare := pow_le_pow_left₀ hratioNonneg hratio 2
  have hden : 0 < (M ^ thresholdExponent) ^ (2 : ℕ) := by
    positivity
  rw [div_le_iff₀ hden]
  calc
    (R / M) ^ (2 : ℕ) ≤
        (M ^ (supportExponent - 1)) ^ (2 : ℕ) := hsquare
    _ = M ^ (2 * (supportExponent - 1 - thresholdExponent)) *
          (M ^ thresholdExponent) ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_mul hM.le, ← Real.rpow_mul hM.le,
        ← Real.rpow_add hM]
      congr 1
      ring

theorem firstBranch_support_threshold_cancellation
    {R M a epsilon supportSlack : ℝ}
    (hM : 0 < M) (hR : 0 ≤ R)
    (hRbound : R ≤ M ^ (1 - 1 / a + supportSlack)) :
    (R / M) ^ (2 : ℕ) /
        (M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) ≤
      M ^ (epsilon / 5 + 2 * supportSlack) := by
  convert supportRatio_sq_div_rpow_sq_le hM hR hRbound using 1
  ring_nf

/-- Cancellation for the mixed term of the sparse mean-value estimate. -/
theorem supportMixed_div_rpow_sq_le
    {R M N T supportExponent thresholdExponent : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hT : 0 ≤ T)
    (hRbound : R ≤ M ^ supportExponent) :
    (R * T / (M ^ (2 : ℕ) * N)) /
        (M ^ thresholdExponent) ^ (2 : ℕ) ≤
      (T / N) *
        M ^ (supportExponent - 2 - 2 * thresholdExponent) := by
  have hdenMain : 0 < M ^ (2 : ℕ) * N := by positivity
  have hdenQ : 0 < (M ^ thresholdExponent) ^ (2 : ℕ) := by
    positivity
  have hnum : R * T ≤ M ^ supportExponent * T :=
    mul_le_mul_of_nonneg_right hRbound hT
  have hbase :
      R * T / (M ^ (2 : ℕ) * N) ≤
        M ^ supportExponent * T / (M ^ (2 : ℕ) * N) :=
    div_le_div_of_nonneg_right hnum hdenMain.le
  calc
    (R * T / (M ^ (2 : ℕ) * N)) /
          (M ^ thresholdExponent) ^ (2 : ℕ) ≤
        (M ^ supportExponent * T / (M ^ (2 : ℕ) * N)) /
          (M ^ thresholdExponent) ^ (2 : ℕ) :=
      div_le_div_of_nonneg_right hbase hdenQ.le
    _ = (T / N) *
        M ^ (supportExponent - 2 - 2 * thresholdExponent) := by
      rw [show M ^ (2 : ℕ) = M ^ (2 : ℝ) by
        exact (Real.rpow_natCast M 2).symm]
      rw [show (M ^ thresholdExponent) ^ (2 : ℕ) =
          M ^ (2 * thresholdExponent) by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
        congr 1
        ring]
      have hpow : M ^ supportExponent =
          M ^ (2 : ℝ) * M ^ (2 * thresholdExponent) *
            M ^ (supportExponent - 2 - 2 * thresholdExponent) := by
        rw [← Real.rpow_add hM, ← Real.rpow_add hM]
        congr 1
        ring
      field_simp [ne_of_gt hM, ne_of_gt hN,
        (Real.rpow_pos_of_pos hM _).ne']
      nlinarith

theorem firstBranch_mixed_threshold_cancellation
    {R M N T a epsilon supportSlack : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hT : 0 ≤ T)
    (hRbound : R ≤ M ^ (1 - 1 / a + supportSlack)) :
    (R * T / (M ^ (2 : ℕ) * N)) /
        (M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) ≤
      (T / N) *
        M ^ (-1 + 1 / a + supportSlack + epsilon / 5) := by
  convert supportMixed_div_rpow_sq_le hM hN hT hRbound using 1
  ring_nf

theorem one_div_rpow_neg_sq {N sigma : ℝ} (hN : 0 < N) :
    1 / (N ^ (-sigma)) ^ (2 : ℕ) = N ^ (2 * sigma) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  norm_num only [Nat.cast_ofNat]
  rw [show (-sigma) * (2 : ℝ) = -(2 * sigma) by ring,
    Real.rpow_neg hN.le]
  field_simp [(Real.rpow_pos_of_pos hN (2 * sigma)).ne']

theorem one_div_rpow_neg_fifth_sq {N sigma : ℝ} (hN : 0 < N) :
    1 / ((N ^ (-sigma)) ^ (5 : ℕ)) ^ (2 : ℕ) =
      N ^ (10 * sigma) := by
  rw [← pow_mul]
  norm_num only
  rw [show (N ^ (-sigma)) ^ (10 : ℕ) = N ^ (-(10 * sigma)) by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring]
  rw [Real.rpow_neg hN.le]
  field_simp [(Real.rpow_pos_of_pos hN (10 * sigma)).ne']

/-- The raw first branch is bounded by the two paper-scale monomials once
the sharp smooth-support estimate is supplied. -/
theorem firstBranchComplexMajorant_le_paperMonomials
    {CRe CIm R M N X eta ARe AIm a epsilon sigma
      supportSlack : ℝ}
    (hM : 0 < M) (hN : 0 < N) (hX : 0 ≤ X) (hR : 0 ≤ R)
    (hcoeff : 0 ≤
      4 * (CRe * ARe ^ (2 : ℕ) + CIm * AIm ^ (2 : ℕ)))
    (hRbound : R ≤ M ^ (1 - 1 / a + supportSlack)) :
    firstBranchComplexMajorant CRe CIm R M N X eta ARe AIm
        (M ^ (-epsilon / 10 - 1 / a)) (N ^ (-sigma)) ≤
      4 * (CRe * ARe ^ (2 : ℕ) + CIm * AIm ^ (2 : ℕ)) *
        (M ^ (epsilon / 5 + 2 * supportSlack) +
          (N * X) ^ eta * (X / N) *
            M ^ (-1 + 1 / a + supportSlack + epsilon / 5)) *
        N ^ (2 * sigma) := by
  have hq : M ^ (-epsilon / 10 - 1 / a) ≠ 0 :=
    (Real.rpow_pos_of_pos hM _).ne'
  have hv : N ^ (-sigma) ≠ 0 :=
    (Real.rpow_pos_of_pos hN _).ne'
  rw [show firstBranchComplexMajorant CRe CIm R M N X eta ARe AIm
        (M ^ (-epsilon / 10 - 1 / a)) (N ^ (-sigma)) =
      4 * (CRe * ARe ^ (2 : ℕ) + CIm * AIm ^ (2 : ℕ)) *
          ((R / M) ^ (2 : ℕ) +
            (N * X) ^ eta * (R * X / (M ^ (2 : ℕ) * N))) /
        ((M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) *
          (N ^ (-sigma)) ^ (2 : ℕ)) by
      unfold firstBranchComplexMajorant
      field_simp [hq, hv]
      ring]
  have hfirst := firstBranch_support_threshold_cancellation
    (epsilon := epsilon) hM hR hRbound
  have hsecond := firstBranch_mixed_threshold_cancellation
    (epsilon := epsilon) hM hN hX hRbound
  have hvInv := one_div_rpow_neg_sq (N := N) (sigma := sigma) hN
  have hpolyNonneg : 0 ≤ (N * X) ^ eta :=
    Real.rpow_nonneg (mul_nonneg hN.le hX) eta
  have hbracket :
      (R / M) ^ (2 : ℕ) /
            (M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) +
          (N * X) ^ eta *
            ((R * X / (M ^ (2 : ℕ) * N)) /
              (M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ)) ≤
        M ^ (epsilon / 5 + 2 * supportSlack) +
          (N * X) ^ eta * (X / N) *
            M ^ (-1 + 1 / a + supportSlack + epsilon / 5) := by
    apply add_le_add hfirst
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hsecond hpolyNonneg
  calc
    4 * (CRe * ARe ^ (2 : ℕ) + CIm * AIm ^ (2 : ℕ)) *
          ((R / M) ^ (2 : ℕ) +
            (N * X) ^ eta * (R * X / (M ^ (2 : ℕ) * N))) /
        ((M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) *
          (N ^ (-sigma)) ^ (2 : ℕ)) =
        4 * (CRe * ARe ^ (2 : ℕ) + CIm * AIm ^ (2 : ℕ)) *
          (((R / M) ^ (2 : ℕ) /
              (M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ)) +
            (N * X) ^ eta *
              ((R * X / (M ^ (2 : ℕ) * N)) /
                (M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ))) *
          N ^ (2 * sigma) := by
            rw [← hvInv]
            field_simp [hq, hv]
    _ ≤ 4 * (CRe * ARe ^ (2 : ℕ) + CIm * AIm ^ (2 : ℕ)) *
        (M ^ (epsilon / 5 + 2 * supportSlack) +
          (N * X) ^ eta * (X / N) *
            M ^ (-1 + 1 / a + supportSlack + epsilon / 5)) *
        N ^ (2 * sigma) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbracket hcoeff)
        (Real.rpow_nonneg hN.le _)

/-- After division by the pointwise lower threshold, the five-block second
branch has the same two paper-scale monomials on every dyadic block. -/
theorem normalizedSecondBranchFiveBlockMajorant_le_paperMonomials
    {C D rho eta X M M1 A0 R a epsilon sigma supportSlack : ℝ}
    (hC : 0 ≤ C) (hM : 0 < M) (hM1 : 0 < M1)
    (hX : 0 ≤ X) (hR : 0 ≤ R)
    (hRbound : R ≤ M ^ (1 - 1 / a + supportSlack)) :
    secondBranchFiveBlockMajorant C D rho eta X M M1 A0 R /
        ((M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) *
          ((M1 ^ (-sigma)) ^ (5 : ℕ)) ^ (2 : ℕ)) ≤
      5 * ∑ j ∈ Finset.range 5,
        let Nj : ℝ := (2 : ℝ) ^ j * M1 ^ (5 : ℕ)
        C *
          (M ^ (epsilon / 5 + 2 * supportSlack) +
            (Nj * X) ^ eta * (X / Nj) *
              M ^ (-1 + 1 / a + supportSlack + epsilon / 5)) *
          (A0 ^ (5 : ℕ) * D * (2 * Nj) ^ rho) ^ (2 : ℕ) *
          M1 ^ (10 * sigma) := by
  have hq : M ^ (-epsilon / 10 - 1 / a) ≠ 0 :=
    (Real.rpow_pos_of_pos hM _).ne'
  have hmden : ((M1 ^ (-sigma)) ^ (5 : ℕ)) ^ (2 : ℕ) ≠ 0 := by
    positivity
  have hfirst := firstBranch_support_threshold_cancellation
    (epsilon := epsilon) hM hR hRbound
  have hminv := one_div_rpow_neg_fifth_sq
    (N := M1) (sigma := sigma) hM1
  unfold secondBranchFiveBlockMajorant
  rw [mul_div_assoc, Finset.sum_div]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro j hj
  let Nj : ℝ := (2 : ℝ) ^ j * M1 ^ (5 : ℕ)
  have hNj : 0 < Nj := by dsimp [Nj]; positivity
  have hpolyNonneg : 0 ≤ (Nj * X) ^ eta :=
    Real.rpow_nonneg (mul_nonneg hNj.le hX) eta
  have hsecond := firstBranch_mixed_threshold_cancellation
    (N := Nj) (epsilon := epsilon) hM hNj hX hRbound
  have hbracket :
      (R / M) ^ (2 : ℕ) /
            (M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) +
          (Nj * X) ^ eta *
            ((R * X / (M ^ (2 : ℕ) * Nj)) /
              (M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ)) ≤
        M ^ (epsilon / 5 + 2 * supportSlack) +
          (Nj * X) ^ eta * (X / Nj) *
            M ^ (-1 + 1 / a + supportSlack + epsilon / 5) := by
    apply add_le_add hfirst
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hsecond hpolyNonneg
  have hcoeffSq : 0 ≤
      (A0 ^ (5 : ℕ) * D * (2 * Nj) ^ rho) ^ (2 : ℕ) :=
    sq_nonneg _
  change
    (C *
      (((R / M) ^ (2 : ℕ) +
        (Nj * X) ^ eta *
          (R * X / (M ^ (2 : ℕ) * Nj))) *
        (A0 ^ (5 : ℕ) * D * (2 * Nj) ^ rho) ^ (2 : ℕ))) /
      ((M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) *
        ((M1 ^ (-sigma)) ^ (5 : ℕ)) ^ (2 : ℕ)) ≤ _
  rw [show
      (C *
        (((R / M) ^ (2 : ℕ) +
          (Nj * X) ^ eta *
            (R * X / (M ^ (2 : ℕ) * Nj))) *
          (A0 ^ (5 : ℕ) * D * (2 * Nj) ^ rho) ^ (2 : ℕ))) /
        ((M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) *
          ((M1 ^ (-sigma)) ^ (5 : ℕ)) ^ (2 : ℕ)) =
      C *
        (((R / M) ^ (2 : ℕ) /
              (M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ)) +
          (Nj * X) ^ eta *
            ((R * X / (M ^ (2 : ℕ) * Nj)) /
              (M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ))) *
        (A0 ^ (5 : ℕ) * D * (2 * Nj) ^ rho) ^ (2 : ℕ) *
        M1 ^ (10 * sigma) by
      rw [← hminv]
      field_simp [hq, hmden]]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbracket hC) hcoeffSq)
    (Real.rpow_nonneg hM1.le _)

/-! ## Explicit coefficient and exponent budgets for the second branch -/

/-- A single fifth-power dyadic block contributes only the explicit fixed
coefficient constant times `X^(epsilon / 55)`.  In particular, the constant
is independent of `X`, the scale exponent, and the block index `j`. -/
theorem fiveBlock_coefficientFactor_sq_le_rpow
    {X M1 A0 D epsilon theta : ℝ} {j : ℕ}
    (hX : 1 < X) (hepsilon : 0 ≤ epsilon)
    (htheta : theta ≤ (2 : ℝ) / 11)
    (hM1 : M1 = X ^ theta) (hj : j < 5) :
    (A0 ^ (5 : ℕ) * D *
        (2 * ((2 : ℝ) ^ j * M1 ^ (5 : ℕ))) ^ (epsilon / 100)) ^
          (2 : ℕ) ≤
      ((A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) *
          (32 : ℝ) ^ (epsilon / 50)) *
        X ^ (epsilon / 55) := by
  have hXpos : 0 < X := lt_trans zero_lt_one hX
  have hXone : 1 ≤ X := hX.le
  have hjle : j ≤ 4 := by omega
  have htwoj : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (4 : ℕ) := by
    exact pow_le_pow_right₀ (by norm_num) hjle
  have hthetaFive : 5 * theta ≤ (10 : ℝ) / 11 := by
    linarith
  have hM1pow : M1 ^ (5 : ℕ) = X ^ (5 * theta) := by
    rw [hM1, ← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hM1pos : 0 < M1 := by
    rw [hM1]
    exact Real.rpow_pos_of_pos hXpos _
  have hM1powNonneg : 0 ≤ M1 ^ (5 : ℕ) := by positivity
  have hscale : M1 ^ (5 : ℕ) ≤ X ^ ((10 : ℝ) / 11) := by
    rw [hM1pow]
    exact Real.rpow_le_rpow_of_exponent_le hXone hthetaFive
  have hbase :
      2 * ((2 : ℝ) ^ j * M1 ^ (5 : ℕ)) ≤
        32 * X ^ ((10 : ℝ) / 11) := by
    calc
      2 * ((2 : ℝ) ^ j * M1 ^ (5 : ℕ)) ≤
          2 * ((2 : ℝ) ^ (4 : ℕ) * X ^ ((10 : ℝ) / 11)) := by
            gcongr
      _ = 32 * X ^ ((10 : ℝ) / 11) := by norm_num; ring
  have hrho : 0 ≤ epsilon / 100 := by positivity
  have hrpow := Real.rpow_le_rpow
    (by positivity : 0 ≤ 2 * ((2 : ℝ) ^ j * M1 ^ (5 : ℕ)))
    hbase hrho
  have hrpowSq :
      ((2 * ((2 : ℝ) ^ j * M1 ^ (5 : ℕ))) ^ (epsilon / 100)) ^
          (2 : ℕ) ≤
        ((32 * X ^ ((10 : ℝ) / 11)) ^ (epsilon / 100)) ^
          (2 : ℕ) :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _) hrpow 2
  have hcoeffNonneg : 0 ≤ (A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) :=
    sq_nonneg _
  have hthirtyTwo :
      (((32 : ℝ) ^ (epsilon / 100)) ^ (2 : ℕ)) =
        (32 : ℝ) ^ (epsilon / 50) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 32)]
    congr 1
    ring
  have hXterm :
      ((X ^ ((10 : ℝ) / 11)) ^ (epsilon / 100)) ^ (2 : ℕ) =
        X ^ (epsilon / 55) := by
    rw [← Real.rpow_natCast,
      ← Real.rpow_mul (Real.rpow_nonneg hXpos.le _),
      ← Real.rpow_mul hXpos.le]
    congr 1
    ring
  calc
    (A0 ^ (5 : ℕ) * D *
        (2 * ((2 : ℝ) ^ j * M1 ^ (5 : ℕ))) ^ (epsilon / 100)) ^
          (2 : ℕ) =
      (A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) *
        ((2 * ((2 : ℝ) ^ j * M1 ^ (5 : ℕ))) ^ (epsilon / 100)) ^
          (2 : ℕ) := by ring
    _ ≤ (A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) *
        ((32 * X ^ ((10 : ℝ) / 11)) ^ (epsilon / 100)) ^
          (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hrpowSq hcoeffNonneg
    _ = ((A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) *
          (32 : ℝ) ^ (epsilon / 50)) *
        X ^ (epsilon / 55) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32)
        (Real.rpow_nonneg hXpos.le _)]
      simp only [mul_pow, hthirtyTwo, hXterm]
      ring

/-- The looser `X^(epsilon / 10)` form used by the final error budget. -/
theorem fiveBlock_coefficientFactor_sq_le_epsilon_tenth
    {X M1 A0 D epsilon theta : ℝ} {j : ℕ}
    (hX : 1 < X) (hepsilon : 0 ≤ epsilon)
    (htheta : theta ≤ (2 : ℝ) / 11)
    (hM1 : M1 = X ^ theta) (hj : j < 5) :
    (A0 ^ (5 : ℕ) * D *
        (2 * ((2 : ℝ) ^ j * M1 ^ (5 : ℕ))) ^ (epsilon / 100)) ^
          (2 : ℕ) ≤
      ((A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) *
          (32 : ℝ) ^ (epsilon / 50)) *
        X ^ (epsilon / 10) := by
  have hstrong := fiveBlock_coefficientFactor_sq_le_rpow
    (A0 := A0) (D := D) hX hepsilon htheta hM1 hj
  have hexponent : epsilon / 55 ≤ epsilon / 10 := by linarith
  have hK : 0 ≤
      (A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) *
        (32 : ℝ) ^ (epsilon / 50) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _)
  exact hstrong.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX.le hexponent) hK)

/-- Lower endpoint for the reciprocal of the sparse-scale exponent. -/
theorem paper_reciprocal_lower
    {a : ℝ} (ha : 0 < a) (haUpper : a ≤ 11 / 10) :
    (10 / 11 : ℝ) ≤ 1 / a := by
  rw [le_div_iff₀ ha]
  nlinarith

/-- Upper endpoint for the reciprocal of the sparse-scale exponent. -/
theorem paper_reciprocal_upper
    {a : ℝ} (ha : 0 < a) (haLower : 12 / 11 ≤ a) :
    1 / a ≤ (11 / 12 : ℝ) := by
  rw [div_le_iff₀ ha]
  nlinarith

/-- Exponent arithmetic for the first (`1`) term of the second
Heath--Brown branch.  This is the place where `theta ≤ 2/11` supplies
`M1^5 ≤ X^(10/11)`, which is just enough against `1/a ≥ 10/11`. -/
theorem secondBranch_firstTerm_exponent_budget
    {a epsilon mu theta sigma1 sigma2 phi : ℝ}
    (hepsilon : 0 < epsilon)
    (ha : 0 < a) (haUpper : a ≤ 11 / 10)
    (hmu : mu ≤ 1) (htheta : theta ≤ 2 / 11)
    (hkey :
      1 / a + 4 * epsilon ≤
        (5 - 8 * sigma1) * theta + 2 * sigma2 * phi) :
    mu * (epsilon / 5 + 2 * (epsilon / 100)) +
          epsilon / 10 + 10 * sigma1 * theta ≤
      2 * sigma1 * theta + 2 * sigma2 * phi - 3 * epsilon := by
  have hrecip : (10 / 11 : ℝ) ≤ 1 / a :=
    paper_reciprocal_lower ha haUpper
  have hmuLoss :
      mu * (epsilon / 5 + 2 * (epsilon / 100)) ≤
        epsilon / 5 + 2 * (epsilon / 100) := by
    apply mul_le_of_le_one_left
    · positivity
    · exact hmu
  nlinarith

/-- The exponent of `M` in the mixed term is negative throughout the
paper's parameter box. -/
theorem secondBranch_mixed_M_exponent_nonpos
    {a epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1 / 10)
    (ha : 0 < a) (haLower : 12 / 11 ≤ a) :
    -1 + 1 / a + epsilon / 100 + epsilon / 5 ≤ 0 := by
  have hrecip : 1 / a ≤ (11 / 12 : ℝ) :=
    paper_reciprocal_upper ha haLower
  nlinarith

/-- Exponent arithmetic for the mixed term of the second branch.  A
lower bound `mu ≥ 1-epsilon/100` is used because the exponent of `M` is
negative. -/
theorem secondBranch_mixedTerm_exponent_budget
    {a epsilon mu theta sigma1 sigma2 phi : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1 / 10)
    (ha : 0 < a) (haLower : 12 / 11 ≤ a)
    (hmu : 1 - epsilon / 100 ≤ mu)
    (htheta : theta ≤ 2 / 11)
    (hkey :
      1 / a + 4 * epsilon ≤
        (5 - 8 * sigma1) * theta + 2 * sigma2 * phi) :
    (epsilon / 100) * (5 * theta + 1) +
          (1 - 5 * theta) +
          mu * (-1 + 1 / a + epsilon / 100 + epsilon / 5) +
          epsilon / 10 + 10 * sigma1 * theta ≤
      2 * sigma1 * theta + 2 * sigma2 * phi - 3 * epsilon := by
  let c : ℝ := -1 + 1 / a + epsilon / 100 + epsilon / 5
  have hc : c ≤ 0 := by
    dsimp [c]
    exact secondBranch_mixed_M_exponent_nonpos hepsilon hepsilonUpper
      ha haLower
  have haInvPos : 0 < 1 / a := by positivity
  have hcLower : -1 ≤ c := by
    dsimp [c]
    nlinarith
  have hmuC : mu * c ≤ (1 - epsilon / 100) * c :=
    mul_le_mul_of_nonpos_right hmu hc
  have hscaleLoss :
      (1 - epsilon / 100) * c ≤ c + epsilon / 100 := by
    have hprod : -(epsilon / 100) * c ≤ epsilon / 100 := by
      nlinarith [mul_nonneg (show 0 ≤ epsilon / 100 by positivity)
        (show 0 ≤ c + 1 by linarith)]
    nlinarith
  have hmuC' : mu * c ≤ c + epsilon / 100 := hmuC.trans hscaleLoss
  have heta :
      (epsilon / 100) * (5 * theta + 1) ≤ epsilon / 50 := by
    have hfactor : 5 * theta + 1 ≤ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left hfactor
      (show 0 ≤ epsilon / 100 by positivity)
    nlinarith
  dsimp [c] at hmuC'
  nlinarith

/-- Rpow realization of the first-term exponent budget.  The middle
factor `K * X^(epsilon/10)` is the already-collected divisor-coefficient
loss; `K` is independent of `X`. -/
theorem secondBranch_firstTerm_fixedPowerSaving_model
    {X K a epsilon mu theta sigma1 sigma2 phi : ℝ}
    (hX : 1 < X) (hK : 0 ≤ K)
    (hepsilon : 0 < epsilon)
    (ha : 0 < a) (haUpper : a ≤ 11 / 10)
    (hmu : mu ≤ 1) (htheta : theta ≤ 2 / 11)
    (hkey :
      1 / a + 4 * epsilon ≤
        (5 - 8 * sigma1) * theta + 2 * sigma2 * phi) :
    X ^ (mu * (epsilon / 5 + 2 * (epsilon / 100))) *
          (K * X ^ (epsilon / 10)) *
          X ^ (10 * sigma1 * theta) ≤
      K * (X ^ (2 * sigma1 * theta) * X ^ (2 * sigma2 * phi)) *
        X ^ (-3 * epsilon) := by
  have hexp := secondBranch_firstTerm_exponent_budget hepsilon ha
    haUpper hmu htheta hkey
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hpow := Real.rpow_le_rpow_of_exponent_le hX.le hexp
  calc
    X ^ (mu * (epsilon / 5 + 2 * (epsilon / 100))) *
          (K * X ^ (epsilon / 10)) *
          X ^ (10 * sigma1 * theta) =
        K * X ^
          (mu * (epsilon / 5 + 2 * (epsilon / 100)) +
            epsilon / 10 + 10 * sigma1 * theta) := by
              calc
                _ = K *
                    ((X ^ (mu * (epsilon / 5 + 2 * (epsilon / 100))) *
                      X ^ (epsilon / 10)) *
                      X ^ (10 * sigma1 * theta)) := by ring
                _ = _ := by
                  rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
    _ ≤ K * X ^
          (2 * sigma1 * theta + 2 * sigma2 * phi - 3 * epsilon) :=
      mul_le_mul_of_nonneg_left hpow hK
    _ = K * (X ^ (2 * sigma1 * theta) * X ^ (2 * sigma2 * phi)) *
        X ^ (-3 * epsilon) := by
          calc
            _ = K *
                ((X ^ (2 * sigma1 * theta) *
                  X ^ (2 * sigma2 * phi)) * X ^ (-3 * epsilon)) := by
                    rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
                    congr 2
                    ring
            _ = _ := by ring

/-- Rpow realization of the mixed-term exponent budget.  `Keta` absorbs
the bounded dyadic multiplier in `(Nj*X)^eta`, while `Krho` absorbs the
fixed part of the divisor-subpower coefficient bound. -/
theorem secondBranch_mixedTerm_fixedPowerSaving_model
    {X Keta Krho a epsilon mu theta sigma1 sigma2 phi : ℝ}
    (hX : 1 < X) (hKeta : 0 ≤ Keta) (hKrho : 0 ≤ Krho)
    (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1 / 10)
    (ha : 0 < a) (haLower : 12 / 11 ≤ a)
    (hmu : 1 - epsilon / 100 ≤ mu)
    (htheta : theta ≤ 2 / 11)
    (hkey :
      1 / a + 4 * epsilon ≤
        (5 - 8 * sigma1) * theta + 2 * sigma2 * phi) :
    (Keta * X ^ ((epsilon / 100) * (5 * theta + 1))) *
          X ^ (1 - 5 * theta) *
          X ^ (mu * (-1 + 1 / a + epsilon / 100 + epsilon / 5)) *
          (Krho * X ^ (epsilon / 10)) *
          X ^ (10 * sigma1 * theta) ≤
      (Keta * Krho) *
        (X ^ (2 * sigma1 * theta) * X ^ (2 * sigma2 * phi)) *
        X ^ (-3 * epsilon) := by
  have hexp := secondBranch_mixedTerm_exponent_budget hepsilon
    hepsilonUpper ha haLower hmu htheta hkey
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hpow := Real.rpow_le_rpow_of_exponent_le hX.le hexp
  have hK : 0 ≤ Keta * Krho := mul_nonneg hKeta hKrho
  calc
    (Keta * X ^ ((epsilon / 100) * (5 * theta + 1))) *
          X ^ (1 - 5 * theta) *
          X ^ (mu * (-1 + 1 / a + epsilon / 100 + epsilon / 5)) *
          (Krho * X ^ (epsilon / 10)) *
          X ^ (10 * sigma1 * theta) =
        (Keta * Krho) * X ^
          ((epsilon / 100) * (5 * theta + 1) +
            (1 - 5 * theta) +
            mu * (-1 + 1 / a + epsilon / 100 + epsilon / 5) +
            epsilon / 10 + 10 * sigma1 * theta) := by
              calc
                _ = (Keta * Krho) *
                    ((((X ^ ((epsilon / 100) * (5 * theta + 1)) *
                      X ^ (1 - 5 * theta)) *
                      X ^ (mu * (-1 + 1 / a + epsilon / 100 + epsilon / 5))) *
                      X ^ (epsilon / 10)) *
                      X ^ (10 * sigma1 * theta)) := by ring
                _ = _ := by
                  rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos,
                    ← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
    _ ≤ (Keta * Krho) * X ^
          (2 * sigma1 * theta + 2 * sigma2 * phi - 3 * epsilon) :=
      mul_le_mul_of_nonneg_left hpow hK
    _ = (Keta * Krho) *
        (X ^ (2 * sigma1 * theta) * X ^ (2 * sigma2 * phi)) *
        X ^ (-3 * epsilon) := by
          calc
            _ = (Keta * Krho) *
                ((X ^ (2 * sigma1 * theta) *
                  X ^ (2 * sigma2 * phi)) * X ^ (-3 * epsilon)) := by
                    rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
                    congr 2
                    ring
            _ = _ := by ring

/-- Both normalized second-branch monomials together retain the same
`X^(-3 epsilon)` saving. -/
theorem secondBranch_twoTerms_fixedPowerSaving_model
    {X Kfirst Keta Krho a epsilon mu theta sigma1 sigma2 phi : ℝ}
    (hX : 1 < X) (hKfirst : 0 ≤ Kfirst)
    (hKeta : 0 ≤ Keta) (hKrho : 0 ≤ Krho)
    (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1 / 10)
    (ha : 0 < a) (haLower : 12 / 11 ≤ a) (haUpper : a ≤ 11 / 10)
    (hmuLower : 1 - epsilon / 100 ≤ mu) (hmuUpper : mu ≤ 1)
    (htheta : theta ≤ 2 / 11)
    (hkey :
      1 / a + 4 * epsilon ≤
        (5 - 8 * sigma1) * theta + 2 * sigma2 * phi) :
    X ^ (mu * (epsilon / 5 + 2 * (epsilon / 100))) *
          (Kfirst * X ^ (epsilon / 10)) *
          X ^ (10 * sigma1 * theta) +
        (Keta * X ^ ((epsilon / 100) * (5 * theta + 1))) *
          X ^ (1 - 5 * theta) *
          X ^ (mu * (-1 + 1 / a + epsilon / 100 + epsilon / 5)) *
          (Krho * X ^ (epsilon / 10)) *
          X ^ (10 * sigma1 * theta) ≤
      (Kfirst + Keta * Krho) *
        (X ^ (2 * sigma1 * theta) * X ^ (2 * sigma2 * phi)) *
        X ^ (-3 * epsilon) := by
  have hfirst := secondBranch_firstTerm_fixedPowerSaving_model hX
    hKfirst hepsilon ha haUpper hmuUpper htheta hkey
  have hmixed := secondBranch_mixedTerm_fixedPowerSaving_model hX
    hKeta hKrho hepsilon hepsilonUpper ha haLower hmuLower
    htheta hkey
  nlinarith [Real.rpow_pos_of_pos (zero_lt_one.trans hX) (-3 * epsilon),
    Real.rpow_pos_of_pos (zero_lt_one.trans hX) (2 * sigma1 * theta),
    Real.rpow_pos_of_pos (zero_lt_one.trans hX) (2 * sigma2 * phi)]

/-! ## Logarithmic coordinates and the literal dyadic loss -/

/-- A positive scale is exactly the ambient scale raised to its logarithmic
coordinate. -/
theorem scale_eq_rpow_logRatio
    {X M : ℝ} (hX : 1 < X) (hM : 0 < M) :
    M = X ^ (Real.log M / Real.log X) := by
  simpa [Hybrid.logarithmicLengthExponent] using
    (Hybrid.eq_rpow_logarithmicLengthExponent hX hM)

/-- Arbitrary real powers can be rewritten in the same logarithmic
coordinate. -/
theorem scale_rpow_eq_rpow_logRatio_mul
    {X M q : ℝ} (hX : 1 < X) (hM : 0 < M) :
    M ^ q = X ^ ((Real.log M / Real.log X) * q) := by
  simpa [Hybrid.logarithmicLengthExponent] using
    (Hybrid.rpow_eq_rpow_logarithmicLengthExponent_mul
      (T := X) (N := M) (q := q) hX hM)

/-- Simultaneous logarithmic coordinates `mu` and `phi` for the sparse and
complementary scales, including the product-of-powers rewrite used after the
second-branch exponent budget. -/
theorem sparseAndComplement_logCoordinate_package
    {X M M2 : ℝ} (hX : 1 < X) (hM : 0 < M) (hM2 : 0 < M2) :
    let mu : ℝ := Real.log M / Real.log X
    let phi : ℝ := Real.log M2 / Real.log X
    M = X ^ mu ∧ M2 = X ^ phi ∧
      ∀ u v : ℝ,
        M ^ u * M2 ^ v = X ^ (mu * u) * X ^ (phi * v) := by
  dsimp only
  refine ⟨scale_eq_rpow_logRatio hX hM,
    scale_eq_rpow_logRatio hX hM2, ?_⟩
  intro u v
  rw [scale_rpow_eq_rpow_logRatio_mul hX hM,
    scale_rpow_eq_rpow_logRatio_mul hX hM2]

/-- For the paper choice `eta=epsilon/100`, every fifth-power dyadic block
has a multiplier bounded by the fixed factor `16^eta` times the exact ambient
power occurring in the mixed-term budget. -/
theorem fifthPowerDyadic_etaMultiplier_le
    {X M1 epsilon theta : ℝ} {j : ℕ}
    (hX : 1 < X) (hepsilon : 0 ≤ epsilon)
    (_htheta : 0 ≤ theta) (hM1 : M1 = X ^ theta) (hj : j < 5) :
    (((2 : ℝ) ^ j * M1 ^ (5 : ℕ)) * X) ^ (epsilon / 100) ≤
      (16 : ℝ) ^ (epsilon / 100) *
        X ^ ((epsilon / 100) * (5 * theta + 1)) := by
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hjle : j ≤ 4 := by omega
  have htwoj : (2 : ℝ) ^ j ≤ 16 := by
    calc
      (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (4 : ℕ) :=
        pow_le_pow_right₀ (by norm_num) hjle
      _ = 16 := by norm_num
  have hM1pow : M1 ^ (5 : ℕ) = X ^ (5 * theta) := by
    rw [hM1, ← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hXcombine : X ^ (5 * theta) * X = X ^ (5 * theta + 1) := by
    calc
      X ^ (5 * theta) * X = X ^ (5 * theta) * X ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = X ^ (5 * theta + 1) :=
        (Real.rpow_add hXpos (5 * theta) 1).symm
  have hbase :
      ((2 : ℝ) ^ j * M1 ^ (5 : ℕ)) * X ≤
        16 * X ^ (5 * theta + 1) := by
    rw [hM1pow]
    calc
      ((2 : ℝ) ^ j * X ^ (5 * theta)) * X =
          (2 : ℝ) ^ j * (X ^ (5 * theta) * X) := by ring
      _ = (2 : ℝ) ^ j * X ^ (5 * theta + 1) := by rw [hXcombine]
      _ ≤ 16 * X ^ (5 * theta + 1) :=
        mul_le_mul_of_nonneg_right htwoj
          (Real.rpow_nonneg hXpos.le _)
  have heta : 0 ≤ epsilon / 100 := by positivity
  have hleftNonneg :
      0 ≤ ((2 : ℝ) ^ j * M1 ^ (5 : ℕ)) * X := by
    rw [hM1]
    positivity
  calc
    (((2 : ℝ) ^ j * M1 ^ (5 : ℕ)) * X) ^ (epsilon / 100) ≤
        (16 * X ^ (5 * theta + 1)) ^ (epsilon / 100) :=
      Real.rpow_le_rpow hleftNonneg hbase heta
    _ = (16 : ℝ) ^ (epsilon / 100) *
        X ^ ((epsilon / 100) * (5 * theta + 1)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16)
        (Real.rpow_nonneg hXpos.le _)]
      rw [← Real.rpow_mul hXpos.le]
      congr 2
      ring

/-! ## Explicit exponent budget for the first branch -/

/-- The support term in the first Heath--Brown branch has a full
`epsilon^2` saving. -/
theorem firstBranch_firstTerm_exponent_budget_model
    {epsilon mu theta sigma1 : ℝ}
    (hepsilon : 0 < epsilon)
    (hmu : mu ≤ 1)
    (htheta : epsilon / 2 ≤ theta)
    (hsigma : 1 / 5 + 2 * epsilon ≤ sigma1) :
    mu * (epsilon / 5 + 2 * (epsilon ^ 2 / 100)) +
          epsilon ^ 2 / 100 ≤
      2 * sigma1 * theta - epsilon ^ 2 := by
  have hloss : 0 ≤ epsilon / 5 + 2 * (epsilon ^ 2 / 100) := by
    positivity
  have hmuLoss :
      mu * (epsilon / 5 + 2 * (epsilon ^ 2 / 100)) ≤
        epsilon / 5 + 2 * (epsilon ^ 2 / 100) :=
    mul_le_of_le_one_left hloss hmu
  have hthetaNonneg : 0 ≤ theta := by linarith
  have hsigmaNonneg : 0 ≤ sigma1 := by linarith
  have hproduct :
      (1 / 5 + 2 * epsilon) * (epsilon / 2) ≤ sigma1 * theta :=
    mul_le_mul hsigma htheta (by positivity) hsigmaNonneg
  nlinarith

/-- The mixed term has the same quadratic saving under the actual first
branch condition and an `epsilon^2/100` logarithmic product-scale loss. -/
theorem firstBranch_mixedTerm_exponent_budget_model
    {a epsilon mu theta phi sigma1 : ℝ}
    (hepsilon : 0 < epsilon)
    (hepsilonUpper : epsilon ≤ 1 / 10)
    (hmu : mu ≤ 1)
    (hphi : phi ≤ 1)
    (hproductLoss : 1 - theta - phi ≤ epsilon ^ 2 / 100)
    (hfirstBranch :
      theta * (1 - 2 * sigma1) ≤
        -epsilon / 3 + mu * (1 - 1 / a)) :
    (epsilon ^ 2 / 100) * (phi + 1) +
          (1 - phi) +
          mu * (-1 + 1 / a + epsilon ^ 2 / 100 + epsilon / 5) +
          epsilon ^ 2 / 100 ≤
      2 * sigma1 * theta - epsilon ^ 2 := by
  have hetaNonneg : 0 ≤ epsilon ^ 2 / 100 := by positivity
  have heta :
      (epsilon ^ 2 / 100) * (phi + 1) ≤ epsilon ^ 2 / 50 := by
    have hfactor : phi + 1 ≤ 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hfactor hetaNonneg]
  have hsmallLoss : 0 ≤ epsilon ^ 2 / 100 + epsilon / 5 := by
    positivity
  have hmuLoss :
      mu * (epsilon ^ 2 / 100 + epsilon / 5) ≤
        epsilon ^ 2 / 100 + epsilon / 5 :=
    mul_le_of_le_one_left hsmallLoss hmu
  have hbranch' :
      mu * (-1 + 1 / a) ≤
        2 * sigma1 * theta - theta - epsilon / 3 := by
    nlinarith [hfirstBranch]
  have hepsilonSmall : epsilon ^ 2 ≤ epsilon / 10 := by
    nlinarith [mul_nonneg hepsilon.le
      (show 0 ≤ 1 / 10 - epsilon by linarith)]
  nlinarith

/-- Rpow form of the first monomial after substituting
`M=X^mu`, `M₂=X^phi` and the coefficient-supremum loss. -/
theorem firstBranch_firstTerm_fixedPowerSaving_model
    {X K epsilon mu theta phi sigma1 sigma2 : ℝ}
    (hX : 1 < X) (hK : 0 ≤ K)
    (hepsilon : 0 < epsilon)
    (hmu : mu ≤ 1)
    (htheta : epsilon / 2 ≤ theta)
    (hsigma : 1 / 5 + 2 * epsilon ≤ sigma1) :
    X ^ (mu * (epsilon / 5 + 2 * (epsilon ^ 2 / 100))) *
          (K * X ^ (epsilon ^ 2 / 100)) *
          X ^ (2 * sigma2 * phi) ≤
      K * (X ^ (2 * sigma1 * theta) * X ^ (2 * sigma2 * phi)) *
        X ^ (-epsilon ^ 2) := by
  have hexp := firstBranch_firstTerm_exponent_budget_model
    hepsilon hmu htheta hsigma
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hpow := Real.rpow_le_rpow_of_exponent_le hX.le
    (show
      mu * (epsilon / 5 + 2 * (epsilon ^ 2 / 100)) +
          epsilon ^ 2 / 100 + 2 * sigma2 * phi ≤
        2 * sigma1 * theta + 2 * sigma2 * phi - epsilon ^ 2 by
      linarith)
  calc
    X ^ (mu * (epsilon / 5 + 2 * (epsilon ^ 2 / 100))) *
          (K * X ^ (epsilon ^ 2 / 100)) *
          X ^ (2 * sigma2 * phi) =
        K * X ^
          (mu * (epsilon / 5 + 2 * (epsilon ^ 2 / 100)) +
            epsilon ^ 2 / 100 + 2 * sigma2 * phi) := by
              calc
                _ = K *
                    ((X ^ (mu * (epsilon / 5 + 2 * (epsilon ^ 2 / 100))) *
                      X ^ (epsilon ^ 2 / 100)) *
                      X ^ (2 * sigma2 * phi)) := by ring
                _ = _ := by
                  rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
    _ ≤ K * X ^
          (2 * sigma1 * theta + 2 * sigma2 * phi - epsilon ^ 2) :=
      mul_le_mul_of_nonneg_left hpow hK
    _ = K * (X ^ (2 * sigma1 * theta) * X ^ (2 * sigma2 * phi)) *
        X ^ (-epsilon ^ 2) := by
          calc
            _ = K *
                ((X ^ (2 * sigma1 * theta) *
                  X ^ (2 * sigma2 * phi)) * X ^ (-epsilon ^ 2)) := by
                    rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
                    congr 2
            _ = _ := by ring

/-- Rpow form of the mixed monomial after the same substitutions. -/
theorem firstBranch_mixedTerm_fixedPowerSaving_model
    {X Keta Kcoeff a epsilon mu theta phi sigma1 sigma2 : ℝ}
    (hX : 1 < X) (hKeta : 0 ≤ Keta) (hKcoeff : 0 ≤ Kcoeff)
    (hepsilon : 0 < epsilon)
    (hepsilonUpper : epsilon ≤ 1 / 10)
    (hmu : mu ≤ 1)
    (hphi : phi ≤ 1)
    (hproductLoss : 1 - theta - phi ≤ epsilon ^ 2 / 100)
    (hfirstBranch :
      theta * (1 - 2 * sigma1) ≤
        -epsilon / 3 + mu * (1 - 1 / a)) :
    (Keta * X ^ ((epsilon ^ 2 / 100) * (phi + 1))) *
          X ^ (1 - phi) *
          X ^ (mu * (-1 + 1 / a + epsilon ^ 2 / 100 + epsilon / 5)) *
          (Kcoeff * X ^ (epsilon ^ 2 / 100)) *
          X ^ (2 * sigma2 * phi) ≤
      (Keta * Kcoeff) *
        (X ^ (2 * sigma1 * theta) * X ^ (2 * sigma2 * phi)) *
        X ^ (-epsilon ^ 2) := by
  have hexp := firstBranch_mixedTerm_exponent_budget_model
    hepsilon hepsilonUpper hmu hphi hproductLoss hfirstBranch
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hpow := Real.rpow_le_rpow_of_exponent_le hX.le
    (show
      (epsilon ^ 2 / 100) * (phi + 1) +
          (1 - phi) +
          mu * (-1 + 1 / a + epsilon ^ 2 / 100 + epsilon / 5) +
          epsilon ^ 2 / 100 + 2 * sigma2 * phi ≤
        2 * sigma1 * theta + 2 * sigma2 * phi - epsilon ^ 2 by
      linarith)
  have hK : 0 ≤ Keta * Kcoeff := mul_nonneg hKeta hKcoeff
  calc
    (Keta * X ^ ((epsilon ^ 2 / 100) * (phi + 1))) *
          X ^ (1 - phi) *
          X ^ (mu * (-1 + 1 / a + epsilon ^ 2 / 100 + epsilon / 5)) *
          (Kcoeff * X ^ (epsilon ^ 2 / 100)) *
          X ^ (2 * sigma2 * phi) =
        (Keta * Kcoeff) * X ^
          ((epsilon ^ 2 / 100) * (phi + 1) +
            (1 - phi) +
            mu * (-1 + 1 / a + epsilon ^ 2 / 100 + epsilon / 5) +
            epsilon ^ 2 / 100 + 2 * sigma2 * phi) := by
              calc
                _ = (Keta * Kcoeff) *
                    ((((X ^ ((epsilon ^ 2 / 100) * (phi + 1)) *
                      X ^ (1 - phi)) *
                      X ^ (mu * (-1 + 1 / a + epsilon ^ 2 / 100 + epsilon / 5))) *
                      X ^ (epsilon ^ 2 / 100)) *
                      X ^ (2 * sigma2 * phi)) := by ring
                _ = _ := by
                  rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos,
                    ← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
    _ ≤ (Keta * Kcoeff) * X ^
          (2 * sigma1 * theta + 2 * sigma2 * phi - epsilon ^ 2) :=
      mul_le_mul_of_nonneg_left hpow hK
    _ = (Keta * Kcoeff) *
        (X ^ (2 * sigma1 * theta) * X ^ (2 * sigma2 * phi)) *
        X ^ (-epsilon ^ 2) := by
          calc
            _ = (Keta * Kcoeff) *
                ((X ^ (2 * sigma1 * theta) *
                  X ^ (2 * sigma2 * phi)) * X ^ (-epsilon ^ 2)) := by
                    rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos]
                    congr 2
            _ = _ := by ring

/-- Both first-branch monomials have a common `X^(-epsilon^2)` saving. -/
theorem firstBranch_twoTerms_fixedPowerSaving_model
    {X Kfirst Keta Kcoeff a epsilon mu theta phi sigma1 sigma2 : ℝ}
    (hX : 1 < X) (hKfirst : 0 ≤ Kfirst)
    (hKeta : 0 ≤ Keta) (hKcoeff : 0 ≤ Kcoeff)
    (hepsilon : 0 < epsilon)
    (hepsilonUpper : epsilon ≤ 1 / 10)
    (hmu : mu ≤ 1)
    (htheta : epsilon / 2 ≤ theta)
    (hphi : phi ≤ 1)
    (hsigma : 1 / 5 + 2 * epsilon ≤ sigma1)
    (hproductLoss : 1 - theta - phi ≤ epsilon ^ 2 / 100)
    (hfirstBranch :
      theta * (1 - 2 * sigma1) ≤
        -epsilon / 3 + mu * (1 - 1 / a)) :
    X ^ (mu * (epsilon / 5 + 2 * (epsilon ^ 2 / 100))) *
          (Kfirst * X ^ (epsilon ^ 2 / 100)) *
          X ^ (2 * sigma2 * phi) +
        (Keta * X ^ ((epsilon ^ 2 / 100) * (phi + 1))) *
          X ^ (1 - phi) *
          X ^ (mu * (-1 + 1 / a + epsilon ^ 2 / 100 + epsilon / 5)) *
          (Kcoeff * X ^ (epsilon ^ 2 / 100)) *
          X ^ (2 * sigma2 * phi) ≤
      (Kfirst + Keta * Kcoeff) *
        (X ^ (2 * sigma1 * theta) * X ^ (2 * sigma2 * phi)) *
        X ^ (-epsilon ^ 2) := by
  have hfirst := firstBranch_firstTerm_fixedPowerSaving_model
    (phi := phi) (sigma2 := sigma2)
    hX hKfirst hepsilon hmu htheta hsigma
  have hmixed := firstBranch_mixedTerm_fixedPowerSaving_model
    (sigma2 := sigma2)
    hX hKeta hKcoeff hepsilon hepsilonUpper hmu hphi
    hproductLoss hfirstBranch
  nlinarith [Real.rpow_pos_of_pos (zero_lt_one.trans hX) (-epsilon ^ 2),
    Real.rpow_pos_of_pos (zero_lt_one.trans hX) (2 * sigma1 * theta),
    Real.rpow_pos_of_pos (zero_lt_one.trans hX) (2 * sigma2 * phi)]

/-- The literal first-branch majorant inherits the quadratic power saving
after the sharp support and coefficient-supremum losses are inserted. -/
theorem firstBranchComplexMajorant_fixedPowerSaving
    {CRe CIm R M N X ARe AIm a epsilon mu theta phi sigma1 sigma2 : ℝ}
    (hX : 1 < X) (hM : 0 < M) (hN : 0 < N) (hR : 0 ≤ R)
    (hMcoord : M = X ^ mu) (hNcoord : N = X ^ phi)
    (hcoeff0 : 0 ≤
      4 * (CRe * ARe ^ (2 : ℕ) + CIm * AIm ^ (2 : ℕ)))
    (hcoeff :
      4 * (CRe * ARe ^ (2 : ℕ) + CIm * AIm ^ (2 : ℕ)) ≤
        X ^ (epsilon ^ 2 / 100))
    (hRbound : R ≤ M ^ (1 - 1 / a + epsilon ^ 2 / 100))
    (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1 / 10)
    (hmu : mu ≤ 1) (htheta : epsilon / 2 ≤ theta)
    (hphi : phi ≤ 1)
    (hsigma : 1 / 5 + 2 * epsilon ≤ sigma1)
    (hproductLoss : 1 - theta - phi ≤ epsilon ^ 2 / 100)
    (hfirstBranch :
      theta * (1 - 2 * sigma1) ≤
        -epsilon / 3 + mu * (1 - 1 / a)) :
    firstBranchComplexMajorant CRe CIm R M N X
        (epsilon ^ 2 / 100) ARe AIm
        (M ^ (-epsilon / 10 - 1 / a)) (N ^ (-sigma2)) ≤
      2 * (X ^ (2 * sigma1 * theta) * X ^ (2 * sigma2 * phi)) *
        X ^ (-epsilon ^ 2) := by
  let alpha : ℝ := epsilon / 5 + 2 * (epsilon ^ 2 / 100)
  let beta : ℝ := -1 + 1 / a + epsilon ^ 2 / 100 + epsilon / 5
  let coeff : ℝ :=
    4 * (CRe * ARe ^ (2 : ℕ) + CIm * AIm ^ (2 : ℕ))
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hraw := firstBranchComplexMajorant_le_paperMonomials
    (eta := epsilon ^ 2 / 100) (epsilon := epsilon) (sigma := sigma2)
    (supportSlack := epsilon ^ 2 / 100)
    hM hN hXpos.le hR hcoeff0 hRbound
  have hMalpha : M ^ alpha = X ^ (mu * alpha) := by
    rw [hMcoord, ← Real.rpow_mul hXpos.le]
  have hMbeta : M ^ beta = X ^ (mu * beta) := by
    rw [hMcoord, ← Real.rpow_mul hXpos.le]
  have hNpow : N ^ (2 * sigma2) = X ^ (2 * sigma2 * phi) := by
    rw [hNcoord, ← Real.rpow_mul hXpos.le]
    congr 1
    ring
  have heta :
      (N * X) ^ (epsilon ^ 2 / 100) =
        X ^ ((epsilon ^ 2 / 100) * (phi + 1)) := by
    rw [hNcoord, Real.mul_rpow (Real.rpow_nonneg hXpos.le _) hXpos.le]
    rw [← Real.rpow_mul hXpos.le]
    rw [show X ^ (epsilon ^ 2 / 100) =
        X ^ ((epsilon ^ 2 / 100) * 1) by ring_nf]
    rw [← Real.rpow_add hXpos]
    congr 1
    ring
  have hquot : X / N = X ^ (1 - phi) := by
    rw [hNcoord]
    calc
      X / X ^ phi = X ^ (1 : ℝ) / X ^ phi := by rw [Real.rpow_one]
      _ = X ^ (1 - phi) := (Real.rpow_sub hXpos 1 phi).symm
  have hrestNonneg :
      0 ≤ (M ^ alpha +
          (N * X) ^ (epsilon ^ 2 / 100) * (X / N) * M ^ beta) *
        N ^ (2 * sigma2) := by positivity
  have htoModel :
      coeff *
          (M ^ alpha +
            (N * X) ^ (epsilon ^ 2 / 100) * (X / N) * M ^ beta) *
          N ^ (2 * sigma2) ≤
        X ^ (mu * alpha) *
              ((1 : ℝ) * X ^ (epsilon ^ 2 / 100)) *
              X ^ (2 * sigma2 * phi) +
          ((1 : ℝ) * X ^ ((epsilon ^ 2 / 100) * (phi + 1))) *
              X ^ (1 - phi) * X ^ (mu * beta) *
              ((1 : ℝ) * X ^ (epsilon ^ 2 / 100)) *
              X ^ (2 * sigma2 * phi) := by
    calc
      coeff *
            (M ^ alpha +
              (N * X) ^ (epsilon ^ 2 / 100) * (X / N) * M ^ beta) *
            N ^ (2 * sigma2) =
          coeff *
            ((M ^ alpha +
              (N * X) ^ (epsilon ^ 2 / 100) * (X / N) * M ^ beta) *
              N ^ (2 * sigma2)) := by ring
      _ ≤ X ^ (epsilon ^ 2 / 100) *
            ((M ^ alpha +
              (N * X) ^ (epsilon ^ 2 / 100) * (X / N) * M ^ beta) *
              N ^ (2 * sigma2)) :=
        mul_le_mul_of_nonneg_right hcoeff hrestNonneg
      _ = _ := by rw [hMalpha, hMbeta, hNpow, heta, hquot]; ring
  have hmodel := firstBranch_twoTerms_fixedPowerSaving_model
    (Kfirst := (1 : ℝ)) (Keta := (1 : ℝ)) (Kcoeff := (1 : ℝ))
    (sigma2 := sigma2)
    hX (by norm_num) (by norm_num) (by norm_num) hepsilon
    hepsilonUpper hmu htheta hphi hsigma hproductLoss hfirstBranch
  dsimp [alpha, beta, coeff] at hraw htoModel
  have hmodel' :
      X ^ (mu * (epsilon / 5 + 2 * (epsilon ^ 2 / 100))) *
            X ^ (epsilon ^ 2 / 100) * X ^ (2 * sigma2 * phi) +
          X ^ ((epsilon ^ 2 / 100) * (phi + 1)) * X ^ (1 - phi) *
            X ^ (mu * (-1 + 1 / a + epsilon ^ 2 / 100 + epsilon / 5)) *
            X ^ (epsilon ^ 2 / 100) * X ^ (2 * sigma2 * phi) ≤
        2 * (X ^ (2 * sigma1 * theta) * X ^ (2 * sigma2 * phi)) *
          X ^ (-epsilon ^ 2) := by
    convert hmodel using 1 <;> ring
  exact hraw.trans (htoModel.trans (by simpa using hmodel'))

/-! ## Literal closure of the normalized five-block second branch -/

/-- Removing the dyadic factor `2^j` can only increase the quotient.  In
logarithmic coordinates this gives the exact power used in the mixed-term
budget. -/
theorem X_div_fifthPowerDyadic_le_logCoordinate_model
    {X M1 theta : ℝ} {j : ℕ}
    (hX : 1 < X) (hM1 : M1 = X ^ theta) :
    X / ((2 : ℝ) ^ j * M1 ^ (5 : ℕ)) ≤ X ^ (1 - 5 * theta) := by
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hM1pos : 0 < M1 := by
    rw [hM1]
    exact Real.rpow_pos_of_pos hXpos _
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ j :=
    one_le_pow₀ (by norm_num)
  have hden : M1 ^ (5 : ℕ) ≤ (2 : ℝ) ^ j * M1 ^ (5 : ℕ) := by
    simpa using mul_le_mul_of_nonneg_right htwo
      (pow_nonneg hM1pos.le 5)
  have hquot :
      X / ((2 : ℝ) ^ j * M1 ^ (5 : ℕ)) ≤ X / M1 ^ (5 : ℕ) :=
    div_le_div_of_nonneg_left hXpos.le (pow_pos hM1pos 5) hden
  have hM1pow : M1 ^ (5 : ℕ) = X ^ (5 * theta) := by
    rw [hM1, ← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  calc
    X / ((2 : ℝ) ^ j * M1 ^ (5 : ℕ)) ≤ X / M1 ^ (5 : ℕ) := hquot
    _ = X ^ (1 - 5 * theta) := by
      rw [hM1pow]
      calc
        X / X ^ (5 * theta) = X ^ (1 : ℝ) / X ^ (5 * theta) := by
          rw [Real.rpow_one]
        _ = X ^ (1 - 5 * theta) :=
          (Real.rpow_sub hXpos 1 (5 * theta)).symm

/-- Every literal dyadic block appearing in the normalized second branch is
bounded by the two monomials consumed by its final power model. -/
theorem normalizedSecondBranch_block_le_fixedPowerModel
    {C D X M M1 A0 a epsilon mu theta sigma1 : ℝ}
    {j : ℕ}
    (hC : 0 ≤ C) (hX : 1 < X) (hM1pos : 0 < M1)
    (hepsilon : 0 < epsilon)
    (hMcoord : M = X ^ mu) (hM1coord : M1 = X ^ theta)
    (htheta0 : 0 ≤ theta) (hthetaUpper : theta ≤ 2 / 11)
    (hj : j < 5) :
    let Nj : ℝ := (2 : ℝ) ^ j * M1 ^ (5 : ℕ)
    let Krho : ℝ :=
      (A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) * (32 : ℝ) ^ (epsilon / 50)
    let Keta : ℝ := (16 : ℝ) ^ (epsilon / 100)
    C *
          (M ^ (epsilon / 5 + 2 * (epsilon / 100)) +
            (Nj * X) ^ (epsilon / 100) * (X / Nj) *
              M ^ (-1 + 1 / a + epsilon / 100 + epsilon / 5)) *
          (A0 ^ (5 : ℕ) * D * (2 * Nj) ^ (epsilon / 100)) ^
            (2 : ℕ) *
          M1 ^ (10 * sigma1) ≤
      C *
        (X ^ (mu * (epsilon / 5 + 2 * (epsilon / 100))) *
            (Krho * X ^ (epsilon / 10)) *
            X ^ (10 * sigma1 * theta) +
          (Keta * X ^ ((epsilon / 100) * (5 * theta + 1))) *
            X ^ (1 - 5 * theta) *
            X ^ (mu * (-1 + 1 / a + epsilon / 100 + epsilon / 5)) *
            (Krho * X ^ (epsilon / 10)) *
            X ^ (10 * sigma1 * theta)) := by
  dsimp only
  let Nj : ℝ := (2 : ℝ) ^ j * M1 ^ (5 : ℕ)
  let Krho : ℝ :=
    (A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) * (32 : ℝ) ^ (epsilon / 50)
  let Keta : ℝ := (16 : ℝ) ^ (epsilon / 100)
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hNj : 0 < Nj := by
    dsimp [Nj]
    positivity
  have hKrho : 0 ≤ Krho := by
    dsimp [Krho]
    positivity
  have hKeta : 0 ≤ Keta := by
    dsimp [Keta]
    positivity
  have hcoeff := fiveBlock_coefficientFactor_sq_le_epsilon_tenth
    (X := X) (M1 := M1) (A0 := A0) (D := D)
    (epsilon := epsilon) (theta := theta) (j := j)
    hX hepsilon.le hthetaUpper hM1coord hj
  have heta := fifthPowerDyadic_etaMultiplier_le
    (X := X) (M1 := M1) (epsilon := epsilon) (theta := theta) (j := j)
    hX hepsilon.le htheta0 hM1coord hj
  have hquot := X_div_fifthPowerDyadic_le_logCoordinate_model
    (X := X) (M1 := M1) (theta := theta) (j := j) hX hM1coord
  have hMsupport :
      M ^ (epsilon / 5 + 2 * (epsilon / 100)) =
        X ^ (mu * (epsilon / 5 + 2 * (epsilon / 100))) := by
    rw [hMcoord, Real.rpow_mul hXpos.le]
  have hMmixed :
      M ^ (-1 + 1 / a + epsilon / 100 + epsilon / 5) =
        X ^ (mu * (-1 + 1 / a + epsilon / 100 + epsilon / 5)) := by
    rw [hMcoord, Real.rpow_mul hXpos.le]
  have hM1sigma :
      M1 ^ (10 * sigma1) = X ^ (10 * sigma1 * theta) := by
    rw [hM1coord]
    calc
      (X ^ theta) ^ (10 * sigma1) = X ^ (theta * (10 * sigma1)) :=
        (Real.rpow_mul hXpos.le theta (10 * sigma1)).symm
      _ = X ^ (10 * sigma1 * theta) := by
        congr 1
        ring
  have hfirst :
      M ^ (epsilon / 5 + 2 * (epsilon / 100)) *
            (A0 ^ (5 : ℕ) * D * (2 * Nj) ^ (epsilon / 100)) ^
              (2 : ℕ) *
            M1 ^ (10 * sigma1) ≤
        X ^ (mu * (epsilon / 5 + 2 * (epsilon / 100))) *
          (Krho * X ^ (epsilon / 10)) *
          X ^ (10 * sigma1 * theta) := by
    rw [hMsupport, hM1sigma]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcoeff
        (Real.rpow_nonneg hXpos.le _))
      (Real.rpow_nonneg hXpos.le _)
  have hsecond :
      (Nj * X) ^ (epsilon / 100) * (X / Nj) *
            M ^ (-1 + 1 / a + epsilon / 100 + epsilon / 5) *
            (A0 ^ (5 : ℕ) * D * (2 * Nj) ^ (epsilon / 100)) ^
              (2 : ℕ) *
            M1 ^ (10 * sigma1) ≤
        (Keta * X ^ ((epsilon / 100) * (5 * theta + 1))) *
          X ^ (1 - 5 * theta) *
          X ^ (mu * (-1 + 1 / a + epsilon / 100 + epsilon / 5)) *
          (Krho * X ^ (epsilon / 10)) *
          X ^ (10 * sigma1 * theta) := by
    rw [hMmixed, hM1sigma]
    have heta' :
        (Nj * X) ^ (epsilon / 100) ≤
          Keta * X ^ ((epsilon / 100) * (5 * theta + 1)) := by
      simpa only [Nj, Keta] using heta
    have hquot' : X / Nj ≤ X ^ (1 - 5 * theta) := by
      simpa only [Nj] using hquot
    have hquot0 : 0 ≤ X / Nj := div_nonneg hXpos.le hNj.le
    have hmixedPow0 : 0 ≤
        X ^ (mu * (-1 + 1 / a + epsilon / 100 + epsilon / 5)) :=
      Real.rpow_nonneg hXpos.le _
    have htargetEta0 : 0 ≤
        Keta * X ^ ((epsilon / 100) * (5 * theta + 1)) := by
      positivity
    gcongr
  have hcombined := add_le_add hfirst hsecond
  have hmul := mul_le_mul_of_nonneg_left hcombined hC
  convert hmul using 1
  all_goals ring

/-- The literal normalized five-block majorant has the fixed power saving
provided by the paper's second-branch key inequality. -/
theorem normalizedSecondBranchFiveBlockMajorant_fixedPowerSaving_model
    {C D X M M1 M2 A0 R a epsilon mu theta phi sigma1 sigma2 : ℝ}
    (hC : 0 ≤ C) (hX : 1 < X)
    (hM : 0 < M) (hM1pos : 0 < M1) (_hM2pos : 0 < M2)
    (hR : 0 ≤ R)
    (hRbound : R ≤ M ^ (1 - 1 / a + epsilon / 100))
    (hepsilon : 0 < epsilon) (hepsilonUpper : epsilon ≤ 1 / 10)
    (ha : 0 < a) (haLower : 12 / 11 ≤ a) (haUpper : a ≤ 11 / 10)
    (hMcoord : M = X ^ mu) (hM1coord : M1 = X ^ theta)
    (hM2coord : M2 = X ^ phi)
    (hmuLower : 1 - epsilon / 100 ≤ mu) (hmuUpper : mu ≤ 1)
    (htheta0 : 0 ≤ theta) (hthetaUpper : theta ≤ 2 / 11)
    (hkey :
      1 / a + 4 * epsilon ≤
        (5 - 8 * sigma1) * theta + 2 * sigma2 * phi) :
    secondBranchFiveBlockMajorant C D (epsilon / 100) (epsilon / 100)
          X M M1 A0 R /
        ((M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) *
          ((M1 ^ (-sigma1)) ^ (5 : ℕ)) ^ (2 : ℕ)) ≤
      25 * C *
        (((A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) *
              (32 : ℝ) ^ (epsilon / 50)) +
          (16 : ℝ) ^ (epsilon / 100) *
            ((A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) *
              (32 : ℝ) ^ (epsilon / 50))) *
        (M1 ^ (2 * sigma1) * M2 ^ (2 * sigma2)) *
        X ^ (-3 * epsilon) := by
  let Krho : ℝ :=
    (A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) * (32 : ℝ) ^ (epsilon / 50)
  let Keta : ℝ := (16 : ℝ) ^ (epsilon / 100)
  let targetX : ℝ :=
    (X ^ (2 * sigma1 * theta) * X ^ (2 * sigma2 * phi)) *
      X ^ (-3 * epsilon)
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hKrho : 0 ≤ Krho := by dsimp [Krho]; positivity
  have hKeta : 0 ≤ Keta := by dsimp [Keta]; positivity
  have hmajor := normalizedSecondBranchFiveBlockMajorant_le_paperMonomials
    (C := C) (D := D) (rho := epsilon / 100) (eta := epsilon / 100)
    (X := X) (M := M) (M1 := M1) (A0 := A0) (R := R)
    (a := a) (epsilon := epsilon) (sigma := sigma1)
    (supportSlack := epsilon / 100)
    hC hM hM1pos hXpos.le hR hRbound
  have hmodel := secondBranch_twoTerms_fixedPowerSaving_model
    (X := X) (Kfirst := Krho) (Keta := Keta) (Krho := Krho)
    (a := a) (epsilon := epsilon) (mu := mu) (theta := theta)
    (sigma1 := sigma1) (sigma2 := sigma2) (phi := phi)
    hX hKrho hKeta hKrho hepsilon hepsilonUpper ha haLower haUpper
    hmuLower hmuUpper hthetaUpper hkey
  have hsum :
      ∑ j ∈ Finset.range 5,
        (let Nj : ℝ := (2 : ℝ) ^ j * M1 ^ (5 : ℕ)
         C *
          (M ^ (epsilon / 5 + 2 * (epsilon / 100)) +
            (Nj * X) ^ (epsilon / 100) * (X / Nj) *
              M ^ (-1 + 1 / a + epsilon / 100 + epsilon / 5)) *
          (A0 ^ (5 : ℕ) * D * (2 * Nj) ^ (epsilon / 100)) ^
            (2 : ℕ) *
          M1 ^ (10 * sigma1)) ≤
        ∑ _j ∈ Finset.range 5,
          C * ((Krho + Keta * Krho) * targetX) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjlt : j < 5 := Finset.mem_range.mp hj
    have hblock := normalizedSecondBranch_block_le_fixedPowerModel
      (C := C) (D := D) (X := X) (M := M) (M1 := M1) (A0 := A0)
      (a := a) (epsilon := epsilon) (mu := mu) (theta := theta)
      (sigma1 := sigma1) (j := j)
      hC hX hM1pos hepsilon hMcoord hM1coord htheta0
      hthetaUpper hjlt
    dsimp only at hblock ⊢
    calc
      C *
            (M ^ (epsilon / 5 + 2 * (epsilon / 100)) +
              (((2 : ℝ) ^ j * M1 ^ (5 : ℕ)) * X) ^
                    (epsilon / 100) *
                  (X / ((2 : ℝ) ^ j * M1 ^ (5 : ℕ))) *
                M ^ (-1 + 1 / a + epsilon / 100 + epsilon / 5)) *
            (A0 ^ (5 : ℕ) * D *
                (2 * ((2 : ℝ) ^ j * M1 ^ (5 : ℕ))) ^
                  (epsilon / 100)) ^ (2 : ℕ) *
            M1 ^ (10 * sigma1) ≤
          C *
            (X ^ (mu * (epsilon / 5 + 2 * (epsilon / 100))) *
                (Krho * X ^ (epsilon / 10)) *
                X ^ (10 * sigma1 * theta) +
              (Keta * X ^ ((epsilon / 100) * (5 * theta + 1))) *
                X ^ (1 - 5 * theta) *
                X ^ (mu *
                  (-1 + 1 / a + epsilon / 100 + epsilon / 5)) *
                (Krho * X ^ (epsilon / 10)) *
                X ^ (10 * sigma1 * theta)) := by
            simpa only [Krho, Keta] using hblock
      _ ≤ C * ((Krho + Keta * Krho) * targetX) := by
        dsimp [targetX]
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_left hmodel hC)
  have hsumEval :
      ∑ _j ∈ Finset.range 5,
          C * ((Krho + Keta * Krho) * targetX) =
        5 * (C * ((Krho + Keta * Krho) * targetX)) := by
    simp
  have hcoordinate :
      targetX =
        (M1 ^ (2 * sigma1) * M2 ^ (2 * sigma2)) *
          X ^ (-3 * epsilon) := by
    have hM1target :
        M1 ^ (2 * sigma1) = X ^ (2 * sigma1 * theta) := by
      rw [hM1coord]
      calc
        (X ^ theta) ^ (2 * sigma1) = X ^ (theta * (2 * sigma1)) :=
          (Real.rpow_mul hXpos.le theta (2 * sigma1)).symm
        _ = X ^ (2 * sigma1 * theta) := by
          congr 1
          ring
    have hM2target :
        M2 ^ (2 * sigma2) = X ^ (2 * sigma2 * phi) := by
      rw [hM2coord]
      calc
        (X ^ phi) ^ (2 * sigma2) = X ^ (phi * (2 * sigma2)) :=
          (Real.rpow_mul hXpos.le phi (2 * sigma2)).symm
        _ = X ^ (2 * sigma2 * phi) := by
          congr 1
          ring
    dsimp [targetX]
    rw [hM1target, hM2target]
  calc
    secondBranchFiveBlockMajorant C D (epsilon / 100) (epsilon / 100)
          X M M1 A0 R /
        ((M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) *
          ((M1 ^ (-sigma1)) ^ (5 : ℕ)) ^ (2 : ℕ)) ≤
      5 * ∑ j ∈ Finset.range 5,
        (let Nj : ℝ := (2 : ℝ) ^ j * M1 ^ (5 : ℕ)
         C *
          (M ^ (epsilon / 5 + 2 * (epsilon / 100)) +
            (Nj * X) ^ (epsilon / 100) * (X / Nj) *
              M ^ (-1 + 1 / a + epsilon / 100 + epsilon / 5)) *
          (A0 ^ (5 : ℕ) * D * (2 * Nj) ^ (epsilon / 100)) ^
            (2 : ℕ) *
          M1 ^ (10 * sigma1)) := hmajor
    _ ≤ 5 * ∑ _j ∈ Finset.range 5,
          C * ((Krho + Keta * Krho) * targetX) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 25 * C * (Krho + Keta * Krho) * targetX := by
      rw [hsumEval]
      ring
    _ = 25 * C *
        (((A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) *
              (32 : ℝ) ^ (epsilon / 50)) +
          (16 : ℝ) ^ (epsilon / 100) *
            ((A0 ^ (5 : ℕ) * D) ^ (2 : ℕ) *
              (32 : ℝ) ^ (epsilon / 50))) *
        (M1 ^ (2 * sigma1) * M2 ^ (2 * sigma2)) *
      X ^ (-3 * epsilon) := by
      rw [hcoordinate]
      dsimp [Krho, Keta]
      ring

/-- Exact normalization of the real and imaginary contributions in the
complex first branch. -/
theorem firstBranchComplexMajorant_normalize
    {CRe CIm R M N T eta ARe AIm q v : ℝ}
    (hq : q ≠ 0) (hv : v ≠ 0) :
    firstBranchComplexMajorant CRe CIm R M N T eta ARe AIm q v =
      4 * (CRe * ARe ^ (2 : ℕ) + CIm * AIm ^ (2 : ℕ)) *
          ((R / M) ^ (2 : ℕ) +
            (N * T) ^ eta *
              (R * T / (M ^ (2 : ℕ) * N))) /
        (q ^ (2 : ℕ) * v ^ (2 : ℕ)) := by
  unfold firstBranchComplexMajorant
  field_simp [hq, hv]
  ring

/-- Exact separation of the two Heath--Brown contributions after combining
the real and imaginary coefficient calls. -/
theorem firstBranchComplexMajorant_split
    {CRe CIm R M N T eta ARe AIm q v : ℝ}
    (hq : q ≠ 0) (hv : v ≠ 0) :
    firstBranchComplexMajorant CRe CIm R M N T eta ARe AIm q v =
      4 * (CRe * ARe ^ (2 : ℕ) + CIm * AIm ^ (2 : ℕ)) *
          (R / M) ^ (2 : ℕ) /
        (q ^ (2 : ℕ) * v ^ (2 : ℕ)) +
      4 * (CRe * ARe ^ (2 : ℕ) + CIm * AIm ^ (2 : ℕ)) *
          ((N * T) ^ eta *
            (R * T / (M ^ (2 : ℕ) * N))) /
        (q ^ (2 : ℕ) * v ^ (2 : ℕ)) := by
  rw [firstBranchComplexMajorant_normalize hq hv]
  ring

/-- Any fixed power saving is eventually stronger than the paper's
`exp (-(log log X)^7)` saving. -/
theorem eventually_rpow_neg_le_exp_neg_loglog_seven
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ X : ℝ in atTop,
      X ^ (-delta) ≤
        Real.exp (-(Real.log (Real.log X)) ^ (7 : ℕ)) := by
  have hsmallRaw :=
    (isLittleO_log_rpow_rpow_atTop (7 : ℝ)
      (by norm_num : (0 : ℝ) < 1)).bound hdelta
  have hsmall : ∀ᶠ X : ℝ in atTop,
      ‖(Real.log (Real.log X)) ^ (7 : ℝ)‖ ≤
        delta * ‖(Real.log X) ^ (1 : ℝ)‖ :=
    Real.tendsto_log_atTop.eventually hsmallRaw
  filter_upwards [hsmall,
      eventually_ge_atTop (Real.exp (Real.exp 1))] with X hbound hX
  have hXpos : 0 < X := (Real.exp_pos _).trans_le hX
  have hlogXone : 1 ≤ Real.log X := by
    have hlogXge : Real.exp 1 ≤ Real.log X := by
      rw [← Real.log_exp (Real.exp 1)]
      exact Real.log_le_log (Real.exp_pos _) hX
    linarith [Real.exp_one_gt_two]
  have hlogXnonneg : 0 ≤ Real.log X := zero_le_one.trans hlogXone
  have hloglognonneg : 0 ≤ Real.log (Real.log X) :=
    Real.log_nonneg hlogXone
  have hpowerR :
      (Real.log (Real.log X)) ^ (7 : ℝ) ≤ delta * Real.log X := by
    simpa only [Real.rpow_one,
      Real.norm_of_nonneg (Real.rpow_nonneg hloglognonneg _),
      Real.norm_of_nonneg hlogXnonneg] using hbound
  have hpower :
      (Real.log (Real.log X)) ^ (7 : ℕ) ≤ delta * Real.log X := by
    rw [← Real.rpow_natCast]
    exact hpowerR
  rw [Real.rpow_def_of_pos hXpos]
  apply Real.exp_le_exp.mpr
  calc
    Real.log X * -delta = -(delta * Real.log X) := by ring
    _ ≤ -(Real.log (Real.log X)) ^ (7 : ℕ) := neg_le_neg hpower

/-- A fixed nonnegative constant is harmless: half of a fixed power saving
absorbs it and the other half still dominates the logarithmic exponential. -/
theorem eventually_const_mul_rpow_neg_le_exp_neg_loglog_seven
    {K delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ X : ℝ in atTop,
      K * X ^ (-delta) ≤
        Real.exp (-(Real.log (Real.log X)) ^ (7 : ℕ)) := by
  have hhalf : 0 < delta / 2 := by positivity
  have hKabsorb : ∀ᶠ X : ℝ in atTop, K ≤ X ^ (delta / 2) :=
    (tendsto_rpow_atTop hhalf).eventually_ge_atTop K
  filter_upwards [hKabsorb,
      eventually_rpow_neg_le_exp_neg_loglog_seven hhalf,
      eventually_gt_atTop (0 : ℝ)] with X hKX hsaving hX
  calc
    K * X ^ (-delta) ≤ X ^ (delta / 2) * X ^ (-delta) :=
      mul_le_mul_of_nonneg_right hKX (Real.rpow_nonneg hX.le _)
    _ = X ^ (-(delta / 2)) := by
      rw [← Real.rpow_add hX]
      congr 1
      ring
    _ ≤ Real.exp (-(Real.log (Real.log X)) ^ (7 : ℕ)) := hsaving

/-- Uniform transfer from a fixed power-saving majorant to the exact saving
printed in the paper.  The base quantity may vary with `X`. -/
theorem eventually_majorant_le_target_mul_exp_of_powerSaving
    {K delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ X : ℝ in atTop, ∀ majorant target : ℝ,
      0 ≤ target →
      majorant ≤ K * target * X ^ (-delta) →
      majorant ≤ target *
        Real.exp (-(Real.log (Real.log X)) ^ (7 : ℕ)) := by
  filter_upwards
      [eventually_const_mul_rpow_neg_le_exp_neg_loglog_seven
        (K := K) hdelta] with X hsaving
  intro majorant target htarget hmajorant
  calc
    majorant ≤ K * target * X ^ (-delta) := hmajorant
    _ = target * (K * X ^ (-delta)) := by ring
    _ ≤ target *
        Real.exp (-(Real.log (Real.log X)) ^ (7 : ℕ)) :=
      mul_le_mul_of_nonneg_left hsaving htarget

/-- The outer factor five and the five dyadic blocks cost only `25` times a
uniform block majorant. -/
theorem secondBranchFiveBlockMajorant_le_twentyFive_mul
    {C D rho eta T sparseScale baseScale A0 R K : ℝ}
    (hblock : ∀ j ∈ Finset.range 5,
      C *
          (((R / sparseScale) ^ (2 : ℕ) +
            (((2 : ℝ) ^ j * baseScale ^ (5 : ℕ)) * T) ^ eta *
              (R * T /
                (sparseScale ^ (2 : ℕ) *
                  ((2 : ℝ) ^ j * baseScale ^ (5 : ℕ))))) *
            (A0 ^ (5 : ℕ) * D *
              (2 * ((2 : ℝ) ^ j * baseScale ^ (5 : ℕ))) ^ rho) ^
                (2 : ℕ)) ≤ K) :
    secondBranchFiveBlockMajorant C D rho eta T sparseScale
        baseScale A0 R ≤ 25 * K := by
  unfold secondBranchFiveBlockMajorant
  calc
    5 * ∑ j ∈ Finset.range 5,
        C *
          (((R / sparseScale) ^ (2 : ℕ) +
            (((2 : ℝ) ^ j * baseScale ^ (5 : ℕ)) * T) ^ eta *
              (R * T /
                (sparseScale ^ (2 : ℕ) *
                  ((2 : ℝ) ^ j * baseScale ^ (5 : ℕ))))) *
            (A0 ^ (5 : ℕ) * D *
              (2 * ((2 : ℝ) ^ j * baseScale ^ (5 : ℕ))) ^ rho) ^
                (2 : ℕ))
        ≤
      5 * ∑ _j ∈ Finset.range 5, K := by
        gcongr with j hj
        exact hblock j hj
    _ = 25 * K := by simp; ring

/-- The exact pointwise lower bound needed when the second branch inserts
the fifth power of the first long polynomial. -/
theorem fifthPower_integrand_lower
    {q v : ℝ} {Q A : ℂ} (hq : 0 ≤ q) (hv : 0 ≤ v)
    (hQ : q ≤ ‖Q‖) (hA : v ≤ ‖A‖) :
    q ^ (2 : ℕ) * (v ^ (5 : ℕ)) ^ (2 : ℕ) ≤
      ‖Q‖ ^ (2 : ℕ) * ‖A ^ (5 : ℕ)‖ ^ (2 : ℕ) := by
  rw [norm_pow]
  exact mul_le_mul
    (pow_le_pow_left₀ hq hQ 2)
    (pow_le_pow_left₀ (pow_nonneg hv 5)
      (pow_le_pow_left₀ hv hA 5) 2)
    (sq_nonneg (v ^ (5 : ℕ))) (sq_nonneg ‖Q‖)

/-- Fixed-scale analytic package for the sparse propagation argument.

It uses the literal normalized dyadic-prime power for the sparse factor,
derives its pointwise lower bound from the paper's floor choice, invokes the
complex first branch and real fifth-power second branch, and appends the
endpoint dichotomy.  Thus no analytic estimate remains hidden in the
conclusion.  The hypotheses are precisely the scale geometry that still has
to be verified for the moving paper parameters. -/
theorem sparsePropagation_fixedScale_package
    (inputs : ExternalInputs) {eta rho : ℝ}
    (heta : 0 < eta) (hrho : 0 < rho)
    {X P M M1 M2 A0 B epsilon a theta sigma1 sigma2
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
    (hepsilon : 0 ≤ epsilon)
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
    (_htheta0 : 0 ≤ theta) (_htheta1 : theta ≤ 1)
    (hresidualError :
      residualError = firstError + scaleError * (1 - 1 / a))
    (hkey : 1 - 1 / a - residualError ≤ theta * (1 - 2 * sigma1) →
      1 / a + keyError < secondBranchKeyExponent theta sigma1 sigma2) :
    (∃ CRe CIm : ℝ, 0 < CRe ∧ 0 < CIm ∧
      volume.real E ≤
        firstBranchComplexMajorant CRe CIm
          ((primePowerSupport (dyadicPrimes P) k).card : ℝ)
          M M2 X eta
          (dyadicRealCoefficientSup (fun n ↦ (beta n).re) M2)
          (dyadicRealCoefficientSup (fun n ↦ (beta n).im) M2)
          (M ^ (-epsilon / 10 - 1 / a))
          (M2 ^ (-sigma2))) ∧
    (∃ C D : ℝ, 0 < C ∧ 1 ≤ D ∧
      volume.real E *
          ((M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) *
            ((M1 ^ (-sigma1)) ^ (5 : ℕ)) ^ (2 : ℕ)) ≤
        secondBranchFiveBlockMajorant C D rho eta X M M1 A0
          ((primePowerSupport (dyadicPrimes P) k).card : ℝ)) ∧
    (M ^ (epsilon / 5) ≤
        M1 ^ (2 * sigma1) / X ^ (epsilon ^ 2)) ∧
    (M1 ^ (1 - 2 * sigma1) ≤
        X ^ (-firstError) * M ^ (1 - 1 / a) ∨
      X ^ (1 / a + keyError) ≤
        (X ^ theta) ^ (5 - 8 * sigma1) *
          (X ^ (1 - theta)) ^ (2 * sigma2)) := by
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
  have hfirst := measure_set_le_firstBranchRaw_complex
    inputs.matomakiTeravainenLemmaThreeFour heta hM hMX hM2
    (Real.rpow_pos_of_pos hMpos _) (Real.rpow_pos_of_pos hM2pos _)
    hSprime hsupport hdeleteFirst hEmeas hEsub hQlower hM2lowerOnE
  rcases hfirst with ⟨CRe, CIm, hCRe, hCIm, hfirstBound⟩
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
  obtain ⟨C, hC, hsecondC⟩ :=
    secondBranch_fifthPower_largeValueMeasure inputs heta hrho
  obtain ⟨D, hD, hsecondD⟩ := hsecondC B hb.1
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
  have hsecondBound := hsecondD X M M1 A0
    (primePowerSupport (dyadicPrimes P) k) (dyadicInterval M1)
    (fun n ↦ (primePowerCoefficient (dyadicPrimes P) k n : ℂ)) b E
    ((M ^ (-epsilon / 10 - 1 / a)) ^ (2 : ℕ) *
      ((M1 ^ (-sigma1)) ^ (5 : ℕ)) ^ (2 : ℕ))
    hM1 hb hbaseSupport hM hMX hsupport hcoeff hblocks hdeleteSecond
    hEmeas hEsub (by positivity) hsecondLower
  have hfirstAlways := firstBranch_first_condition_of_power_bounds
    hX.le hMpos.le hMX hM1lower hepsilon hsigmaStrong
  have hdichotomy := firstOrSecondBranch_exactPowerDichotomy_of_key
    hX hMpos hM1 ha htheta hMExponent hresidualError hkey
  refine ⟨?_, ?_, hfirstAlways, hdichotomy⟩
  · refine ⟨CRe, CIm, hCRe, hCIm, ?_⟩
    simpa [firstBranchComplexMajorant] using hfirstBound
  · refine ⟨C, D, hC, hD, ?_⟩
    simpa [secondBranchFiveBlockMajorant] using hsecondBound

def propagationModule : ProofModule :=
  { name := "Sparse.Propagation"
    paperLocation := "Section 6.1"
    purpose :=
      "Track the endpoint error budget and package the normalized sparse polynomial, both complete analytic branches, and their exact dichotomy at fixed verified scales. Moving support, deletion, Q-lower-bound geometry, the log(M)/log(X) lower asymptotic, the real dyadic structured-coefficient bridge, exact Type-II convolution factorization, literal product-scale substitution, and both explicit branch-majorant power savings are proved. GlobalComponentCancellation shows that no componentwise upper-tail estimate is required; PropagationParameters supplies the uniform moving-parameter form."
    dependsOn :=
      [ "Sparse.FirstBranch",
        "Sparse.SupportGeometry",
        "Sparse.QLowerBound",
        "Sparse.MagnitudeBins",
        "Sparse.ComplexCoefficientSplit",
        "Sparse.ResidualRange",
        "Sparse.SecondBranch",
        "Sparse.EndpointAlgebra",
        "Sparse.EndpointSaturation",
        "TypeII.PolynomialLengthRanges" ]
    status := .proved }

end

end Sparse
end ExactSemiprimes
