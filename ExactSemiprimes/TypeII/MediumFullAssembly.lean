import ExactSemiprimes.TypeII.MediumFiniteUniformization

/-! # End-to-end assembly of one powered medium bin -/

namespace ExactSemiprimes
namespace TypeII

noncomputable section

/-- The pointwise powered-slice selector and the uniform prepared hybrid
bound combine to control a whole medium bin.  The loss from shifting the
large-value exponent is displayed as `2 * shift` in the final saving, and
the height-dependent choice of slice costs exactly the factor `ell`. -/
theorem poweredFirstMediumBin_cardinality_from_uniformPrepared
    {thresholdLoss B eps κ C T₀ A shift tau₁ tau₂ T : ℝ}
    {K ell M : ℕ} {a₁ : ℕ → ℂ} {R : Finset ℝ}
    (hA : 1 ≤ A)
    (hUniform : ∀ e : ℕ, 1 ≤ e → e ≤ K →
      MediumPreparedPoweredAt
        thresholdLoss B eps e κ ⟨A, hA⟩ C T₀)
    (hell : 1 ≤ ell) (hellK : ell ≤ K)
    (hM : 1 ≤ M)
    (hT : T₀ ≤ T)
    (hPlower : T ^ (9 / 11 - 10 * eps) ≤ ((M ^ ell : ℕ) : ℝ))
    (hPupper : (((2 * M) ^ ell : ℕ) : ℝ) ≤ T ^ (1 - eps / 10))
    (hshift : 0 ≤ shift)
    (habsorb : (ell : ℝ) ≤ (((M : ℝ) ^ ell) ^ shift))
    (htau₁ : 0 ≤ tau₁)
    (htauLower : 10 * eps ≤ tau₁ + shift)
    (htauUpper : tau₁ + shift ≤ 17 / 70 - thresholdLoss * eps)
    (horder : tau₁ + shift ≤ tau₂)
    (ha₁ : IsDivisorBoundedByConstant B A a₁)
    (hspaced : IsOneSpaced (↑R : Set ℝ))
    (hR : ∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T)
    (hlarge : ∀ t ∈ R,
      (M : ℝ) ^ (-tau₁) <
        ‖dyadicDirichletPolynomial a₁ (M : ℝ) (onePlusIT t)‖) :
    (R.card : ℝ) ≤
      (ell : ℝ) * C * T ^
        (2 * min tau₁ tau₂ - (κ - 2 * shift)) := by
  classical
  let Large : ℕ → ℝ → Prop := fun j t ↦
    let P := naturalOpenClosedSliceBase M ell j
    (P : ℝ) ^ (-(tau₁ + shift)) <
      ‖dyadicDirichletPolynomial
        (powerConvolutionCoefficient a₁ (dyadicInterval (M : ℝ)) ell)
        (P : ℝ) (onePlusIT t)‖
  have hselect : ∀ t ∈ R, ∃ j < ell, Large j t := by
    intro t ht
    obtain ⟨j, hj, P, hP, _hPone, _hPlo, _hPhi, hlargePiece⟩ :=
      exists_large_poweredDyadicPolynomial_shiftedThreshold_naturalScale
        a₁ hM hell htau₁ hshift habsorb (onePlusIT t) (hlarge t ht)
    refine ⟨j, hj, ?_⟩
    dsimp only [Large]
    simpa only [hP] using hlargePiece
  have hslice : ∀ j < ell,
      (((R.filter fun t ↦ Large j t).card : ℕ) : ℝ) ≤
        C * T ^ (2 * min (tau₁ + shift) tau₂ - κ) := by
    intro j hj
    let P := naturalOpenClosedSliceBase M ell j
    have hPbounds := naturalOpenClosedSliceBase_bounds (M := M) hj
    have hPone : 1 ≤ P := one_le_naturalOpenClosedSliceBase hM
    have hPlower' : T ^ (9 / 11 - 10 * eps) ≤ (P : ℝ) := by
      apply hPlower.trans
      exact_mod_cast hPbounds.1
    have hPupper' : (P : ℝ) ≤ T ^ (1 - eps / 10) := by
      apply (show (P : ℝ) ≤ (((2 * M) ^ ell : ℕ) : ℝ) by
        exact_mod_cast hPbounds.2).trans
      exact hPupper
    have hspaced' :
        IsOneSpaced (↑(R.filter fun t ↦ Large j t) : Set ℝ) := by
      apply hspaced.mono
      intro t ht
      exact (Finset.mem_filter.mp ht).1
    have hR' : ∀ t ∈ R.filter fun t ↦ Large j t,
        t ∈ Set.Icc (0 : ℝ) T := by
      intro t ht
      exact hR t (Finset.mem_filter.mp ht).1
    have hlarge' : ∀ t ∈ R.filter fun t ↦ Large j t,
        (P : ℝ) ^ (-(tau₁ + shift)) <
          ‖dyadicDirichletPolynomial
            (powerConvolutionCoefficient a₁ (dyadicInterval (M : ℝ)) ell)
            (P : ℝ) (onePlusIT t)‖ := by
      intro t ht
      exact (Finset.mem_filter.mp ht).2
    exact hUniform ell hell hellK T M P (tau₁ + shift) tau₂ a₁
      (R.filter fun t ↦ Large j t) hT hM hPone hPlower' hPupper'
      htauLower htauUpper horder ha₁ hspaced' hR' hlarge'
  have hcover := card_le_ell_mul_of_heightSlice_cover
    R Large hselect hslice
  have horderOriginal : tau₁ ≤ tau₂ := by linarith
  rw [min_eq_left horder] at hcover
  rw [min_eq_left horderOriginal]
  convert hcover using 1
  ring_nf

/-- After the previous whole-bin cardinality estimate, the already-proved
negative-power cancellation gives the weighted contribution of that bin.
All reserve-spending is explicit: `2*shift` is spent on slice selection and
the remaining saving must dominate the product-length error and `delta`. -/
theorem poweredFirstMediumBin_weighted_from_uniformPrepared
    {thresholdLoss B eps κ C T₀ A shift tau₁ tau₂ T : ℝ}
    {K ell M : ℕ} {M₂ eta₁ eta₂ xi delta : ℝ}
    {a₁ : ℕ → ℂ} {R : Finset ℝ}
    (hA : 1 ≤ A)
    (hUniform : ∀ e : ℕ, 1 ≤ e → e ≤ K →
      MediumPreparedPoweredAt
        thresholdLoss B eps e κ ⟨A, hA⟩ C T₀)
    (hell : 1 ≤ ell) (hellK : ell ≤ K)
    (hM : 1 ≤ M)
    (hT₀ : T₀ ≤ T) (hTone : 1 < T)
    (hModeledM : (M : ℝ) = T ^ eta₁) (hModeledM₂ : M₂ = T ^ eta₂)
    (heta₁ : 0 ≤ eta₁) (heta₂ : 0 ≤ eta₂)
    (hproduct : T ^ (1 - xi) ≤ (M : ℝ) * M₂)
    (hPlower : T ^ (9 / 11 - 10 * eps) ≤ ((M ^ ell : ℕ) : ℝ))
    (hPupper : (((2 * M) ^ ell : ℕ) : ℝ) ≤ T ^ (1 - eps / 10))
    (hshift : 0 ≤ shift)
    (habsorb : (ell : ℝ) ≤ (((M : ℝ) ^ ell) ^ shift))
    (htau₁ : 0 ≤ tau₁) (htau₂ : 0 ≤ tau₂)
    (htauLower : 10 * eps ≤ tau₁ + shift)
    (htauUpper : tau₁ + shift ≤ 17 / 70 - thresholdLoss * eps)
    (horder : tau₁ + shift ≤ tau₂)
    (hgap : 2 * xi * min tau₁ tau₂ + delta ≤ κ - 2 * shift)
    (hC : 0 < C)
    (ha₁ : IsDivisorBoundedByConstant B A a₁)
    (hspaced : IsOneSpaced (↑R : Set ℝ))
    (hR : ∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T)
    (hlarge : ∀ t ∈ R,
      (M : ℝ) ^ (-tau₁) <
        ‖dyadicDirichletPolynomial a₁ (M : ℝ) (onePlusIT t)‖) :
    (R.card : ℝ) * (M : ℝ) ^ (-2 * tau₁) * M₂ ^ (-2 * tau₂) ≤
      ((ell : ℝ) * C) * T ^ (-delta) := by
  have hcard := poweredFirstMediumBin_cardinality_from_uniformPrepared
    hA hUniform hell hellK hM hT₀ hPlower hPupper hshift habsorb htau₁
    htauLower htauUpper horder ha₁ hspaced hR hlarge
  have hC' : 0 ≤ (ell : ℝ) * C :=
    mul_nonneg (Nat.cast_nonneg ell) hC.le
  exact weightedMediumCardinality_le_negativePower hTone hModeledM
    hModeledM₂ heta₁ heta₂ hproduct htau₁ htau₂ hgap hC' (by
      simpa only [mul_assoc] using hcard)

/-! ## Closing the transition strip with the unpowered second branch -/

/-- Fixed-parameter universal tail of the direct second-polynomial branch. -/
def MediumUnpoweredSecondAt
    (thresholdLoss B eps κ : ℝ) (A : {x : ℝ // 1 ≤ x})
    (C T₀ : ℝ) : Prop :=
  ∀ (T : ℝ) (N₂ : ℕ) (tau₁ tau₂ : ℝ) (a₂ : ℕ → ℂ)
      (R : Finset ℝ),
    T₀ ≤ T → 1 ≤ N₂ →
    T ^ (9 / 11 - 10 * eps) ≤ (N₂ : ℝ) →
    (N₂ : ℝ) ≤ T ^ (1 - eps / 10) →
    10 * eps ≤ tau₂ →
    tau₂ ≤ 17 / 70 - thresholdLoss * eps →
    tau₂ < tau₁ →
    IsDivisorBoundedByConstant B A.1 a₂ →
    IsOneSpaced (↑R : Set ℝ) →
    (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
    (∀ t ∈ R,
      (N₂ : ℝ) ^ (-tau₂) <
        ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ) (onePlusIT t)‖) →
    (R.card : ℝ) ≤ C * T ^ (2 * min tau₁ tau₂ - κ)

/-- Raising only the first entry of a minimum by a nonnegative shift raises
the minimum by at most that shift. -/
theorem min_add_left_le_min_add
    {x y shift : ℝ} (hshift : 0 ≤ shift) :
    min (x + shift) y ≤ min x y + shift := by
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy]
    exact min_le_left _ _
  · have hyx : y ≤ x := le_of_not_ge hxy
    rw [min_eq_right hyx]
    exact (min_le_right (x + shift) y).trans (by linarith)

/-- The split at `tau₁ + shift` has no uncovered transition strip.  On the
first side the powered selector applies; on the complementary side the raw
second-polynomial hybrid estimate applies.  The upper threshold is required
only for the smaller of `tau₁ + shift` and `tau₂`, exactly matching the
pointwise large-value disjunction in the outer Type-II argument.  Both sides
give the unshifted minimum with saving `κ - 2*shift`. -/
theorem mediumBin_cardinality_from_uniformPowered_and_direct
    {thresholdLoss B eps κ C T₀ A shift tau₁ tau₂ T : ℝ}
    {K ell M N₂ : ℕ} {a₁ a₂ : ℕ → ℂ} {R : Finset ℝ}
    (hA : 1 ≤ A)
    (hPowered : ∀ e : ℕ, 1 ≤ e → e ≤ K →
      MediumPreparedPoweredAt
        thresholdLoss B eps e κ ⟨A, hA⟩ C T₀)
    (hDirect : MediumUnpoweredSecondAt
      thresholdLoss B eps κ ⟨A, hA⟩ C T₀)
    (hell : 1 ≤ ell) (hellK : ell ≤ K)
    (hM : 1 ≤ M) (hN₂ : 1 ≤ N₂)
    (hT₀ : T₀ ≤ T) (hTone : 1 ≤ T)
    (hPlower : T ^ (9 / 11 - 10 * eps) ≤ ((M ^ ell : ℕ) : ℝ))
    (hPupper : (((2 * M) ^ ell : ℕ) : ℝ) ≤ T ^ (1 - eps / 10))
    (hN₂lower : T ^ (9 / 11 - 10 * eps) ≤ (N₂ : ℝ))
    (hN₂upper : (N₂ : ℝ) ≤ T ^ (1 - eps / 10))
    (hshift : 0 ≤ shift)
    (habsorb : (ell : ℝ) ≤ (((M : ℝ) ^ ell) ^ shift))
    (htau₁ : 0 ≤ tau₁)
    (htauShiftLower : 10 * eps ≤ tau₁ + shift)
    (htauMinUpper : min (tau₁ + shift) tau₂ ≤
      17 / 70 - thresholdLoss * eps)
    (htau₂Lower : 10 * eps ≤ tau₂)
    (ha₁ : IsDivisorBoundedByConstant B A a₁)
    (ha₂ : IsDivisorBoundedByConstant B A a₂)
    (hC : 0 ≤ C)
    (hspaced : IsOneSpaced (↑R : Set ℝ))
    (hR : ∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T)
    (hlarge₁ : ∀ t ∈ R,
      (M : ℝ) ^ (-tau₁) <
        ‖dyadicDirichletPolynomial a₁ (M : ℝ) (onePlusIT t)‖)
    (hlarge₂ : ∀ t ∈ R,
      (N₂ : ℝ) ^ (-tau₂) <
        ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ) (onePlusIT t)‖) :
    (R.card : ℝ) ≤
      (ell : ℝ) * C * T ^
        (2 * min tau₁ tau₂ - (κ - 2 * shift)) := by
  by_cases horder : tau₁ + shift ≤ tau₂
  · have htauShiftUpper : tau₁ + shift ≤
        17 / 70 - thresholdLoss * eps := by
      simpa only [min_eq_left horder] using htauMinUpper
    exact poweredFirstMediumBin_cardinality_from_uniformPrepared
      hA hPowered hell hellK hM hT₀ hPlower hPupper hshift habsorb
      htau₁ htauShiftLower htauShiftUpper horder ha₁ hspaced hR hlarge₁
  · have hreverse : tau₂ < tau₁ + shift := lt_of_not_ge horder
    have htau₂Upper : tau₂ ≤ 17 / 70 - thresholdLoss * eps := by
      simpa only [min_eq_right hreverse.le] using htauMinUpper
    have hcard := hDirect T N₂ (tau₁ + shift) tau₂ a₂ R hT₀ hN₂
      hN₂lower hN₂upper htau₂Lower htau₂Upper hreverse ha₂ hspaced hR
      hlarge₂
    have hmin := min_add_left_le_min_add
      (x := tau₁) (y := tau₂) hshift
    have hexponent :
        2 * min (tau₁ + shift) tau₂ - κ ≤
          2 * min tau₁ tau₂ - (κ - 2 * shift) := by
      linarith
    have hpower := Real.rpow_le_rpow_of_exponent_le hTone hexponent
    have hellReal : (1 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hell
    have hCincrease : C ≤ (ell : ℝ) * C := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hellReal) hC]
    calc
      (R.card : ℝ) ≤ C * T ^ (2 * min (tau₁ + shift) tau₂ - κ) := hcard
      _ ≤ C * T ^ (2 * min tau₁ tau₂ - (κ - 2 * shift)) :=
        mul_le_mul_of_nonneg_left hpower hC
      _ ≤ (ell : ℝ) * C *
          T ^ (2 * min tau₁ tau₂ - (κ - 2 * shift)) :=
        mul_le_mul_of_nonneg_right hCincrease
          (Real.rpow_nonneg (by linarith) _)

/-- Weighted form of the complete shifted-order split. -/
theorem mediumBin_weighted_from_uniformPowered_and_direct
    {thresholdLoss B eps κ C T₀ A shift tau₁ tau₂ T : ℝ}
    {K ell M N₂ : ℕ} {eta₁ eta₂ xi delta : ℝ}
    {a₁ a₂ : ℕ → ℂ} {R : Finset ℝ}
    (hA : 1 ≤ A)
    (hPowered : ∀ e : ℕ, 1 ≤ e → e ≤ K →
      MediumPreparedPoweredAt
        thresholdLoss B eps e κ ⟨A, hA⟩ C T₀)
    (hDirect : MediumUnpoweredSecondAt
      thresholdLoss B eps κ ⟨A, hA⟩ C T₀)
    (hell : 1 ≤ ell) (hellK : ell ≤ K)
    (hM : 1 ≤ M) (hN₂ : 1 ≤ N₂)
    (hT₀ : T₀ ≤ T) (hTone : 1 < T)
    (hModeledM : (M : ℝ) = T ^ eta₁)
    (hModeledN₂ : (N₂ : ℝ) = T ^ eta₂)
    (heta₁ : 0 ≤ eta₁) (heta₂ : 0 ≤ eta₂)
    (hproduct : T ^ (1 - xi) ≤ (M : ℝ) * (N₂ : ℝ))
    (hPlower : T ^ (9 / 11 - 10 * eps) ≤ ((M ^ ell : ℕ) : ℝ))
    (hPupper : (((2 * M) ^ ell : ℕ) : ℝ) ≤ T ^ (1 - eps / 10))
    (hN₂lower : T ^ (9 / 11 - 10 * eps) ≤ (N₂ : ℝ))
    (hN₂upper : (N₂ : ℝ) ≤ T ^ (1 - eps / 10))
    (hshift : 0 ≤ shift)
    (habsorb : (ell : ℝ) ≤ (((M : ℝ) ^ ell) ^ shift))
    (htau₁ : 0 ≤ tau₁) (htau₂ : 0 ≤ tau₂)
    (htauShiftLower : 10 * eps ≤ tau₁ + shift)
    (htauMinUpper : min (tau₁ + shift) tau₂ ≤
      17 / 70 - thresholdLoss * eps)
    (htau₂Lower : 10 * eps ≤ tau₂)
    (hgap : 2 * xi * min tau₁ tau₂ + delta ≤ κ - 2 * shift)
    (hC : 0 < C)
    (ha₁ : IsDivisorBoundedByConstant B A a₁)
    (ha₂ : IsDivisorBoundedByConstant B A a₂)
    (hspaced : IsOneSpaced (↑R : Set ℝ))
    (hR : ∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T)
    (hlarge₁ : ∀ t ∈ R,
      (M : ℝ) ^ (-tau₁) <
        ‖dyadicDirichletPolynomial a₁ (M : ℝ) (onePlusIT t)‖)
    (hlarge₂ : ∀ t ∈ R,
      (N₂ : ℝ) ^ (-tau₂) <
        ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ) (onePlusIT t)‖) :
    (R.card : ℝ) * (M : ℝ) ^ (-2 * tau₁) *
        (N₂ : ℝ) ^ (-2 * tau₂) ≤
      ((ell : ℝ) * C) * T ^ (-delta) := by
  have hcard := mediumBin_cardinality_from_uniformPowered_and_direct
    hA hPowered hDirect hell hellK hM hN₂ hT₀ hTone.le hPlower
    hPupper hN₂lower hN₂upper hshift habsorb htau₁ htauShiftLower
    htauMinUpper htau₂Lower ha₁ ha₂ hC.le hspaced hR hlarge₁ hlarge₂
  exact weightedMediumCardinality_le_negativePower hTone hModeledM
    hModeledN₂ heta₁ heta₂ hproduct htau₁ htau₂ hgap
    (mul_nonneg (Nat.cast_nonneg ell) hC.le) (by
      simpa only [mul_assoc] using hcard)

/-- The direct branch and every bounded powered branch can be placed under
one threshold margin, one saving, one constant, and one starting height.
The choices preserve the analytic quantifier order: the common saving is
chosen before `A`, while `C,T₀` are chosen after `A`. -/
theorem exists_commonMediumBranchParameters_of_guthMaynard
    (inputs : ExactSemiprimes.ExternalInputs) :
    ∃ thresholdLoss : ℝ, 0 < thresholdLoss ∧
      ∀ K : ℕ, 1 ≤ K →
        ∀ B : ℝ, 0 ≤ B →
          ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 1000 →
            ∃ κ : ℝ, 0 < κ ∧
              ∀ A : ℝ, ∀ hA : 1 ≤ A,
                ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
                  (∀ ell : ℕ, 1 ≤ ell → ell ≤ K →
                    MediumPreparedPoweredAt
                      thresholdLoss B eps ell κ ⟨A, hA⟩ C T₀) ∧
                  MediumUnpoweredSecondAt
                    thresholdLoss B eps κ ⟨A, hA⟩ C T₀ := by
  obtain ⟨thresholdPowered, hthresholdPowered, hPoweredAll⟩ :=
    mediumPreparedPoweredFirstBranch_uniform_boundedOrders
      (mediumPreparedPoweredFirstBranch_of_guthMaynard inputs)
  obtain ⟨thresholdDirect, hthresholdDirect, hDirectAll⟩ :=
    mediumUnpoweredSecondBranch_of_guthMaynard inputs
  let thresholdLoss := max thresholdPowered thresholdDirect
  refine ⟨thresholdLoss,
    hthresholdPowered.trans_le (le_max_left _ _), ?_⟩
  intro K hK B hB eps heps hepsSmall
  obtain ⟨κPowered, hκPowered, hPoweredAll⟩ :=
    hPoweredAll K hK B hB eps heps hepsSmall
  obtain ⟨κDirect, hκDirect, hDirectAll⟩ :=
    hDirectAll B hB eps heps hepsSmall
  let κ := min κPowered κDirect
  have hκ : 0 < κ := lt_min hκPowered hκDirect
  refine ⟨κ, hκ, ?_⟩
  intro A hA
  obtain ⟨CPowered, TPowered, hCPowered, hTPowered, hPowered⟩ :=
    hPoweredAll A hA
  obtain ⟨CDirect, TDirect, hCDirect, hTDirect, hDirect⟩ :=
    hDirectAll A hA
  let C := max CPowered CDirect
  let T₀ := max TPowered TDirect
  have hC : 0 < C := hCPowered.trans_le (le_max_left _ _)
  have hT₀ : 1 ≤ T₀ := hTPowered.trans (le_max_left _ _)
  refine ⟨C, T₀, hC, hT₀, ?_, ?_⟩
  · intro ell hell hellK
    have hOld := hPowered ell hell hellK
    intro T M P tau₁ tau₂ a₁ R hT hM hP hPlower hPupper
      htauLower htauUpper horder ha₁ hspaced hR hlarge
    have hTold : TPowered ≤ T :=
      (le_max_left TPowered TDirect).trans hT
    have htauUpperOld :
        tau₁ ≤ 17 / 70 - thresholdPowered * eps := by
      have hthresholdOrder : thresholdPowered ≤ thresholdLoss :=
        le_max_left _ _
      have hscaled : thresholdPowered * eps ≤ thresholdLoss * eps :=
        mul_le_mul_of_nonneg_right hthresholdOrder heps.le
      linarith
    have hbound := hOld T M P tau₁ tau₂ a₁ R hTold hM hP
      hPlower hPupper htauLower htauUpperOld horder ha₁ hspaced hR hlarge
    have hTone : 1 ≤ T := hTPowered.trans hTold
    have hκle : κ ≤ κPowered := min_le_left _ _
    have hexponent :
        2 * min tau₁ tau₂ - κPowered ≤ 2 * min tau₁ tau₂ - κ := by
      linarith
    have hpower := Real.rpow_le_rpow_of_exponent_le hTone hexponent
    calc
      (R.card : ℝ) ≤
          CPowered * T ^ (2 * min tau₁ tau₂ - κPowered) := hbound
      _ ≤ CPowered * T ^ (2 * min tau₁ tau₂ - κ) :=
        mul_le_mul_of_nonneg_left hpower hCPowered.le
      _ ≤ C * T ^ (2 * min tau₁ tau₂ - κ) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (by linarith) _)
  · intro T N₂ tau₁ tau₂ a₂ R hT hN₂ hN₂lower hN₂upper
      htau₂Lower htau₂Upper horder ha₂ hspaced hR hlarge
    have hTold : TDirect ≤ T :=
      (le_max_right TPowered TDirect).trans hT
    have htau₂UpperOld :
        tau₂ ≤ 17 / 70 - thresholdDirect * eps := by
      have hthresholdOrder : thresholdDirect ≤ thresholdLoss :=
        le_max_right _ _
      have hscaled : thresholdDirect * eps ≤ thresholdLoss * eps :=
        mul_le_mul_of_nonneg_right hthresholdOrder heps.le
      linarith
    have hbound := hDirect T N₂ tau₁ tau₂ a₂ R hTold hN₂
      hN₂lower hN₂upper htau₂Lower htau₂UpperOld horder ha₂ hspaced hR
      hlarge
    have hTone : 1 ≤ T := hTDirect.trans hTold
    have hκle : κ ≤ κDirect := min_le_right _ _
    have hexponent :
        2 * min tau₁ tau₂ - κDirect ≤ 2 * min tau₁ tau₂ - κ := by
      linarith
    have hpower := Real.rpow_le_rpow_of_exponent_le hTone hexponent
    calc
      (R.card : ℝ) ≤
          CDirect * T ^ (2 * min tau₁ tau₂ - κDirect) := hbound
      _ ≤ CDirect * T ^ (2 * min tau₁ tau₂ - κ) :=
        mul_le_mul_of_nonneg_left hpower hCDirect.le
      _ ≤ C * T ^ (2 * min tau₁ tau₂ - κ) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg (by linarith) _)

/-- Fully quantified discrete medium-bin estimate, including both order
branches.  The hypotheses after `C,T₀` are exactly the geometric length,
bin-threshold, and reserve conditions still to be supplied by the outer
Type-II argument. -/
def MediumWeightedBinStatement : Prop :=
  ∃ thresholdLoss : ℝ, 0 < thresholdLoss ∧
    ∀ K : ℕ, 1 ≤ K →
      ∀ B : ℝ, 0 ≤ B →
        ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 1000 →
          ∃ κ : ℝ, 0 < κ ∧
            ∀ A : ℝ, ∀ _hA : 1 ≤ A,
              ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
                ∀ (ell M N₂ : ℕ)
                    (eta₁ eta₂ xi delta shift tau₁ tau₂ T : ℝ)
                    (a₁ a₂ : ℕ → ℂ) (R : Finset ℝ),
                  1 ≤ ell → ell ≤ K → 1 ≤ M → 1 ≤ N₂ →
                  T₀ ≤ T → 1 < T →
                  (M : ℝ) = T ^ eta₁ →
                  (N₂ : ℝ) = T ^ eta₂ →
                  0 ≤ eta₁ → 0 ≤ eta₂ →
                  T ^ (1 - xi) ≤ (M : ℝ) * (N₂ : ℝ) →
                  T ^ (9 / 11 - 10 * eps) ≤ ((M ^ ell : ℕ) : ℝ) →
                  (((2 * M) ^ ell : ℕ) : ℝ) ≤ T ^ (1 - eps / 10) →
                  T ^ (9 / 11 - 10 * eps) ≤ (N₂ : ℝ) →
                  (N₂ : ℝ) ≤ T ^ (1 - eps / 10) →
                  0 ≤ shift →
                  (ell : ℝ) ≤ (((M : ℝ) ^ ell) ^ shift) →
                  0 ≤ tau₁ → 0 ≤ tau₂ →
                  10 * eps ≤ tau₁ + shift →
                  min (tau₁ + shift) tau₂ ≤
                    17 / 70 - thresholdLoss * eps →
                  10 * eps ≤ tau₂ →
                  2 * xi * min tau₁ tau₂ + delta ≤ κ - 2 * shift →
                  IsDivisorBoundedByConstant B A a₁ →
                  IsDivisorBoundedByConstant B A a₂ →
                  IsOneSpaced (↑R : Set ℝ) →
                  (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
                  (∀ t ∈ R,
                    (M : ℝ) ^ (-tau₁) <
                      ‖dyadicDirichletPolynomial a₁ (M : ℝ)
                        (onePlusIT t)‖) →
                  (∀ t ∈ R,
                    (N₂ : ℝ) ^ (-tau₂) <
                      ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ)
                        (onePlusIT t)‖) →
                  (R.card : ℝ) * (M : ℝ) ^ (-2 * tau₁) *
                      (N₂ : ℝ) ^ (-2 * tau₂) ≤
                    ((ell : ℝ) * C) * T ^ (-delta)

/-- The established Guth--Maynard inputs imply the complete discrete
medium-bin statement after the deterministic common-parameter merge. -/
theorem mediumWeightedBin_of_guthMaynard
    (inputs : ExactSemiprimes.ExternalInputs) :
    MediumWeightedBinStatement := by
  obtain ⟨thresholdLoss, hthresholdLoss, hCommon⟩ :=
    exists_commonMediumBranchParameters_of_guthMaynard inputs
  refine ⟨thresholdLoss, hthresholdLoss, ?_⟩
  intro K hK B hB eps heps hepsSmall
  obtain ⟨κ, hκ, hCommon⟩ := hCommon K hK B hB eps heps hepsSmall
  refine ⟨κ, hκ, ?_⟩
  intro A hA
  obtain ⟨C, T₀, hC, hT₀, hPowered, hDirect⟩ := hCommon A hA
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro ell M N₂ eta₁ eta₂ xi delta shift tau₁ tau₂ T a₁ a₂ R
    hell hellK hM hN₂ hT₀T hTone hModeledM hModeledN₂ heta₁ heta₂
    hproduct hPlower hPupper hN₂lower hN₂upper hshift habsorb htau₁
    htau₂ htauShiftLower htauShiftUpper htau₂Lower hgap ha₁ ha₂
    hspaced hR hlarge₁ hlarge₂
  exact mediumBin_weighted_from_uniformPowered_and_direct
    hA hPowered hDirect hell hellK hM hN₂ hT₀T hTone hModeledM
    hModeledN₂ heta₁ heta₂ hproduct hPlower hPupper hN₂lower hN₂upper
    hshift habsorb htau₁ htau₂ htauShiftLower htauShiftUpper htau₂Lower
    hgap hC ha₁ ha₂ hspaced hR hlarge₁ hlarge₂

/-- Metadata for the complete discrete medium-bin layer. -/
def mediumFullAssemblyModule : ProofModule :=
  { name := "TypeII.MediumFullAssembly"
    paperLocation :=
      "Proof of Proposition 5.1, complete discrete R₂-bin estimate"
    purpose :=
      "Merge the direct and bounded powered hybrid parameters, split without an order-transition gap, aggregate height-dependent powered slices, and prove the negative-power weighted bound for a complete medium bin."
    dependsOn :=
      ["TypeII.MediumFiniteUniformization", "TypeII.MediumThresholdBridge",
        "TypeII.MediumRangeCardinality"]
    status := .proved }

end

end TypeII
end ExactSemiprimes
