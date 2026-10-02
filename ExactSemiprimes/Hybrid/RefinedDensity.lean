import ExactSemiprimes.Hybrid.HybridDensity

/-!
# Length-dependent Guth--Maynard thresholds

`Hybrid.HybridDensity` proves the density estimate `|R| ≪ T^(2σ-κ)` for
polynomials of every length `N ∈ [T^(9/11), T^(1-ε/10)]` with the single
threshold `σ ≤ 17/70 - O(ε)`, which is what the shortest length `T^(9/11)`
allows.  Longer polynomials allow larger `σ`:

* for `N ≥ T^(η₀)` with `9/11 ≤ η₀ ≤ 5/6`, the third term `T N^(12/5) V^(-4)`
  of [GM, Theorem 1.1] is acceptable as long as
  `σ (4η₀ - 2) < 8η₀/5 - 1`, i.e. `σ < 2/5 - 1/(10(2η₀ - 1))`;
* for `N ≥ T^(5/6)`, the long-polynomial bound [GM, Proposition 12.1] gives
  every `σ < 1/4`.

This file proves the resulting density estimate, with threshold loss `20ε`
and saving `T^(-ε²/2)`, from the same two cited Guth--Maynard inputs.
-/

namespace ExactSemiprimes
namespace Hybrid

noncomputable section

namespace Refined

/-! ## Exponent margins below `T^(5/6)` -/

private theorem eps_sq_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 1000) :
    ε ^ 2 ≤ ε / 1000 := by
  have hprod : 0 ≤ ε * (1 / 1000 - ε) := mul_nonneg hε0 (sub_nonneg.mpr hε)
  nlinarith [hprod]

theorem lower_second_margin {ε η σ ρ : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 1000)
    (hηlo : 9 / 11 - 10 * ε ≤ η) (hηhi : η ≤ 5 / 6)
    (hσ : σ ≤ 1 / 4 - 20 * ε) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ε ^ 2) :
    LowerRange.secondExponent η σ ρ ≤ LowerRange.targetExponent σ - ε / 2 := by
  unfold LowerRange.secondExponent LowerRange.targetExponent
  have h1 : 0 ≤ (4 * η - 2) * ((1 / 4 - 20 * ε) - σ) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ ε * (η - (9 / 11 - 10 * ε)) := mul_nonneg hε0.le (by linarith)
  have h3 : 0 ≤ ρ * (1 - η) := mul_nonneg hρ0 (by linarith)
  have h4 := eps_sq_le hε0.le hε
  nlinarith

theorem lower_third_margin {ε η η₀ σ ρ : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 1000)
    (hηlo : η₀ - 10 * ε ≤ η) (hηhi : η ≤ 5 / 6)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / 4 - 20 * ε)
    (hpoly : σ * (4 * η₀ - 2) + 20 * ε ≤ 8 * η₀ / 5 - 1)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ε ^ 2) :
    LowerRange.thirdExponent η σ ρ ≤ LowerRange.targetExponent σ - ε / 2 := by
  unfold LowerRange.thirdExponent LowerRange.targetExponent
  have h1 : 0 ≤ (η - η₀ + 10 * ε) * (8 / 5 - 4 * σ) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ ε * σ := mul_nonneg hε0.le hσ0
  have h3 : 0 ≤ ρ * (1 - η) := mul_nonneg hρ0 (by linarith)
  have h4 := eps_sq_le hε0.le hε
  nlinarith

/-! ## Exponent margins above `T^(5/6)` -/

theorem upper_second_margin {ε η σ ρ : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 1000)
    (hηlo : 5 / 6 ≤ η) (hηhi : η ≤ 1)
    (hσ : σ ≤ 1 / 4 - 20 * ε) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ε ^ 2) :
    UpperRange.secondExponent η σ ρ ≤ UpperRange.targetExponent σ - ε := by
  unfold UpperRange.secondExponent UpperRange.targetExponent
  have h1 : 0 ≤ ((1 / 2 - 2 * σ) - 40 * ε) * (2 * η - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ ε * (η - 5 / 6) := mul_nonneg hε0.le (by linarith)
  have h3 : 0 ≤ ρ * (1 - η) := mul_nonneg hρ0 (by linarith)
  have h4 := eps_sq_le hε0.le hε
  nlinarith

theorem upper_third_margin {ε η σ ρ : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 1000)
    (hηlo : 5 / 6 ≤ η) (hηhi : η ≤ 1)
    (hσ : σ ≤ 1 / 4 - 20 * ε) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ε ^ 2) :
    UpperRange.thirdExponent η σ ρ ≤ UpperRange.targetExponent σ - ε := by
  unfold UpperRange.thirdExponent UpperRange.targetExponent
  have h1 : 0 ≤ ((1 / 4 - 20 * ε) - σ) * (12 * η - 8) :=
    mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ ε * (η - 5 / 6) := mul_nonneg hε0.le (by linarith)
  have h3 : 0 ≤ ρ * (1 - η) := mul_nonneg hρ0 (by linarith)
  have h4 := eps_sq_le hε0.le hε
  nlinarith

end Refined

/-! ## The two branches at fixed constants -/

theorem refinedLower_density_bound_at
    {ε T A B D σ η₀ C : ℝ} {N : ℕ} {a : ℕ → ℂ} {R : Finset ℝ}
    (hGM : GuthMaynardMainBoundAt (ε ^ 2 / 4) C)
    (hC : 0 < C)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 1000)
    (hT : 1 < T) (hN : 1 ≤ N)
    (hNlower : T ^ (η₀ - 10 * ε) ≤ (N : ℝ))
    (hNupper : (N : ℝ) ≤ T ^ (5 / 6 : ℝ))
    (hσlo : 10 * ε ≤ σ) (hσhi : σ ≤ 1 / 4 - 20 * ε)
    (hpoly : σ * (4 * η₀ - 2) + 20 * ε ≤ 8 * η₀ / 5 - 1)
    (hA : 0 < A) (hD : 0 < D)
    (ha : IsDivisorBoundedByConstant B A a)
    (hdiv : HasDyadicDivisorSubpowerBound B D (ε ^ 2 / 4) N)
    (hR : IsOneSpaced (↑R : Set ℝ))
    (hRT : ∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T)
    (hKle : guthMaynardK A D (ε ^ 2 / 4) ≤ (N : ℝ) ^ (ε ^ 2 / 4))
    (hlarge : ∀ t ∈ R,
      (N : ℝ) ^ (-σ) < ‖dyadicDirichletPolynomial a (N : ℝ) (onePlusIT t)‖)
    (hη₀ : 9 / 11 ≤ η₀) :
    (R.card : ℝ) ≤ (3 * C) * T ^ (2 * σ - ε ^ 2 / 2) := by
  let ρ : ℝ := ε ^ 2 / 4
  let η : ℝ := logarithmicLengthExponent T (N : ℝ)
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hηeq : (N : ℝ) = T ^ η := eq_rpow_logarithmicLengthExponent hT hNpos
  have hηbounds : η₀ - 10 * ε ≤ η ∧ η ≤ 5 / 6 :=
    logarithmicLengthExponent_bounds hT hNpos hNlower hNupper
  have hρle : ρ ≤ ε ^ 2 := by dsimp [ρ]; nlinarith [sq_nonneg ε]
  have hm1 := LowerRange.first_explicit_margin hε0 hε
    (by simpa [LowerRange.etaJoin] using hηbounds.2) hσlo hρ0 hρle
  have hm2 := Refined.lower_second_margin hε0 hε (by linarith [hηbounds.1])
    hηbounds.2 hσhi hρ0 hρle
  have hm3 := Refined.lower_third_margin hε0 hε hηbounds.1 hηbounds.2
    (by linarith) hσhi hpoly hρ0 hρle
  have hcommonHalf : 3 * ε ^ 2 / 4 ≤ ε / 2 := by nlinarith
  have h₁ : LowerRange.firstExponent η σ ρ ≤
      LowerRange.targetExponent σ - ρ - ε ^ 2 / 2 := by dsimp [ρ]; nlinarith
  have h₂ : LowerRange.secondExponent η σ ρ ≤
      LowerRange.targetExponent σ - ρ - ε ^ 2 / 2 := by dsimp [ρ]; nlinarith
  have h₃ : LowerRange.thirdExponent η σ ρ ≤
      LowerRange.targetExponent σ - ρ - ε ^ 2 / 2 := by dsimp [ρ]; nlinarith
  have hraw := normalized_guthMaynardMain_bound_at hGM
    (le_of_lt hT) hN hA hD ha hdiv hR hRT hKle hlarge
  rw [main_terms_eq_lowerRange_powers hT hNpos hηeq] at hraw
  exact hraw.trans (by
    have habsorb := absorb_three_power_terms (le_of_lt hC) (le_of_lt hT) h₁ h₂ h₃
    simpa [ρ, LowerRange.targetExponent] using habsorb)

theorem refinedUpper_density_bound_at
    {ε T A B D σ C : ℝ} {N : ℕ} {a : ℕ → ℂ} {R : Finset ℝ}
    (hGM : GuthMaynardLongBoundAt (ε ^ 2 / 4) C)
    (hC : 0 < C)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 1000)
    (hT : 1 < T) (hN : 1 ≤ N)
    (hNlower : T ^ (5 / 6 : ℝ) ≤ (N : ℝ))
    (hNupper : (N : ℝ) ≤ T ^ (1 - ε / 10))
    (hσlo : 10 * ε ≤ σ) (hσhi : σ ≤ 1 / 4 - 20 * ε)
    (hA : 0 < A) (hD : 0 < D)
    (ha : IsDivisorBoundedByConstant B A a)
    (hdiv : HasDyadicDivisorSubpowerBound B D (ε ^ 2 / 4) N)
    (hR : IsOneSpaced (↑R : Set ℝ))
    (hRT : ∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T)
    (hKle : guthMaynardK A D (ε ^ 2 / 4) ≤ (N : ℝ) ^ (ε ^ 2 / 4))
    (hlarge : ∀ t ∈ R,
      (N : ℝ) ^ (-σ) < ‖dyadicDirichletPolynomial a (N : ℝ) (onePlusIT t)‖) :
    (R.card : ℝ) ≤ (3 * C) * T ^ (2 * σ - ε ^ 2 / 2) := by
  let ρ : ℝ := ε ^ 2 / 4
  let η : ℝ := logarithmicLengthExponent T (N : ℝ)
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hηeq : (N : ℝ) = T ^ η := eq_rpow_logarithmicLengthExponent hT hNpos
  have hηbounds : 5 / 6 ≤ η ∧ η ≤ 1 - ε / 10 :=
    logarithmicLengthExponent_bounds hT hNpos hNlower hNupper
  have hρle : ρ ≤ ε ^ 2 := by dsimp [ρ]; nlinarith [sq_nonneg ε]
  have hρle4 : ρ ≤ ε ^ 2 / 4 := by dsimp [ρ]; exact le_rfl
  have hamplitude : 7 / 10 ≤ 1 - σ - 2 * ρ := by
    have : ε ^ 2 ≤ 1 / 1000000 := by nlinarith
    dsimp [ρ]; nlinarith
  have hm1 := UpperRange.first_explicit_margin hε0 hηbounds.2 hσlo hρ0 hρle4
  have hm2 := Refined.upper_second_margin hε0 hε hηbounds.1 (by linarith [hηbounds.2])
    hσhi hρ0 hρle
  have hm3 := Refined.upper_third_margin hε0 hε hηbounds.1 (by linarith [hηbounds.2])
    hσhi hρ0 hρle
  have hcommon : 3 * ε ^ 2 / 4 ≤ ε := by nlinarith
  have h₁ : UpperRange.firstExponent η σ ρ ≤
      UpperRange.targetExponent σ - ρ - ε ^ 2 / 2 := by dsimp [ρ]; nlinarith
  have h₂ : UpperRange.secondExponent η σ ρ ≤
      UpperRange.targetExponent σ - ρ - ε ^ 2 / 2 := by dsimp [ρ]; nlinarith
  have h₃ : UpperRange.thirdExponent η σ ρ ≤
      UpperRange.targetExponent σ - ρ - ε ^ 2 / 2 := by dsimp [ρ]; nlinarith
  have hNleT : (N : ℝ) ≤ T := by
    have hexponent : T ^ (1 - ε / 10) ≤ T ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hT) (by linarith)
    simpa using hNupper.trans hexponent
  have hraw := normalized_guthMaynardLong_bound_at hGM
    (le_of_lt hT) hN hNlower hNleT hamplitude hA hD ha hdiv hR hRT hKle hlarge
  have hterms := long_terms_le_upperRange_powers (σ := σ) (le_of_lt hT) hNpos hηeq hρ0
  have hconverted := hraw.trans
    (mul_le_mul_of_nonneg_left hterms (by positivity : 0 ≤ C * T ^ ρ))
  exact hconverted.trans (by
    have habsorb := absorb_three_power_terms (le_of_lt hC) (le_of_lt hT) h₁ h₂ h₃
    simpa [ρ, UpperRange.targetExponent] using habsorb)

/-! ## The refined density statement -/

/-- **Refined hybrid density estimate.**  For polynomials of length at
least `T^(η₀ - 10ε)` (with `9/11 ≤ η₀ ≤ 5/6`) and `σ` below both `1/4` and
the length-`T^(η₀)` Guth--Maynard threshold, the large-value set has at most
`C T^(2σ - ε²/2)` one-spaced points.  At `η₀ = 9/11` the polynomial
condition is `σ ≤ 17/70 - 20ε/(14/11)`; at `η₀ = 5/6` it is implied by
`σ ≤ 1/4 - 20ε`. -/
def RefinedHybridDiscreteDensityStatement : Prop :=
  ∀ B : ℝ, 0 ≤ B →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 1000 →
      ∀ A : ℝ, 1 ≤ A →
        ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
          ∀ (T : ℝ) (N : ℕ) (σ η₀ : ℝ) (a : ℕ → ℂ) (R : Finset ℝ),
            T₀ ≤ T → 1 ≤ N → 9 / 11 ≤ η₀ → η₀ ≤ 5 / 6 →
            T ^ (η₀ - 10 * ε) ≤ (N : ℝ) →
            (N : ℝ) ≤ T ^ (1 - ε / 10) →
            10 * ε ≤ σ → σ ≤ 1 / 4 - 20 * ε →
            σ * (4 * η₀ - 2) + 20 * ε ≤ 8 * η₀ / 5 - 1 →
            IsDivisorBoundedByConstant B A a →
            IsOneSpaced (↑R : Set ℝ) →
            (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
            (∀ t ∈ R,
              (N : ℝ) ^ (-σ) < ‖dyadicDirichletPolynomial a (N : ℝ) (onePlusIT t)‖) →
            (R.card : ℝ) ≤ C * T ^ (2 * σ - ε ^ 2 / 2)

/-- Measure form of the refined density estimate. -/
def RefinedHybridMeasureDensityStatement : Prop :=
  ∀ B : ℝ, 0 ≤ B →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 1000 →
      ∀ A : ℝ, 1 ≤ A →
        ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
          ∀ (T : ℝ) (N : ℕ) (σ η₀ : ℝ) (a : ℕ → ℂ),
            T₀ ≤ T → 1 ≤ N → 9 / 11 ≤ η₀ → η₀ ≤ 5 / 6 →
            T ^ (η₀ - 10 * ε) ≤ (N : ℝ) →
            (N : ℝ) ≤ T ^ (1 - ε / 10) →
            10 * ε ≤ σ → σ ≤ 1 / 4 - 20 * ε →
            σ * (4 * η₀ - 2) + 20 * ε ≤ 8 * η₀ / 5 - 1 →
            IsDivisorBoundedByConstant B A a →
            MeasureTheory.volume
                (largeValueSet (dyadicDirichletPolynomial a (N : ℝ)) T ((N : ℝ) ^ (-σ))) ≤
              ENNReal.ofReal (C * T ^ (2 * σ - ε ^ 2 / 2))

theorem refinedHybridDiscreteDensity_of_guthMaynard
    (hMain : GuthMaynardMainLargeValuesStatement)
    (hLong : GuthMaynardLongPolynomialStatement) :
    RefinedHybridDiscreteDensityStatement := by
  intro B hB ε hε0 hε A hA
  let ρ : ℝ := ε ^ 2 / 4
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  obtain ⟨D, hD, hdiv⟩ :=
    exists_uniform_hasDyadicDivisorSubpowerBound globalDivisorSubpower hB hρpos
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  obtain ⟨Cmain, hCmain, hMainρ⟩ := hMain ρ hρpos
  obtain ⟨Clong, hClong, hLongρ⟩ := hLong ρ hρpos
  have hMainAt : GuthMaynardMainBoundAt ρ Cmain := hMainρ
  have hLongAt : GuthMaynardLongBoundAt ρ Clong := hLongρ
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    (eventually_guthMaynardK_le_natCast_rpow A D ρ hρpos)
  let α : ℝ := 9 / 11 - 10 * ε
  have hα : 0 < α := by dsimp [α]; linarith
  have hTeventual : ∀ᶠ T : ℝ in Filter.atTop, (N₀ : ℝ) ≤ T ^ α :=
    (tendsto_rpow_atTop hα).eventually_ge_atTop (N₀ : ℝ)
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.1 hTeventual
  refine ⟨3 * (Cmain + Clong), max 2 T₁, by positivity,
    le_trans (by norm_num) (le_max_left 2 T₁), ?_⟩
  intro T N σ η₀ a R hT hN hη₀ hη₀' hNlower hNupper hσlo hσhi hpoly ha hR hRT hlarge
  have hTone : 1 < T := by
    have htwo : (2 : ℝ) ≤ T := (le_max_left 2 T₁).trans hT
    linarith
  have hT₁T : T₁ ≤ T := (le_max_right 2 T₁).trans hT
  have hαle : T ^ α ≤ T ^ (η₀ - 10 * ε) :=
    Real.rpow_le_rpow_of_exponent_le hTone.le (by dsimp [α]; linarith)
  have hN₀cast : (N₀ : ℝ) ≤ (N : ℝ) := (hT₁ T hT₁T).trans (hαle.trans hNlower)
  have hN₀nat : N₀ ≤ N := by exact_mod_cast hN₀cast
  have hKle : guthMaynardK A D ρ ≤ (N : ℝ) ^ ρ := hN₀ N hN₀nat
  have hTpos : 0 ≤ T := by linarith
  by_cases hlower : (N : ℝ) ≤ T ^ (5 / 6 : ℝ)
  · have hbound := refinedLower_density_bound_at
      (by simpa [ρ] using hMainAt) hCmain hε0 hε hTone hN hNlower hlower hσlo hσhi
      hpoly hApos hDpos ha (by simpa [ρ] using hdiv N) hR hRT
      (by simpa [ρ] using hKle) hlarge hη₀
    have hconst : 3 * Cmain ≤ 3 * (Cmain + Clong) := by linarith
    exact hbound.trans (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hTpos _))
  · have hbranch : T ^ (5 / 6 : ℝ) ≤ (N : ℝ) := le_of_not_ge hlower
    have hbound := refinedUpper_density_bound_at
      (by simpa [ρ] using hLongAt) hClong hε0 hε hTone hN hbranch hNupper hσlo hσhi
      hApos hDpos ha (by simpa [ρ] using hdiv N) hR hRT (by simpa [ρ] using hKle) hlarge
    have hconst : 3 * Clong ≤ 3 * (Cmain + Clong) := by linarith
    exact hbound.trans (mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hTpos _))

theorem refinedHybridMeasureDensity_of_discrete
    (hDiscrete : RefinedHybridDiscreteDensityStatement) :
    RefinedHybridMeasureDensityStatement := by
  intro B hB ε hε0 hε A hA
  obtain ⟨C, T₀, hC, hT₀, hDiscrete⟩ := hDiscrete B hB ε hε0 hε A hA
  refine ⟨2 * C, T₀, mul_pos (by norm_num) hC, hT₀, ?_⟩
  intro T N σ η₀ a hT hN hη₀ hη₀' hNlower hNupper hσlo hσhi hpoly ha
  have hvolume := volume_largeValueSet_le_of_uniform_card_bound
    (A := dyadicDirichletPolynomial a (N : ℝ)) (T := T) (V := (N : ℝ) ^ (-σ))
    (C := C * T ^ (2 * σ - ε ^ 2 / 2)) (fun R hR hRT hlarge ↦
      hDiscrete T N σ η₀ a R hT hN hη₀ hη₀' hNlower hNupper hσlo hσhi hpoly ha
        hR hRT hlarge)
  simpa [mul_assoc] using hvolume

theorem refinedHybridMeasureDensity_of_inputs (inputs : ExternalInputs) :
    RefinedHybridMeasureDensityStatement :=
  refinedHybridMeasureDensity_of_discrete
    (refinedHybridDiscreteDensity_of_guthMaynard inputs.guthMaynardMainLargeValues
      inputs.guthMaynardLongPolynomial)

def refinedDensityModule : ProofModule :=
  { name := "Hybrid.RefinedDensity"
    paperLocation := "Lemma 4.3 (length-dependent form)"
    purpose :=
      "Density estimate with the length-dependent Guth--Maynard threshold min(1/4, 2/5 - 1/(10(2η₀-1)))."
    dependsOn := ["Hybrid.HybridDensity"]
    status := .proved }

end

end Hybrid
end ExactSemiprimes
