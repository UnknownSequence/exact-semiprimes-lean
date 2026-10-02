import ExactSemiprimes.Hybrid.RefinedDensity
import ExactSemiprimes.TypeII.MediumThresholdBridge
import ExactSemiprimes.TypeII.MediumLogBinBridge
import ExactSemiprimes.TypeII.TypeIIEstimate
import ExactSemiprimes.Sparse.PropagationMoving

/-!
# Medium bins below the length-dependent thresholds

Section 6 of the paper treats a medium `R₂` bin with exponents `(σ₁,σ₂)`
by Heath-Brown's sparse mean value theorem.  With a single threshold
`17/70` for both factors, the sparse branches need `a > 35/32`.

The refinement uses the length-dependent thresholds of
`Hybrid/RefinedDensity.lean`:

* if the first factor is the smaller one and `σ₁ < 1/4 - O(ε)`, power it
  into `[X^(5/6), X)` (five or six copies) and apply the long-polynomial
  density bound;
* if the second factor (of length `X^(1-θ)`) is the smaller one and
  `σ₂` lies below the Guth--Maynard threshold for that length, apply the
  density bound to it directly;
* otherwise the second sparse branch closes as soon as
  `a > 1925/1763`, by the three elementary inequalities `key_regionA`,
  `key_regionB1`, `key_regionB2` below.

This file contains the density estimates for the first two cases, phrased
for an arbitrary set of points at which the relevant factor is large, the
comparison with the sparse target, and the exponent arithmetic of the third
case.
-/

namespace ExactSemiprimes
namespace Final

open Filter Real MeasureTheory

noncomputable section

/-! ## Measure bookkeeping -/

theorem measureReal_le_of_subset_of_volume_le {V L : Set ℝ} {B : ℝ}
    (hVL : V ⊆ L) (hL : volume L ≤ ENNReal.ofReal B) (hB : 0 ≤ B) :
    volume.real V ≤ B := by
  have h := (measure_mono hVL).trans hL
  calc volume.real V = (volume V).toReal := rfl
    _ ≤ (ENNReal.ofReal B).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = B := ENNReal.toReal_ofReal hB

theorem measureReal_le_of_subset_biUnion {V : Set ℝ} {ℓ : ℕ}
    {L : ℕ → Set ℝ} {B : ℝ}
    (hVL : V ⊆ ⋃ j ∈ Finset.range ℓ, L j)
    (hL : ∀ j ∈ Finset.range ℓ, volume (L j) ≤ ENNReal.ofReal B) (hB : 0 ≤ B) :
    volume.real V ≤ ℓ * B := by
  have h1 : volume V ≤ ∑ j ∈ Finset.range ℓ, volume (L j) :=
    (measure_mono hVL).trans (measure_biUnion_finset_le _ _)
  have h2 : ∑ j ∈ Finset.range ℓ, volume (L j) ≤
      ∑ _j ∈ Finset.range ℓ, ENNReal.ofReal B :=
    Finset.sum_le_sum hL
  have h3 : ∑ _j ∈ Finset.range ℓ, ENNReal.ofReal B =
      ENNReal.ofReal ((ℓ : ℝ) * B) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  refine measureReal_le_of_subset_of_volume_le subset_rfl ?_ (by positivity)
  rw [← h3]
  exact h1.trans h2

/-! ## Points of a medium bin -/

theorem mediumBin_subset_ambient {E : Set ℝ} {F₁ F₂ : ℂ → ℂ}
    {N₁ N₂ X eps : ℝ} {k : ℤ × ℤ} :
    TypeII.mediumLogMagnitudeBinSet E F₁ F₂ N₁ N₂ X eps k ⊆ E :=
  fun _ ht ↦ (TypeII.mem_largeValueR2_iff.mp ht.1).1

theorem mediumBin_first_large {E : Set ℝ} {F₁ F₂ : ℂ → ℂ}
    {N₁ N₂ X eps : ℝ} {k : ℤ × ℤ} {t : ℝ} (hN₁ : 1 < N₁) (hX : 0 < X)
    (ht : t ∈ TypeII.mediumLogMagnitudeBinSet E F₁ F₂ N₁ N₂ X eps k) :
    N₁ ^ (-TypeII.upperBinExponent N₁ k.1) < ‖F₁ (onePlusIT t)‖ :=
  (TypeII.magnitude_bounds_of_mem_logMagnitudeBin_upperExponent hN₁ ht.2.1
    (TypeII.typeIIMagnitudes_pos_of_mem_largeValueR2 hX ht.1).1).1

theorem mediumBin_second_large {E : Set ℝ} {F₁ F₂ : ℂ → ℂ}
    {N₁ N₂ X eps : ℝ} {k : ℤ × ℤ} {t : ℝ} (hN₂ : 1 < N₂) (hX : 0 < X)
    (ht : t ∈ TypeII.mediumLogMagnitudeBinSet E F₁ F₂ N₁ N₂ X eps k) :
    N₂ ^ (-TypeII.upperBinExponent N₂ k.2) < ‖F₂ (onePlusIT t)‖ :=
  (TypeII.magnitude_bounds_of_mem_logMagnitudeBin_upperExponent hN₂ ht.2.2
    (TypeII.typeIIMagnitudes_pos_of_mem_largeValueR2 hX ht.1).2).1

/-! ## Comparison with the sparse target -/

/-- The sparse target `N₁^(2σ₁) N₂^(2σ₂)` is at least `X^(2σ - e²/200)`
when `σ ≤ min(σ₁,σ₂)` and `N₁N₂ ≥ X^(1-e²/100)`. -/
theorem sparseTarget_lower_bound {X n N σ σ₁ σ₂ θ φ e : ℝ} (hX : 1 < X)
    (hn : n = X ^ θ) (hN : N = X ^ φ) (hθ : 0 ≤ θ) (hφ : 0 ≤ φ)
    (hσ : 0 ≤ σ) (hσ14 : σ ≤ 1 / 4) (h1 : σ ≤ σ₁) (h2 : σ ≤ σ₂)
    (hloss : 1 - θ - φ ≤ e ^ 2 / 100) :
    X ^ (2 * σ - e ^ 2 / 200) ≤ Sparse.sparsePropagationScaleTarget n N σ₁ σ₂ := by
  unfold Sparse.sparsePropagationScaleTarget
  have hX0 : 0 < X := by linarith
  rw [hn, hN, ← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le,
    ← Real.rpow_add hX0]
  apply Real.rpow_le_rpow_of_exponent_le hX.le
  have k1 := mul_le_mul_of_nonneg_left h1 hθ
  have k2 := mul_le_mul_of_nonneg_left h2 hφ
  have k3 := mul_le_mul_of_nonneg_left hloss hσ
  have k4 := mul_le_mul_of_nonneg_right hσ14 (by positivity : (0 : ℝ) ≤ e ^ 2 / 100)
  nlinarith

/-- A density bound `C X^(2σ - c)` with `c ≥ (1 + 1/200) e²` is at most
`C · target · X^(-e²)`. -/
theorem density_le_sparseTarget {X C Tg σ e c : ℝ} (hX : 1 < X) (hC : 0 ≤ C)
    (hT : X ^ (2 * σ - e ^ 2 / 200) ≤ Tg) (hc : e ^ 2 + e ^ 2 / 200 ≤ c) :
    C * X ^ (2 * σ - c) ≤ C * Tg * X ^ (-(e ^ 2)) := by
  have hX0 : 0 < X := by linarith
  have h1 : X ^ (2 * σ - c) ≤ X ^ (2 * σ - e ^ 2 / 200) * X ^ (-(e ^ 2)) := by
    rw [← Real.rpow_add hX0]
    exact Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)
  have h2 : X ^ (2 * σ - e ^ 2 / 200) * X ^ (-(e ^ 2)) ≤ Tg * X ^ (-(e ^ 2)) :=
    mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg hX0.le _)
  calc C * X ^ (2 * σ - c) ≤ C * (Tg * X ^ (-(e ^ 2))) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hC
    _ = C * Tg * X ^ (-(e ^ 2)) := by ring

/-! ## The density bound for a powered first factor -/

/-- The refined density bound, applied to the `ℓ` dyadic slices of the
`ℓ`-th power of a short polynomial. -/
theorem poweredSlices_volume_le {B A εh C T₀ δ σ X : ℝ} {n ℓ : ℕ}
    {c : ℕ → ℂ} {V : Set ℝ}
    (hD : ∀ (T : ℝ) (N : ℕ) (σ η₀ : ℝ) (a : ℕ → ℂ),
        T₀ ≤ T → 1 ≤ N → 9 / 11 ≤ η₀ → η₀ ≤ 5 / 6 →
        T ^ (η₀ - 10 * εh) ≤ (N : ℝ) → (N : ℝ) ≤ T ^ (1 - εh / 10) →
        10 * εh ≤ σ → σ ≤ 1 / 4 - 20 * εh →
        σ * (4 * η₀ - 2) + 20 * εh ≤ 8 * η₀ / 5 - 1 →
        IsDivisorBoundedByConstant (B * ℓ + ℓ - 1) (A ^ ℓ) a →
        volume (largeValueSet (dyadicDirichletPolynomial a (N : ℝ)) T
          ((N : ℝ) ^ (-σ))) ≤ ENNReal.ofReal (C * T ^ (2 * σ - εh ^ 2 / 2)))
    (hεh : 0 ≤ εh) (hC : 0 ≤ C) (hX0 : 0 ≤ X) (hXT : T₀ ≤ X) (hn : 1 ≤ n) (hℓ : 1 ≤ ℓ)
    (hc : IsDivisorBoundedByConstant B A c) (hδ : 0 ≤ δ) (hσ0 : 0 ≤ σ)
    (hlo : X ^ (5 / 6 - 10 * εh) ≤ (n : ℝ) ^ ℓ)
    (hhi : (2 * (n : ℝ)) ^ ℓ ≤ X ^ (1 - εh / 10))
    (habsorb : (ℓ : ℝ) ≤ ((n : ℝ) ^ ℓ) ^ δ)
    (hσlo : 10 * εh ≤ σ + δ) (hσhi : σ + δ ≤ 1 / 4 - 20 * εh)
    (hVsub : V ⊆ Set.Icc 0 X)
    (hlarge : ∀ t ∈ V,
      (n : ℝ) ^ (-σ) < ‖dyadicDirichletPolynomial c (n : ℝ) (onePlusIT t)‖) :
    volume.real V ≤ ℓ * (C * X ^ (2 * (σ + δ) - εh ^ 2 / 2)) := by
  set L : ℕ → Set ℝ := fun j ↦ largeValueSet
      (dyadicDirichletPolynomial
        (TypeII.powerConvolutionCoefficient c (dyadicInterval (n : ℝ)) ℓ)
        (TypeII.naturalOpenClosedSliceBase n ℓ j : ℝ)) X
      ((TypeII.naturalOpenClosedSliceBase n ℓ j : ℝ) ^ (-(σ + δ))) with hL
  have hcover : V ⊆ ⋃ j ∈ Finset.range ℓ, L j := by
    intro t ht
    obtain ⟨j, hj, P, hP, _hP1, _hPlo, _hPhi, hPlarge⟩ :=
      TypeII.exists_large_poweredDyadicPolynomial_shiftedThreshold_naturalScale
        c hn hℓ hσ0 hδ habsorb (onePlusIT t) (hlarge t ht)
    simp only [Set.mem_iUnion, Finset.mem_range]
    refine ⟨j, hj, hVsub ht, ?_⟩
    show (TypeII.naturalOpenClosedSliceBase n ℓ j : ℝ) ^ (-(σ + δ)) < _
    rw [← hP]
    exact hPlarge
  refine measureReal_le_of_subset_biUnion hcover ?_
    (mul_nonneg hC (Real.rpow_nonneg hX0 _))
  intro j hj
  have hj' : j < ℓ := Finset.mem_range.mp hj
  obtain ⟨hPlo, hPhi⟩ := TypeII.naturalOpenClosedSliceBase_bounds (M := n) hj'
  have hP1 : 1 ≤ TypeII.naturalOpenClosedSliceBase n ℓ j :=
    le_trans (Nat.one_le_pow _ _ hn) hPlo
  have hPloR : (n : ℝ) ^ ℓ ≤ (TypeII.naturalOpenClosedSliceBase n ℓ j : ℝ) := by
    exact_mod_cast hPlo
  have hPhiR : (TypeII.naturalOpenClosedSliceBase n ℓ j : ℝ) ≤ (2 * (n : ℝ)) ^ ℓ := by
    exact_mod_cast hPhi
  exact hD X (TypeII.naturalOpenClosedSliceBase n ℓ j) (σ + δ) (5 / 6) _ hXT hP1
    (by norm_num) le_rfl (hlo.trans hPloR) (hPhiR.trans hhi) hσlo hσhi
    (by norm_num; linarith)
    (TypeII.powerConvolutionCoefficient_isDivisorBoundedByConstant hℓ hc)

/-- **Case (a).**  If the first factor has length `X^θ` with
`1/7 ≤ θ ≤ 2/11` and is larger than `X^(-θσ)` with `σ ≤ 1/4 - 21εₕ` on
`V`, then `|V| ≪ X^(2σ - εₕ²/4)`: power it five or six times into
`[X^(5/6 - 10εₕ), X^(1-εₕ/10)]` and apply the long-polynomial density bound
to each of the `ℓ` dyadic slices. -/
theorem poweredFirstFactor_density
    (hdens : Hybrid.RefinedHybridMeasureDensityStatement)
    {B A εh : ℝ} (hB : 0 ≤ B) (hA : 1 ≤ A) (hεh : 0 < εh)
    (hεh' : εh ≤ 1 / 1000) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (n : ℕ) (c : ℕ → ℂ) (V : Set ℝ) (σ θ : ℝ),
        IsDivisorBoundedByConstant B A c →
        (n : ℝ) = (X : ℝ) ^ θ → 1 / 7 ≤ θ → θ ≤ 2 / 11 →
        10 * εh ≤ σ → σ ≤ 1 / 4 - 21 * εh →
        V ⊆ Set.Icc 0 (X : ℝ) →
        (∀ t ∈ V, (n : ℝ) ^ (-σ) <
          ‖dyadicDirichletPolynomial c (n : ℝ) (onePlusIT t)‖) →
        volume.real V ≤ C * (X : ℝ) ^ (2 * σ - εh ^ 2 / 4) := by
  have hB5 : 0 ≤ B * ((5 : ℕ) : ℝ) + ((5 : ℕ) : ℝ) - 1 := by push_cast; linarith
  have hB6 : 0 ≤ B * ((6 : ℕ) : ℝ) + ((6 : ℕ) : ℝ) - 1 := by push_cast; linarith
  obtain ⟨C₅, T₅, hC₅, _hT₅, h5⟩ :=
    hdens _ hB5 εh hεh hεh' (A ^ (5 : ℕ)) (one_le_pow₀ hA)
  obtain ⟨C₆, T₆, hC₆, _hT₆, h6⟩ :=
    hdens _ hB6 εh hεh hεh' (A ^ (6 : ℕ)) (one_le_pow₀ hA)
  refine ⟨6 * max C₅ C₆, by positivity, ?_⟩
  have hev1 := tendsto_natCast_atTop_atTop.eventually_ge_atTop (max T₅ T₆)
  have hev2 := tendsto_natCast_atTop_atTop.eventually
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < εh / 10)).eventually_ge_atTop 64)
  have hev3 := tendsto_natCast_atTop_atTop.eventually
    ((tendsto_rpow_atTop (by positivity : (0 : ℝ) < εh ^ 2 / 16)).eventually_ge_atTop 6)
  filter_upwards [hev1, hev2, hev3, eventually_ge_atTop 2] with X hXT hX64 hX6 hX2
  intro n c V σ θ hc hn hθlo hθhi hσlo hσhi hVsub hlarge
  have hX1 : (1 : ℝ) < X := by
    have : (2 : ℝ) ≤ X := by exact_mod_cast hX2
    linarith
  have hX0 : (0 : ℝ) < X := by linarith
  have hθ0 : 0 ≤ θ := by linarith
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by rw [hn]; exact Real.one_le_rpow hX1.le hθ0
  have hn1 : 1 ≤ n := by exact_mod_cast hn1R
  have hpow : ∀ ℓ : ℕ, (n : ℝ) ^ ℓ = (X : ℝ) ^ (θ * ℓ) := by
    intro ℓ
    rw [hn, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
  have hpow2 : ∀ ℓ : ℕ, ℓ ≤ 6 →
      (2 * (n : ℝ)) ^ ℓ ≤ (X : ℝ) ^ (εh / 10 + θ * ℓ) := by
    intro ℓ hℓ
    rw [mul_pow, hpow, Real.rpow_add hX0]
    have h2 : (2 : ℝ) ^ ℓ ≤ 64 :=
      calc (2 : ℝ) ^ ℓ ≤ 2 ^ (6 : ℕ) := pow_le_pow_right₀ (by norm_num) hℓ
        _ = 64 := by norm_num
    exact mul_le_mul_of_nonneg_right (h2.trans hX64) (Real.rpow_nonneg hX0.le _)
  have habs : ∀ ℓ : ℕ, 5 ≤ ℓ → (ℓ : ℝ) ≤ 6 →
      (ℓ : ℝ) ≤ ((n : ℝ) ^ ℓ) ^ (εh ^ 2 / 8) := by
    intro ℓ hℓ hℓ6
    have hℓR : (5 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    rw [hpow, ← Real.rpow_mul hX0.le]
    refine hℓ6.trans (hX6.trans (Real.rpow_le_rpow_of_exponent_le hX1.le ?_))
    have hεsq : 0 ≤ εh ^ 2 := sq_nonneg εh
    have h1 : 5 / 7 ≤ θ * ℓ := by nlinarith
    nlinarith
  have hεsq : εh ^ 2 / 8 ≤ εh := by nlinarith
  have hσ0 : 0 ≤ σ := by linarith
  have hσhi' : σ + εh ^ 2 / 8 ≤ 1 / 4 - 20 * εh := by linarith
  have hσlo' : 10 * εh ≤ σ + εh ^ 2 / 8 := by nlinarith
  have hexp : 2 * (σ + εh ^ 2 / 8) - εh ^ 2 / 2 = 2 * σ - εh ^ 2 / 4 := by ring
  have hXe : 0 ≤ (X : ℝ) ^ (2 * σ - εh ^ 2 / 4) := Real.rpow_nonneg hX0.le _
  by_cases h6θ : 6 * θ ≤ 1 - εh / 5
  · have hres := poweredSlices_volume_le (ℓ := 6) h6 hεh.le hC₆.le hX0.le
      ((le_max_right _ _).trans hXT) hn1 (by norm_num) hc (by positivity) hσ0
      (by
        rw [hpow]
        exact Real.rpow_le_rpow_of_exponent_le hX1.le (by push_cast; linarith))
      ((hpow2 6 le_rfl).trans
        (Real.rpow_le_rpow_of_exponent_le hX1.le (by push_cast; linarith)))
      (habs 6 (by norm_num) (by norm_num)) hσlo' hσhi' hVsub hlarge
    rw [hexp] at hres
    refine hres.trans ?_
    push_cast
    have : C₆ ≤ max C₅ C₆ := le_max_right _ _
    nlinarith
  · replace h6θ := lt_of_not_ge h6θ
    have hres := poweredSlices_volume_le (ℓ := 5) h5 hεh.le hC₅.le hX0.le
      ((le_max_left _ _).trans hXT) hn1 (by norm_num) hc (by positivity) hσ0
      (by
        rw [hpow]
        exact Real.rpow_le_rpow_of_exponent_le hX1.le (by push_cast; linarith))
      ((hpow2 5 (by norm_num)).trans
        (Real.rpow_le_rpow_of_exponent_le hX1.le (by push_cast; linarith)))
      (habs 5 le_rfl (by norm_num)) hσlo' hσhi' hVsub hlarge
    rw [hexp] at hres
    refine hres.trans ?_
    push_cast
    have : C₅ ≤ max C₅ C₆ := le_max_left _ _
    nlinarith

/-- **Case (b).**  The refined density bound for a single polynomial of
length `X^φ`, `φ ≥ η₀ - 10εₕ`, which is larger than `X^(-φσ)` on `V`. -/
theorem directFactor_density
    (hdens : Hybrid.RefinedHybridMeasureDensityStatement)
    {B A εh : ℝ} (hB : 0 ≤ B) (hA : 1 ≤ A) (hεh : 0 < εh)
    (hεh' : εh ≤ 1 / 1000) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (N : ℕ) (c : ℕ → ℂ) (V : Set ℝ) (σ φ η₀ : ℝ),
        IsDivisorBoundedByConstant B A c → 1 ≤ N →
        (N : ℝ) = (X : ℝ) ^ φ → 9 / 11 ≤ η₀ → η₀ ≤ 5 / 6 →
        η₀ - 10 * εh ≤ φ → φ ≤ 1 - εh / 10 →
        10 * εh ≤ σ → σ ≤ 1 / 4 - 20 * εh →
        σ * (4 * η₀ - 2) + 20 * εh ≤ 8 * η₀ / 5 - 1 →
        V ⊆ Set.Icc 0 (X : ℝ) →
        (∀ t ∈ V, (N : ℝ) ^ (-σ) <
          ‖dyadicDirichletPolynomial c (N : ℝ) (onePlusIT t)‖) →
        volume.real V ≤ C * (X : ℝ) ^ (2 * σ - εh ^ 2 / 2) := by
  obtain ⟨C, T₀, hC, _hT₀, hD⟩ := hdens B hB εh hεh hεh' A hA
  refine ⟨C, hC, ?_⟩
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop T₀,
    eventually_ge_atTop 1] with X hXT hX1
  intro N c V σ φ η₀ hc hN hNφ hη₁ hη₂ hφlo hφhi hσlo hσhi hGM hVsub hlarge
  have hX1' : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  refine measureReal_le_of_subset_of_volume_le
    (L := largeValueSet (dyadicDirichletPolynomial c (N : ℝ)) X ((N : ℝ) ^ (-σ)))
    ?_ ?_ (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))
  · intro t ht
    exact ⟨hVsub ht, hlarge t ht⟩
  · refine hD X N σ η₀ c hXT hN hη₁ hη₂ ?_ ?_ hσlo hσhi hGM hc
    · rw [hNφ]; exact Real.rpow_le_rpow_of_exponent_le hX1' hφlo
    · rw [hNφ]; exact Real.rpow_le_rpow_of_exponent_le hX1' hφhi

/-! ## The second sparse branch in the remaining region

Write `K(θ,σ₁,σ₂) = (5-8σ₁)θ + 2σ₂(1-θ)` for the exponent of the second
branch, `v = 1/a`, and assume the first branch fails:
`1 - v - r ≤ θ(1-2σ₁)`.  The identity
`K = 4θ(1-2σ₁) + θ(1-2σ₂) + 2σ₂` gives `K > v + κ` in each of the three
regions left over by cases (a) and (b). -/

/-- Region A: `σ₁ ≤ σ₂` and `σ₁ ≥ 1/4 - δ₁`. -/
theorem key_regionA {v r κ δ₁ θ σ₁ σ₂ : ℝ} (hθ1 : θ ≤ 1)
    (h12 : σ₁ ≤ σ₂) (hσ₁ : 1 / 4 - δ₁ ≤ σ₁)
    (hprem : 1 - v - r ≤ θ * (1 - 2 * σ₁))
    (hmargin : 1 / 2 + κ + 2 * δ₁ + 5 * r < 6 * (1 - v)) :
    v + κ < Sparse.secondBranchKeyExponent θ σ₁ σ₂ := by
  unfold Sparse.secondBranchKeyExponent
  have h := mul_nonneg (sub_nonneg.mpr h12) (sub_nonneg.mpr hθ1)
  nlinarith

/-- Region B1: `σ₂ < σ₁` and `σ₂ ≥ 1/4 - δ₁`. -/
theorem key_regionB1 {v r κ δ₁ θ σ₁ σ₂ : ℝ} (hθ0 : 0 ≤ θ)
    (h21 : σ₂ < σ₁) (hσ₂ : 1 / 4 - δ₁ ≤ σ₂)
    (hprem : 1 - v - r ≤ θ * (1 - 2 * σ₁))
    (hmargin : 1 / 2 + κ + 2 * δ₁ + 5 * r < 6 * (1 - v)) :
    v + κ < Sparse.secondBranchKeyExponent θ σ₁ σ₂ := by
  unfold Sparse.secondBranchKeyExponent
  have h := mul_nonneg hθ0 (sub_nonneg.mpr h21.le)
  nlinarith

/-- Region B2: `1/6 ≤ θ ≤ 2/11` and `σ₂` lies above the Guth--Maynard
threshold `(3/5 - 8θ/5 - δ₂)/(2 - 4θ)` for polynomials of length
`X^(1-θ)`.  The worst case is `θ = 2/11`, where the threshold is `17/70`
and `θ + 2σ₂(1-θ) ≥ 223/385`. -/
theorem key_regionB2 {v r κ δ₂ θ σ₁ σ₂ : ℝ} (hθ6 : 1 / 6 ≤ θ)
    (hθ211 : θ ≤ 2 / 11) (hδ₂ : 0 ≤ δ₂)
    (hσ₂ : 3 / 5 - 8 * θ / 5 < σ₂ * (2 - 4 * θ) + δ₂)
    (hprem : 1 - v - r ≤ θ * (1 - 2 * σ₁))
    (hmargin : 162 / 385 + κ + 4 * r + 2 * δ₂ < 5 * (1 - v)) :
    v + κ < Sparse.secondBranchKeyExponent θ σ₁ σ₂ := by
  have hpos : 0 < 1 - 2 * θ := by linarith
  have h1 : (1 - θ) * (3 / 5 - 8 * θ / 5 - δ₂) ≤ (1 - θ) * (σ₂ * (2 - 4 * θ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : 0 ≤ (2 - 11 * θ) * (7 * θ + 2) := mul_nonneg (by linarith) (by linarith)
  have h3 : 0 ≤ δ₂ * (1 - 3 * θ) := mul_nonneg hδ₂ (by linarith)
  have hS : (223 / 385 - 2 * δ₂) * (1 - 2 * θ) ≤
      (θ + 2 * σ₂ * (1 - θ)) * (1 - 2 * θ) := by nlinarith
  have hS' : 223 / 385 - 2 * δ₂ ≤ θ + 2 * σ₂ * (1 - θ) :=
    le_of_mul_le_mul_right hS hpos
  unfold Sparse.secondBranchKeyExponent
  nlinarith

/-- The margins available on the window `1925/1763 + η ≤ a ≤ 11/10`, with
the error terms of the sparse package at scale `e`. -/
theorem window_margins {a η e : ℝ} (hη : 0 < η) (he : 0 < e)
    (he1 : e ≤ 1 / 40000) (heη : 40 * e ≤ η)
    (ha : 1925 / 1763 + η ≤ a) (ha' : a ≤ 11 / 10) :
    1 / 2 + (4 * e + e ^ 2 / 25) + 2 * (63 * e) +
        5 * (e / 3 + e ^ 2 / 1000 * (1 - 1 / a)) < 6 * (1 - 1 / a) ∧
      162 / 385 + (4 * e + e ^ 2 / 25) +
          4 * (e / 3 + e ^ 2 / 1000 * (1 - 1 / a)) + 2 * (60 * e) <
        5 * (1 - 1 / a) ∧
      1 / a ≤ 1763 / 1925 ∧
      e / 3 + e ^ 2 / 1000 * (1 - 1 / a) ≤ e := by
  have hapos : 0 < a := by linarith
  set w := 1 / a with hw
  have hwa : w * a = 1 := by rw [hw]; field_simp
  have hw0 : 0 < w := by positivity
  have hw10 : 10 / 11 ≤ w := by
    rw [hw, le_div_iff₀ hapos]; linarith
  have hwη : w * (1925 / 1763) ≤ 1 - 10 / 11 * η := by
    have h1 : w * (1925 / 1763 + η) ≤ w * a := mul_le_mul_of_nonneg_left ha hw0.le
    have h2 : 10 / 11 * η ≤ w * η := mul_le_mul_of_nonneg_right hw10 hη.le
    nlinarith
  have hw1 : w ≤ 1763 / 1925 := by nlinarith
  have hwle1 : w ≤ 1 := by linarith
  have he2 : e ^ 2 ≤ e / 40000 := by nlinarith
  have hr : e ^ 2 / 1000 * (1 - w) ≤ e ^ 2 / 1000 :=
    mul_le_of_le_one_right (by positivity) (by linarith)
  have hr0 : 0 ≤ e ^ 2 / 1000 * (1 - w) :=
    mul_nonneg (by positivity) (by linarith)
  refine ⟨by nlinarith, by nlinarith, hw1, by nlinarith⟩

/-- If the first sparse branch fails at a point of an `R₂` bin, then the
first factor is long: `θ ≥ 1/7`. -/
theorem theta_lower_of_firstBranch_failure {v r θ σ₁ σs : ℝ} (hθ0 : 0 ≤ θ)
    (hσ : σs < σ₁) (hσs : 17 / 70 - 1 / 1000 ≤ σs) (hv : v ≤ 1763 / 1925)
    (hr : r ≤ 1 / 1000) (hprem : 1 - v - r ≤ θ * (1 - 2 * σ₁)) :
    1 / 7 ≤ θ := by
  by_contra h
  replace h := lt_of_not_ge h
  have h1 := mul_le_mul_of_nonneg_left
    (show 1 - 2 * σ₁ ≤ 18 / 35 + 1 / 500 by linarith) hθ0
  nlinarith

/-- **The three cases for one medium bin.**  `vol` is the measure of a bin
with exponents `(σ₁,σ₂)` above the Type II threshold `σs`, `Tg` its sparse
target, and the three hypotheses `hdensA`, `hdensB`, `hsparse` are the
density bound for the powered first factor, the density bound for the
second factor, and the sparse two-branch bound (conditional on its key
inequality).  On the window `a ≥ 1925/1763 + η` one of them always applies. -/
theorem medium_bin_three_cases {vol K Ca Cb Tg X e a r κ θ φ σ₁ σ₂ σs : ℝ}
    (hX : 1 < X) (he0 : 0 < e)
    (hMA : 1 / 2 + κ + 2 * (63 * e) + 5 * r < 6 * (1 - 1 / a))
    (hMB : 162 / 385 + κ + 4 * r + 2 * (60 * e) < 5 * (1 - 1 / a))
    (hv : 1 / a ≤ 1763 / 1925) (hrsmall : r ≤ e) (hesmall : e ≤ 1 / 40000)
    (hθ0 : 0 ≤ θ) (hθhi : θ ≤ 2 / 11) (hθφ : θ + φ ≤ 1)
    (hloss : 1 - θ - φ ≤ e ^ 2 / 100)
    (hσs : 17 / 70 - 1 / 1000 ≤ σs) (h1 : σs < σ₁) (h2 : σs < σ₂)
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCaK : Ca ≤ K) (hCbK : Cb ≤ K)
    (hTg0 : 0 ≤ Tg)
    (hTg : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 / 4 → σ ≤ σ₁ → σ ≤ σ₂ →
      X ^ (2 * σ - e ^ 2 / 200) ≤ Tg)
    (hdensA : 1 / 7 ≤ θ → 10 * (3 * e) ≤ σ₁ → σ₁ ≤ 1 / 4 - 21 * (3 * e) →
      vol ≤ Ca * X ^ (2 * σ₁ - (3 * e) ^ 2 / 4))
    (hdensB : ∀ η₀ : ℝ, 9 / 11 ≤ η₀ → η₀ ≤ 5 / 6 → η₀ - 10 * (3 * e) ≤ φ →
      φ ≤ 1 - 3 * e / 10 → 10 * (3 * e) ≤ σ₂ → σ₂ ≤ 1 / 4 - 20 * (3 * e) →
      σ₂ * (4 * η₀ - 2) + 20 * (3 * e) ≤ 8 * η₀ / 5 - 1 →
      vol ≤ Cb * X ^ (2 * σ₂ - (3 * e) ^ 2 / 2))
    (hsparse : (1 - 1 / a - r ≤ θ * (1 - 2 * σ₁) →
        1 / a + κ < Sparse.secondBranchKeyExponent θ σ₁ σ₂) →
      vol ≤ K * Tg * X ^ (-(e ^ 2))) :
    vol ≤ K * Tg * X ^ (-(e ^ 2)) := by
  by_cases hprem : 1 - 1 / a - r ≤ θ * (1 - 2 * σ₁)
  swap
  · exact hsparse (fun h ↦ absurd h hprem)
  have hθ7 : 1 / 7 ≤ θ :=
    theta_lower_of_firstBranch_failure hθ0 h1 hσs hv (by linarith) hprem
  have hXe : 0 ≤ X ^ (-(e ^ 2)) := Real.rpow_nonneg (by linarith) _
  have hTW : 0 ≤ Tg * X ^ (-(e ^ 2)) := mul_nonneg hTg0 hXe
  have he2 : e ^ 2 ≤ e := by nlinarith
  have hc4 : e ^ 2 + e ^ 2 / 200 ≤ (3 * e) ^ 2 / 4 := by nlinarith
  have hc2 : e ^ 2 + e ^ 2 / 200 ≤ (3 * e) ^ 2 / 2 := by nlinarith
  by_cases hcaseA : σ₁ ≤ σ₂ ∧ σ₁ < 1 / 4 - 63 * e
  · -- case (a): the powered first factor
    obtain ⟨h12, h1lo⟩ := hcaseA
    have hd := hdensA hθ7 (by linarith) (by linarith)
    have hT := hTg σ₁ (by linarith) (by linarith) le_rfl h12
    have hc := density_le_sparseTarget hX hCa hT hc4
    calc vol ≤ _ := hd
      _ ≤ Ca * Tg * X ^ (-(e ^ 2)) := hc
      _ ≤ K * Tg * X ^ (-(e ^ 2)) := by
        rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hCaK hTW
  by_cases hcaseB : σ₂ < σ₁ ∧ σ₂ < 1 / 4 - 63 * e ∧
      (θ < 1 / 6 ∨ σ₂ * (2 - 4 * θ) + 60 * e ≤ 3 / 5 - 8 * θ / 5)
  · -- case (b): the second factor directly
    obtain ⟨h21, h2lo, hGMc⟩ := hcaseB
    obtain ⟨η₀, hη₁, hη₂, hη₃, hη₄⟩ : ∃ η₀ : ℝ, 9 / 11 ≤ η₀ ∧ η₀ ≤ 5 / 6 ∧
        η₀ - 10 * (3 * e) ≤ φ ∧
        σ₂ * (4 * η₀ - 2) + 20 * (3 * e) ≤ 8 * η₀ / 5 - 1 := by
      by_cases hθ6 : θ < 1 / 6
      · exact ⟨5 / 6, by norm_num, le_rfl, by linarith, by linarith⟩
      · have hGM : σ₂ * (2 - 4 * θ) + 60 * e ≤ 3 / 5 - 8 * θ / 5 :=
          hGMc.resolve_left hθ6
        exact ⟨1 - θ, by linarith, by linarith, by linarith, by linarith⟩
    have hd := hdensB η₀ hη₁ hη₂ hη₃ (by linarith) (by linarith) (by linarith) hη₄
    have hT := hTg σ₂ (by linarith) (by linarith) h21.le le_rfl
    have hc := density_le_sparseTarget hX hCb hT hc2
    calc vol ≤ _ := hd
      _ ≤ Cb * Tg * X ^ (-(e ^ 2)) := hc
      _ ≤ K * Tg * X ^ (-(e ^ 2)) := by
        rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hCbK hTW
  -- otherwise the second sparse branch closes
  apply hsparse
  intro _
  rcases le_or_gt σ₁ σ₂ with h12 | h21
  · have hσ₁lo : 1 / 4 - 63 * e ≤ σ₁ := by
      by_contra h
      exact hcaseA ⟨h12, lt_of_not_ge h⟩
    exact key_regionA (by linarith) h12 hσ₁lo hprem hMA
  · by_cases h2lo : 1 / 4 - 63 * e ≤ σ₂
    · exact key_regionB1 hθ0 h21 h2lo hprem hMA
    · replace h2lo := lt_of_not_ge h2lo
      have hθ6 : 1 / 6 ≤ θ := by
        by_contra h
        exact hcaseB ⟨h21, h2lo, Or.inl (lt_of_not_ge h)⟩
      have hGMf : 3 / 5 - 8 * θ / 5 < σ₂ * (2 - 4 * θ) + 60 * e := by
        by_contra h
        exact hcaseB ⟨h21, h2lo, Or.inr (le_of_not_gt h)⟩
      exact key_regionB2 hθ6 hθhi (by positivity) hGMf hprem hMB

end

end Final
end ExactSemiprimes
