import ExactSemiprimes.Final.Counting
import ExactSemiprimes.Results.ParameterTheorem
import ExactSemiprimes.Results.CleanTheorem

/-!
# Section 7.2: from block variances to the dyadic exceptional-set bound

On the scale `[X, 2X]`, sum the buffered prime blocks `P` of the paper.
By the labelled extension (E2) the long averages add up to `≫ 1/log X`;
by Proposition 7.1 (`Final.blockVariance_uniform`) every block deviation has
variance `≪ (log X)^(-2-ε/10)`.  Chebyshev and a union bound over the
`O(log log X)` blocks show that the short averages add up to `≫ 1/log X`
outside a set of measure `≪ X (log X)^(-ε/20)`; [MT23, Theorem 2.1(i)]
(`ρ⁻ ≤ 1_ℙ`) and the unique small prime factor convert a good real point
into the prime-window count at the neighbouring integer.
-/

namespace ExactSemiprimes
namespace Final

open Filter Real MeasureTheory

noncomputable section

/-! ## The pointwise step -/

/-- A good real point `y ∈ [m, m+1)` gives the prime-window count at `m`. -/
theorem windowCount_of_good_point
    {w : ℕ → ℝ} {c Δ κ γ X y : ℝ} {m : ℕ}
    (hminorant : Completion.IsPrimeMinorantOnMatomakiTeravainenRange w X)
    (hX : 2 ≤ X) (hL1 : 1 ≤ Real.log X) (hc : 1 ≤ c) (hc3 : c ≤ 3)
    (hLc : 2 ≤ (Real.log X) ^ c) (hhX : (Real.log X) ^ c / 2 ≤ X)
    (hblocks : ∀ P ∈ Completion.bufferedDyadicScales c Δ X,
      0 < P ∧ 2 * P ≤ (Real.log X) ^ Completion.bufferedPrimeUpperExponent c Δ)
    (hdisj : ((Completion.bufferedDyadicScales c Δ X : Finset ℝ) : Set ℝ).PairwiseDisjoint
      dyadicPrimes)
    (hwin : ∀ P ∈ Completion.bufferedDyadicScales c Δ X, ∀ p ∈ dyadicPrimes P,
      (Real.log (m : ℝ)) ^ (c - 1 - Δ) < (p : ℝ) ∧
        (p : ℝ) ≤ (Real.log (m : ℝ)) ^ (c - 1 - Δ / 2))
    (hcut2 : ((Real.log X) ^ Completion.bufferedPrimeUpperExponent c Δ) ^ 2 ≤ X)
    (hinner : 2 * X ^ (1 / 2 : ℝ) *
      (Real.log X) ^ Completion.bufferedPrimeUpperExponent c Δ ≤ X)
    (hκ : 0 ≤ κ) (hκγ : 3200 * κ ≤ γ)
    (hXm : X ≤ (m : ℝ)) (hm2 : (m : ℝ) ≤ 2 * X)
    (hmy : (m : ℝ) ≤ y) (hym : y < (m : ℝ) + 1) (hy2 : y ≤ 2 * X)
    (hgood : γ / (400 * Real.log X) ≤
      ∑ P ∈ Completion.bufferedDyadicScales c Δ X,
        Completion.weightedPrimeProductSum w P y ((Real.log X) ^ c / 2) /
          ((Real.log X) ^ c / 2)) :
    Results.ParameterWindowCountProperty c Δ κ m := by
  set L := Real.log X with hL
  set s := Completion.bufferedDyadicScales c Δ X with hs
  set Ucut := L ^ Completion.bufferedPrimeUpperExponent c Δ with hUcut
  set h := L ^ c / 2 with hh
  have hLpos : 0 < L := by linarith
  have hXpos : 0 < X := by linarith
  have hhpos : 0 < h := by rw [hh]; linarith
  have hh1 : 1 ≤ h := by rw [hh]; linarith
  have hUpos : 0 < Ucut := Real.rpow_pos_of_pos hLpos _
  have hy0 : 0 ≤ y := le_trans (Nat.cast_nonneg m) hmy
  have hXy : X ≤ y := hXm.trans hmy
  -- step 1: the short sum is at least `h θ`
  have h1 : h * (γ / (400 * L)) ≤ ∑ P ∈ s, Completion.weightedPrimeProductSum w P y h := by
    rw [← Finset.sum_div, le_div_iff₀ hhpos] at hgood
    linarith only [hgood]
  -- step 2: minorant domination
  have h2 : (∑ P ∈ s, Completion.weightedPrimeProductSum w P y h) ≤
      ∑ P ∈ s, Completion.weightedPrimeProductSum Completion.realPrimeIndicator P y h := by
    apply Finset.sum_le_sum
    intro P hP
    apply Completion.weightedPrimeProductSum_le_primeIndicator_on_matomakiTeravainenRange
      hminorant
    intro p hp n hn
    have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpprime.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hpP := (mem_dyadicInterval (hblocks P hP).1.le).mp (Finset.mem_filter.mp hp).1
    have hpU : (p : ℝ) ≤ Ucut := hpP.2.trans (hblocks P hP).2
    rw [shortInterval, mem_natOpenClosedInterval (by positivity) (by positivity)] at hn
    constructor
    · have hsq : 2 * X ^ (1 / 2 : ℝ) ≤ X / Ucut := by
        rw [le_div_iff₀ hUpos]; exact hinner
      have hXU : X / Ucut ≤ y / p := by
        calc X / Ucut ≤ X / p := div_le_div_of_nonneg_left hXpos.le hp0 hpU
          _ ≤ y / p := div_le_div_of_nonneg_right hXy hp0.le
      linarith [hn.1]
    · have hyp : y / p ≤ y := div_le_self hy0 (by linarith)
      have hhp : h / p ≤ h := div_le_self hhpos.le (by linarith)
      linarith [hn.2]
  -- step 3: injection into windowed products
  have hlogm : L ≤ Real.log (m : ℝ) := Real.log_le_log hXpos hXm
  have hLcm : L ^ c ≤ (Real.log (m : ℝ)) ^ c :=
    Real.rpow_le_rpow hLpos.le hlogm (by linarith)
  have h3 := sum_blocks_primeIndicator_le_windowedCount (s := s) (y := y) (h := h)
    (H := (Real.log (m : ℝ)) ^ c) (L' := (Real.log (m : ℝ)) ^ (c - 1 - Δ))
    (U' := (Real.log (m : ℝ)) ^ (c - 1 - Δ / 2)) (Ucut := Ucut) (Xr := X) (m := m)
    hdisj hmy (by linarith [hLcm, hym, hh1, show L ^ c = 2 * h by rw [hh]; ring]) hhpos.le hXy hwin
    (fun P hP p hp ↦
      ((mem_dyadicInterval (hblocks P hP).1.le).mp (Finset.mem_filter.mp hp).1).2.trans
        (hblocks P hP).2) hcut2
  -- step 4: the size of the target
  have hlog2 : Real.log (m : ℝ) ≤ 2 * L := by
    have := Real.log_le_log (by linarith) hm2
    rw [Real.log_mul (by norm_num) hXpos.ne'] at this
    have hl2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
    linarith
  have hpow : (Real.log (m : ℝ)) ^ (c - 1) ≤ 4 * L ^ (c - 1) := by
    calc (Real.log (m : ℝ)) ^ (c - 1) ≤ (2 * L) ^ (c - 1) :=
          Real.rpow_le_rpow (by linarith) hlog2 (by linarith)
      _ = (2 : ℝ) ^ (c - 1) * L ^ (c - 1) := Real.mul_rpow (by norm_num) hLpos.le
      _ ≤ 4 * L ^ (c - 1) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hLpos.le _)
          calc (2 : ℝ) ^ (c - 1) ≤ (2 : ℝ) ^ (2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
            _ = 4 := by norm_num
  have hhθ : h * (γ / (400 * L)) = γ / 800 * L ^ (c - 1) := by
    have : L ^ c = L ^ (c - 1) * L := by
      rw [← Real.rpow_add_one hLpos.ne']; ring_nf
    rw [hh, this]; field_simp; ring
  unfold Results.ParameterWindowCountProperty logarithmicLength
  have hγ0 : 0 ≤ γ := by linarith
  calc κ * (Real.log (m : ℝ)) ^ (c - 1) ≤ κ * (4 * L ^ (c - 1)) :=
        mul_le_mul_of_nonneg_left hpow hκ
    _ ≤ γ / 800 * L ^ (c - 1) := by
        have : 0 ≤ L ^ (c - 1) := Real.rpow_nonneg hLpos.le _
        nlinarith
    _ = h * (γ / (400 * L)) := hhθ.symm
    _ ≤ _ := h1.trans (h2.trans h3)

/-! ## The bad set is covered by the block deviation sets -/

theorem badSet_subset_biUnion {ι : Type*} (s : Finset ι) (a b : ι → ℝ → ℝ)
    {X θ : ℝ} (hθ : 0 < θ)
    (hlong : ∀ y ∈ Set.Ioc X (2 * X), 2 * θ ≤ ∑ i ∈ s, b i y) :
    {y | y ∈ Set.Ioc X (2 * X) ∧ (∑ i ∈ s, a i y) < θ} ⊆
      ⋃ i ∈ s, ({y | (θ / (s.card : ℝ)) ^ (2 : ℕ) ≤ |a i y - b i y| ^ (2 : ℕ)} ∩
        Set.Ioc X (2 * X)) := by
  intro y ⟨hy, hya⟩
  have hb := hlong y hy
  by_contra hnot
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, not_exists, not_and] at hnot
  -- every block deviation is below the threshold
  have hpt : ∀ i ∈ s, |a i y - b i y| ≤ θ / (s.card : ℝ) := by
    intro i hi
    have hlt : |a i y - b i y| ^ (2 : ℕ) < (θ / (s.card : ℝ)) ^ (2 : ℕ) := by
      by_contra hge
      exact hnot i hi (not_lt.mp hge) hy
    exact (pow_lt_pow_iff_left₀ (abs_nonneg _) (by positivity) (by norm_num)).mp hlt |>.le
  have hsum : (∑ i ∈ s, |a i y - b i y|) ≤ θ := by
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [Finset.card_eq_zero.mp h0, Finset.sum_empty]; exact hθ.le
    · calc (∑ i ∈ s, |a i y - b i y|) ≤ ∑ _i ∈ s, θ / (s.card : ℝ) := Finset.sum_le_sum hpt
        _ = θ := by
          rw [Finset.sum_const, nsmul_eq_mul]
          field_simp
  have htri : (∑ i ∈ s, b i y) - ∑ i ∈ s, a i y ≤ ∑ i ∈ s, |a i y - b i y| := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun i _ ↦ by rw [abs_sub_comm]; exact le_abs_self _)
  linarith

/-! ## Arithmetic of the final count -/

theorem final_count_arith {R X Cv L γ ε : ℝ} (hR : 0 ≤ R) (hL : 0 < L) (hγ : 0 < γ)
    (hX : 0 ≤ X) (hCv : 0 ≤ Cv) (hR3 : R ^ (3 : ℕ) ≤ L ^ (ε / 20)) :
    R * ((X * (Cv * L ^ (-(2 + ε / 10)))) / (γ / (400 * L) / R) ^ (2 : ℕ)) ≤
      160000 * Cv / γ ^ (2 : ℕ) * X * L ^ (-(ε / 20)) := by
  rcases eq_or_lt_of_le hR with h0 | hpos
  · rw [← h0]; simp only [zero_mul]; positivity
  have hL2 : L ^ (-(2 + ε / 10)) * L ^ (2 : ℕ) = L ^ (-(ε / 10)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL]; congr 1; push_cast; ring
  have hL3 : L ^ (ε / 20) * L ^ (-(ε / 10)) = L ^ (-(ε / 20)) := by
    rw [← Real.rpow_add hL]; congr 1; ring
  have heq : R * ((X * (Cv * L ^ (-(2 + ε / 10)))) / (γ / (400 * L) / R) ^ (2 : ℕ)) =
      160000 * Cv / γ ^ (2 : ℕ) * X * (R ^ (3 : ℕ) * (L ^ (-(2 + ε / 10)) * L ^ (2 : ℕ))) := by
    field_simp; ring
  rw [heq, hL2, ← hL3]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul_of_nonneg_right hR3 (Real.rpow_nonneg hL.le _)

/-! ## From the scale `X` to the dyadic majorant -/

theorem dyadic_of_eventually_card {Q : ℕ → Prop} {C ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC : 0 ≤ C)
    (h : ∀ᶠ X : ℕ in atTop, ((exceptionalOnDyadicBlock Q X).card : ℝ) ≤
      2 + C * X * (Real.log (X : ℝ)) ^ (-(ε / 20))) :
    (fun k : ℕ ↦ ((exceptionalOnDyadicBlock Q (2 ^ k)).card : ℝ)) =O[atTop]
      Completion.dyadicLogPowerMajorant (ε / 40) := by
  have hpow : Tendsto (fun k : ℕ ↦ 2 ^ k) atTop atTop :=
    tendsto_atTop_mono (fun k ↦ le_of_lt Nat.lt_two_pow_self) tendsto_id
  apply Asymptotics.IsBigO.of_bound (2 + C)
  filter_upwards [hpow.eventually h, eventually_ge_atTop 3] with k hk hk3
  have hk3' : (3 : ℝ) ≤ k := by exact_mod_cast hk3
  have hl2 := Real.log_two_gt_d9
  have hlog : Real.log ((2 ^ k : ℕ) : ℝ) = k * Real.log 2 := by
    push_cast; rw [Real.log_pow]
  have hkl : 0 < (k : ℝ) * Real.log 2 := by positivity
  have hk1 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hsq : ((k + 1 : ℕ) : ℝ) ≤ ((k : ℝ) * Real.log 2) ^ (2 : ℕ) := by
    have hl : (0.48 : ℝ) ≤ (Real.log 2) ^ (2 : ℕ) := by nlinarith
    have hk2 : 3 * (k : ℝ) ≤ (k : ℝ) ^ (2 : ℕ) := by nlinarith
    have e : ((k : ℝ) * Real.log 2) ^ (2 : ℕ) = (k : ℝ) ^ (2 : ℕ) * (Real.log 2) ^ (2 : ℕ) := by
      ring
    rw [e]; push_cast
    have : (k : ℝ) ^ (2 : ℕ) * 0.48 ≤ (k : ℝ) ^ (2 : ℕ) * (Real.log 2) ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    nlinarith
  have hmaj : Completion.dyadicLogPowerMajorant (ε / 40) k =
      (2 : ℝ) ^ k * ((k + 1 : ℕ) : ℝ) ^ (-(ε / 40)) := by
    unfold Completion.dyadicLogPowerMajorant
    rw [Real.rpow_neg hk1.le, div_eq_mul_inv]
  have hmaj0 : 0 ≤ Completion.dyadicLogPowerMajorant (ε / 40) k := by
    rw [hmaj]; positivity
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hmaj0, hmaj]
  have hdecay : ((k : ℝ) * Real.log 2) ^ (-(ε / 20)) ≤ ((k + 1 : ℕ) : ℝ) ^ (-(ε / 40)) := by
    have : ((k : ℝ) * Real.log 2) ^ (-(ε / 20)) =
        (((k : ℝ) * Real.log 2) ^ (2 : ℕ)) ^ (-(ε / 40)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hkl.le]; congr 1; push_cast; ring
    rw [this]
    exact Real.rpow_le_rpow_of_nonpos hk1 hsq (by linarith)
  have htwo : 1 ≤ (2 : ℝ) ^ k * ((k + 1 : ℕ) : ℝ) ^ (-(ε / 40)) := by
    have h1 : ((k + 1 : ℕ) : ℝ) ^ (ε / 40) ≤ ((k + 1 : ℕ) : ℝ) := by
      calc ((k + 1 : ℕ) : ℝ) ^ (ε / 40) ≤ ((k + 1 : ℕ) : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by push_cast; linarith) (by linarith)
        _ = _ := Real.rpow_one _
    have h2 : ((k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ k := by
      have : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
      exact_mod_cast this
    rw [Real.rpow_neg hk1.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
    linarith
  have hk' := hk
  rw [hlog] at hk'
  push_cast at hk'
  calc ((exceptionalOnDyadicBlock Q (2 ^ k)).card : ℝ)
      ≤ 2 + C * (2 : ℝ) ^ k * ((k : ℝ) * Real.log 2) ^ (-(ε / 20)) := hk'
    _ ≤ 2 * ((2 : ℝ) ^ k * ((k + 1 : ℕ) : ℝ) ^ (-(ε / 40))) +
          C * ((2 : ℝ) ^ k * ((k + 1 : ℕ) : ℝ) ^ (-(ε / 40))) := by
        have := mul_le_mul_of_nonneg_left hdecay (show 0 ≤ C * (2 : ℝ) ^ k by positivity)
        nlinarith
    _ = (2 + C) * ((2 : ℝ) ^ k * ((k + 1 : ℕ) : ℝ) ^ (-(ε / 40))) := by ring

/-! ## The exceptional set on one scale -/

theorem rpow_half_sq {X : ℝ} (hX : 0 ≤ X) : (X ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = X := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX]; norm_num

theorem eventually_exceptional_card_le (inputs : ExternalInputs)
    (ext : ParameterExtensionInputs)
    {c Δ : ℝ} (hc : 3688 / 1763 < c) (hcU : c ≤ 21 / 10) (hΔ : 0 < Δ)
    (hwin : 1925 / 1763 < c - 1 - Δ) :
    ∃ κ ε C : ℝ, 0 < κ ∧ 0 < ε ∧ ε ≤ 1 ∧ 0 < C ∧
      ∀ᶠ X : ℕ in atTop,
        ((exceptionalOnDyadicBlock (Results.ParameterWindowCountProperty c Δ κ) X).card : ℝ) ≤
          2 + C * X * (Real.log (X : ℝ)) ^ (-(ε / 20)) := by
  classical
  have hc2 : 2 < c := by linarith
  have haL' : Completion.bufferedPrimeLowerExponent c Δ = c - 1 - 3 * Δ / 4 := rfl
  have haU' : Completion.bufferedPrimeUpperExponent c Δ = c - 1 - 5 * Δ / 8 := rfl
  set aL := Completion.bufferedPrimeLowerExponent c Δ with haL
  set aU := Completion.bufferedPrimeUpperExponent c Δ with haU
  have haL1 : 1 ≤ aL := by rw [haL']; linarith
  have haLpos : 0 < aL := by linarith
  have haU11 : aU ≤ 11 / 10 := by rw [haU']; linarith
  have haUc : aU ≤ c - 1 := by rw [haU']; linarith
  have haU0 : 0 < aU := by rw [haU']; linarith
  set η := aL - 1925 / 1763 with hη
  have hη0 : 0 < η := by rw [hη, haL']; linarith
  obtain ⟨εV, hεV, hV⟩ := blockVariance_uniform inputs ext hc2 hcU η hη0
  obtain ⟨εL, hεL, hLmin⟩ := ext.uniformLongIntervalMinorant
  obtain ⟨εM, hεM, hM⟩ := inputs.matomakiTeravainenTheoremTwoOnePartOne
  set ε := min (min εV εL) (min εM 1) with hεdef
  have hε : 0 < ε := by positivity
  have hεV' : ε ≤ εV := (min_le_left _ _).trans (min_le_left _ _)
  have hεL' : ε ≤ εL := (min_le_left _ _).trans (min_le_right _ _)
  have hεM' : ε ≤ εM := (min_le_right _ _).trans (min_le_left _ _)
  have hε1 : ε ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨Cv, hCv, hVev⟩ := hV ε hε hεV'
  obtain ⟨XL, hXL3, hLb⟩ := hLmin ε hε hεL'
  set γ := Completion.bufferedDyadicLongTotalConstant c Δ with hγdef
  have hrate : 0 < Completion.bufferedDyadicScaleRate Δ := by
    unfold Completion.bufferedDyadicScaleRate
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have hγ : 0 < γ := by
    rw [hγdef, Completion.bufferedDyadicLongTotalConstant]
    exact div_pos hrate (by linarith)
  refine ⟨γ / 3200, ε, 160000 * Cv / γ ^ (2 : ℕ), by positivity, hε, hε1, by positivity, ?_⟩
  have hlogNat : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsizeE := tendsto_natCast_atTop_atTop.eventually
    (Completion.eventually_bufferedDyadicScale_size hΔ)
  have hwinE := tendsto_natCast_atTop_atTop.eventually
    (Completion.eventually_parameter_prime_window_transfer hΔ (by linarith : 0 ≤ c - 1 - Δ))
  have hRE := tendsto_natCast_atTop_atTop.eventually
    (Completion.eventually_blockCount_sq_le_log_rpow (Completion.bufferedDyadicScaleRate Δ)
      hrate.le (η := ε / 40) (by positivity))
  have hcutE := eventually_const_mul_log_rpow_le_rpow 2 (11 / 10) (c := 1 / 2) (by norm_num)
  have hLcE := eventually_const_mul_log_rpow_le_rpow 1 (21 / 10) (c := 1 / 2) (by norm_num)
  filter_upwards [hVev, hsizeE, hwinE, hRE, hcutE, hLcE, hlogNat.eventually_ge_atTop 2,
    eventually_ge_atTop ⌈XL⌉₊, eventually_ge_atTop 3] with
    X hVX hsizeX hwinX hRX hcutX hLcX hlog2 hXLX hX3
  -- basic sizes
  have hX3' : (3 : ℝ) ≤ X := by exact_mod_cast hX3
  have hXpos : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) < X := by linarith
  have hXL' : XL ≤ (X : ℝ) := (Nat.le_ceil XL).trans (by exact_mod_cast hXLX)
  set L := Real.log (X : ℝ) with hL
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  set s := Completion.bufferedDyadicScales c Δ (X : ℝ) with hs
  have hsqX : (0 : ℝ) < (X : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hLc1 : L ≤ L ^ c := by
    calc L = L ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ L ^ c := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hLc : 2 ≤ L ^ c := by linarith
  have hLcX : L ^ c ≤ (X : ℝ) ^ (1 / 2 : ℝ) := by
    have h1 : L ^ c ≤ L ^ (21 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 hcU
    have h2 : 1 * L ^ (21 / 10 : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) := hLcX
    linarith
  have hhX : L ^ c / 2 ≤ (X : ℝ) := by
    have : (X : ℝ) ^ (1 / 2 : ℝ) ≤ (X : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num)
    rw [Real.rpow_one] at this
    linarith
  have hUle : L ^ aU ≤ L ^ (11 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 haU11
  have hU0 : 0 < L ^ aU := Real.rpow_pos_of_pos hLpos _
  have hcutX' : 2 * L ^ (11 / 10 : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) := hcutX
  have hcut2 : (L ^ aU) ^ (2 : ℕ) ≤ (X : ℝ) := by
    have h1 : L ^ aU ≤ (X : ℝ) ^ (1 / 2 : ℝ) := by linarith
    calc (L ^ aU) ^ (2 : ℕ) ≤ ((X : ℝ) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) :=
          pow_le_pow_left₀ hU0.le h1 2
      _ = X := rpow_half_sq hXpos.le
  have hinner : 2 * (X : ℝ) ^ (1 / 2 : ℝ) * L ^ aU ≤ X := by
    have h1 : 2 * L ^ aU ≤ (X : ℝ) ^ (1 / 2 : ℝ) := by linarith
    calc 2 * (X : ℝ) ^ (1 / 2 : ℝ) * L ^ aU = (X : ℝ) ^ (1 / 2 : ℝ) * (2 * L ^ aU) := by ring
      _ ≤ (X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left h1 hsqX.le
      _ = X := by rw [← pow_two]; exact rpow_half_sq hXpos.le
  -- the minorant and the blocks
  have hminorant : Completion.IsPrimeMinorantOnMatomakiTeravainenRange
      (matomakiTeravainenMinorant (X : ℝ) ε) (X : ℝ) := by
    intro n hn1 hn2
    exact hM ε hε hεM' (X : ℝ) hX3' (11 / 10) (by norm_num) (by norm_num) n hn1 hn2
  have hblocksW : ∀ P ∈ s, L ^ aL < P ∧ 2 * P ≤ L ^ aU := fun P hP ↦
    Completion.bufferedDyadicScales_mem_window hΔ hsizeX.1 hsizeX.2 hP
  have hblocks : ∀ P ∈ s, 0 < P ∧ 2 * P ≤ L ^ aU := fun P hP ↦
    ⟨(Real.rpow_pos_of_pos hLpos _).trans (hblocksW P hP).1, (hblocksW P hP).2⟩
  have hdisj := bufferedDyadicScales_pairwiseDisjoint (c := c) (Δ := Δ) hX1
  -- the block variances
  set h := L ^ c / 2 with hh
  set h₁ := (X : ℝ) ^ (99 / 100 : ℝ) with hh₁
  have hhpos : 0 < h := by rw [hh]; linarith
  have hh₁pos : 0 < h₁ := Real.rpow_pos_of_pos hXpos _
  set V := (X : ℝ) * (Cv * L ^ (-(2 + ε / 10))) with hVdef
  have hvar : ∀ P ∈ s, (∫ y in Set.Ioc (X : ℝ) (2 * X),
      |Completion.weightedPrimeProductSum (matomakiTeravainenMinorant (X : ℝ) ε) P y h / h -
        Completion.weightedPrimeProductSum (matomakiTeravainenMinorant (X : ℝ) ε) P y h₁ / h₁| ^
          (2 : ℕ)) ≤ V := by
    intro P hP
    have hPlo : L ^ (1925 / 1763 + η) ≤ P := by
      have : 1925 / 1763 + η = aL := by rw [hη]; ring
      rw [this]; exact (hblocksW P hP).1.le
    have hPhi : P ≤ L ^ (c - 1) := by
      have h1 := hblocks P hP
      have h2 : L ^ aU ≤ L ^ (c - 1) := Real.rpow_le_rpow_of_exponent_le hL1 haUc
      linarith
    have hv := hVX P hPlo hPhi
    unfold matomakiTeravainenShortLongVariance at hv
    rw [one_div, inv_mul_le_iff₀ hXpos] at hv
    exact hv
  -- the long averages
  have hlong : ∀ P ∈ s, Completion.HasLongIntervalMinorantLowerBound
      (matomakiTeravainenMinorant (X : ℝ) ε) (X : ℝ) P := by
    intro P hP
    have hPpos := (hblocks P hP).1
    have ha1 : 1 ≤ scaleExponent (X : ℝ) P := by
      apply le_scaleExponent_of_rpow_le hsizeX.1 hPpos
      rw [Real.rpow_one]
      have : L ≤ L ^ aL := by
        calc L = L ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ L ^ aL := Real.rpow_le_rpow_of_exponent_le hL1 haL1
      linarith [(hblocksW P hP).1]
    have ha11 : scaleExponent (X : ℝ) P ≤ 11 / 10 := by
      apply scaleExponent_le_of_le_rpow hsizeX.1 hPpos
      linarith [(hblocks P hP).2, hUle]
    have hb := hLb (X : ℝ) hXL' (scaleExponent (X : ℝ) P) ha1 ha11
    dsimp only at hb
    rw [rpow_scaleExponent hsizeX.1 hPpos] at hb
    exact hb
  set θ := γ / (400 * L) with hθ
  have hθpos : 0 < θ := by positivity
  have hlongθ : ∀ y ∈ Set.Ioc (X : ℝ) (2 * X), 2 * θ ≤
      ∑ P ∈ s, Completion.weightedPrimeProductSum (matomakiTeravainenMinorant (X : ℝ) ε)
        P y h₁ / h₁ := by
    intro y hy
    have := Completion.bufferedDyadicScales_longTotal_lower_bound hΔ haLpos hsizeX.1 hsizeX.2
      hlong hy.1 hy.2
    have e : 2 * θ = γ / (200 * L) := by rw [hθ]; field_simp; ring
    rw [e]
    exact this
  -- the number of blocks
  have hcard : (s.card : ℝ) = (Completion.bufferedDyadicScaleCount Δ (X : ℝ) : ℝ) := by
    rw [hs, Completion.card_bufferedDyadicScales hX1]
  have hRle : (s.card : ℝ) ≤ Completion.bufferedDyadicScaleRate Δ * Real.log L := by
    rw [hcard, Completion.bufferedDyadicScaleCount]
    exact Nat.floor_le (by linarith [hsizeX.2])
  have hR1 : (1 : ℝ) ≤ s.card := by
    rw [hcard, Completion.bufferedDyadicScaleCount]
    have : 1 ≤ ⌊Completion.bufferedDyadicScaleRate Δ * Real.log (Real.log (X : ℝ))⌋₊ :=
      Nat.le_floor (by push_cast; linarith [hsizeX.2])
    exact_mod_cast this
  have hR2 := hRX (s.card : ℝ) (by linarith) hRle
  have hR3 : (s.card : ℝ) ^ (3 : ℕ) ≤ L ^ (ε / 20) := by
    have h1 : (s.card : ℝ) ^ (3 : ℕ) ≤ ((s.card : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) := by
      rw [← pow_mul]; exact pow_le_pow_right₀ hR1 (by norm_num)
    have h2 : ((s.card : ℝ) ^ (2 : ℕ)) ^ (2 : ℕ) ≤ (L ^ (ε / 40)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (by positivity) hR2 2
    have h3 : (L ^ (ε / 40)) ^ (2 : ℕ) = L ^ (ε / 20) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; congr 1; push_cast; ring
    linarith
  -- the real bad set
  set realBad : ℝ → Prop := fun y ↦ y ∈ Set.Ioc (X : ℝ) (2 * X) ∧
    (∑ P ∈ s, Completion.weightedPrimeProductSum (matomakiTeravainenMinorant (X : ℝ) ε)
      P y h / h) < θ with hrealBad
  have hcover := badSet_subset_biUnion s
    (fun P y ↦ Completion.weightedPrimeProductSum (matomakiTeravainenMinorant (X : ℝ) ε)
      P y h / h)
    (fun P y ↦ Completion.weightedPrimeProductSum (matomakiTeravainenMinorant (X : ℝ) ε)
      P y h₁ / h₁) hθpos hlongθ
  have hθR : 0 < (θ / (s.card : ℝ)) ^ (2 : ℕ) := by
    have : 0 < (s.card : ℝ) := by linarith
    positivity
  have hvol := volume_le_of_subset_biUnion s
    (fun P y ↦ |Completion.weightedPrimeProductSum (matomakiTeravainenMinorant (X : ℝ) ε)
        P y h / h -
      Completion.weightedPrimeProductSum (matomakiTeravainenMinorant (X : ℝ) ε)
        P y h₁ / h₁| ^ (2 : ℕ)) hθR hcover
    (fun P _ ↦ integrableOn_blockDeviation_sq _ (X : ℝ) P h h₁ hXpos.le hhpos hh₁pos)
    (fun P _ y ↦ by positivity) hvar
  -- integer exceptions in the interior
  have htransfer : ∀ m ∈ Finset.Icc (X + 1) (2 * X - 1),
      ¬ Results.ParameterWindowCountProperty c Δ (γ / 3200) m →
        Set.Ico (m : ℝ) ((m : ℝ) + 1) ⊆ {y | realBad y} := by
    intro m hm hbad y hy
    by_contra hyB
    apply hbad
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    have hm1' : (X : ℝ) + 1 ≤ m := by exact_mod_cast hm1
    have hm2' : (m : ℝ) + 1 ≤ 2 * X := by
      have : m + 1 ≤ 2 * X := by omega
      exact_mod_cast this
    have hyI : y ∈ Set.Ioc (X : ℝ) (2 * X) :=
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hgood : θ ≤ ∑ P ∈ s, Completion.weightedPrimeProductSum
        (matomakiTeravainenMinorant (X : ℝ) ε) P y h / h := by
      by_contra hlt
      exact hyB ⟨hyI, lt_of_not_ge hlt⟩
    have hXm : (X : ℝ) ≤ m := by linarith
    have hm2'' : (m : ℝ) ≤ 2 * X := by linarith
    refine windowCount_of_good_point hminorant (by linarith) hL1 (by linarith) (by linarith)
      hLc hhX hblocks hdisj ?_ hcut2 hinner (by positivity) (by linarith) hXm hm2''
      hy.1 hy.2 (by linarith [hy.2]) hgood
    intro P hP p hp
    have hPpos := (hblocks P hP).1
    exact hwinX m P p hXm hm2'' (hblocksW P hP).1 (hblocksW P hP).2
      ((mem_dyadicInterval hPpos.le).mp (Finset.mem_filter.mp hp).1)
  have hF := Completion.card_filter_le_volume_of_unitInterval_transfer
    (Finset.Icc (X + 1) (2 * X - 1))
    (fun m ↦ ¬ Results.ParameterWindowCountProperty c Δ (γ / 3200) m) realBad htransfer
  set F := (Finset.Icc (X + 1) (2 * X - 1)).filter
    (fun m ↦ ¬ Results.ParameterWindowCountProperty c Δ (γ / 3200) m) with hFdef
  have hFreal : (F.card : ℝ) ≤ (s.card : ℝ) *
      (V / (θ / (s.card : ℝ)) ^ (2 : ℕ)) := by
    have h1 := hF.trans hvol
    have hne : (s.card : ENNReal) * ENNReal.ofReal (V / (θ / (s.card : ℝ)) ^ (2 : ℕ)) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
    have h2 := ENNReal.toReal_mono hne h1
    have hV00 : 0 ≤ V := mul_nonneg hXpos.le (mul_nonneg hCv.le (Real.rpow_nonneg hLpos.le _))
    have hV0 : 0 ≤ V / (θ / (s.card : ℝ)) ^ (2 : ℕ) := div_nonneg hV00 (sq_nonneg _)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hV0,
      ENNReal.toReal_natCast] at h2
  -- assembling
  have hsub : exceptionalOnDyadicBlock (Results.ParameterWindowCountProperty c Δ (γ / 3200)) X ⊆
      insert X (insert (2 * X) F) := by
    intro n hn
    simp only [exceptionalOnDyadicBlock, Finset.mem_filter, Finset.mem_Icc] at hn
    simp only [Finset.mem_insert, hFdef, Finset.mem_filter, Finset.mem_Icc]
    by_cases h1 : n = X
    · exact Or.inl h1
    · by_cases h2 : n = 2 * X
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr ⟨⟨by omega, by omega⟩, hn.2⟩)
  have hcardE : (exceptionalOnDyadicBlock (Results.ParameterWindowCountProperty c Δ (γ / 3200))
      X).card ≤ F.card + 2 := by
    calc _ ≤ (insert X (insert (2 * X) F)).card := Finset.card_le_card hsub
      _ ≤ (insert (2 * X) F).card + 1 := Finset.card_insert_le _ _
      _ ≤ F.card + 1 + 1 := by gcongr; exact Finset.card_insert_le _ _
  have hcardE' : ((exceptionalOnDyadicBlock (Results.ParameterWindowCountProperty c Δ (γ / 3200))
      X).card : ℝ) ≤ F.card + 2 := by exact_mod_cast hcardE
  have hfinal := final_count_arith (R := (s.card : ℝ)) (X := (X : ℝ)) (Cv := Cv) (L := L)
    (γ := γ) (ε := ε) (Nat.cast_nonneg _) hLpos hγ hXpos.le hCv.le hR3
  exact hcardE'.trans (by linarith only [hFreal, hfinal])

/-! ## The paper's theorems -/

/-- **Section 7.2**: the dyadic prime-window statement for every
`3688/1763 < c ≤ 21/10`. -/
theorem parameterDyadicWindowCount_of_inputs (inputs : ExternalInputs)
    (ext : ParameterExtensionInputs) : Results.ParameterDyadicWindowCountStatement := by
  intro c hc hcU Δ hΔ hwin
  obtain ⟨κ, ε, C, hκ, hε, hε1, hC, hev⟩ :=
    eventually_exceptional_card_le inputs ext hc hcU hΔ hwin
  exact ⟨κ, ε / 40, hκ, by positivity, dyadic_of_eventually_card hε hε1 hC.le hev⟩

/-- **Theorem 1.3** (every `c > 3688/1763`) from the cited inputs and the
labelled parameter extensions. -/
theorem parameterTheorem_of_inputs (inputs : ExternalInputs)
    (ext : ParameterExtensionInputs) : Results.ParameterTheoremStatement :=
  Results.parameterTheorem_of_dyadicWindowCount
    (parameterDyadicWindowCount_of_inputs inputs ext)

/-- **Theorem 1.2** (the exponent `2.092`) from the cited inputs and the
labelled parameter extensions. -/
theorem cleanTheorem_of_inputs (inputs : ExternalInputs)
    (ext : ParameterExtensionInputs) : Results.CleanTheoremStatement :=
  Results.cleanTheorem_of_parameterTheorem (parameterTheorem_of_inputs inputs ext)

end

end Final
end ExactSemiprimes
