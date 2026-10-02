import ExactSemiprimes.Completion.LongIntervalMinorant
import ExactSemiprimes.Assumptions

/-! # Summation over buffered dyadic prime blocks -/

namespace ExactSemiprimes
namespace Completion

open Filter
open scoped BigOperators

noncomputable section

/-! ## The explicit buffered family -/

/-- The lower exponent in the buffered block window of Section 7.2. -/
def bufferedPrimeLowerExponent (c Δ : ℝ) : ℝ :=
  c - 1 - 3 * Δ / 4

/-- The upper exponent in the buffered block window of Section 7.2. -/
def bufferedPrimeUpperExponent (c Δ : ℝ) : ℝ :=
  c - 1 - 5 * Δ / 8

/-- A deliberately conservative proportion of `log log X` blocks.

The full logarithmic width of the buffered window is
`(Δ / (8 log 2)) log log X`.  Taking one quarter of that width leaves
room for the initial factor two and the integer part. -/
def bufferedDyadicScaleRate (Δ : ℝ) : ℝ :=
  Δ / (32 * Real.log 2)

/-- The number of scales in the explicit buffered family. -/
def bufferedDyadicScaleCount (Δ X : ℝ) : ℕ :=
  ⌊bufferedDyadicScaleRate Δ * Real.log (Real.log X)⌋₊

/-- The explicit `C log log X` used as the common upper bound for
`log P` over the buffered family. -/
def bufferedDyadicCommonLogBound (c Δ X : ℝ) : ℝ :=
  bufferedPrimeUpperExponent c Δ * Real.log (Real.log X)

/-- The fixed positive constant left after block count cancels the common
logarithmic scale. -/
def bufferedDyadicLongTotalConstant (c Δ : ℝ) : ℝ :=
  bufferedDyadicScaleRate Δ / (2 * bufferedPrimeUpperExponent c Δ)

/-- An explicit family of pairwise distinct, successively doubled scales.

Writing `A=(log X)^(c-1-3Δ/4)`, these are
`2A,4A,…,2^m A`, where `m=bufferedDyadicScaleCount Δ X`.  Hence the
associated half-open blocks `(P,2P]` are adjacent and disjoint. -/
def bufferedDyadicScales (c Δ X : ℝ) : Finset ℝ :=
  (Finset.range (bufferedDyadicScaleCount Δ X)).image fun k ↦
    (Real.log X) ^ (bufferedPrimeLowerExponent c Δ) *
      (2 : ℝ) ^ (k + 1)

/-- The logarithmic exponent of a positive scale `P` relative to the base
`log X`.  For the large values of `X` used below, `log X > 1`, so this is
the unique exponent `a` for which `P = (log X)^a`. -/
def bufferedDyadicExponent (X P : ℝ) : ℝ :=
  Real.logb (Real.log X) P

theorem mem_bufferedDyadicScales {c Δ X P : ℝ} :
    P ∈ bufferedDyadicScales c Δ X ↔
      ∃ k < bufferedDyadicScaleCount Δ X,
        P = (Real.log X) ^ (bufferedPrimeLowerExponent c Δ) *
          (2 : ℝ) ^ (k + 1) := by
  simp only [bufferedDyadicScales, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩

/-- No scales are lost when passing from the index interval to its image. -/
theorem card_bufferedDyadicScales {c Δ X : ℝ} (hX : 1 < X) :
    (bufferedDyadicScales c Δ X).card =
      bufferedDyadicScaleCount Δ X := by
  calc
    (bufferedDyadicScales c Δ X).card =
        (Finset.range (bufferedDyadicScaleCount Δ X)).card := by
      apply Finset.card_image_of_injective
      intro i j hij
      have hlogXpos : 0 < Real.log X := Real.log_pos hX
      have hA : 0 <
          (Real.log X) ^ (bufferedPrimeLowerExponent c Δ) :=
        Real.rpow_pos_of_pos hlogXpos _
      have hpows : (2 : ℝ) ^ (i + 1) = (2 : ℝ) ^ (j + 1) :=
        mul_left_cancel₀ hA.ne' hij
      have hij' : i + 1 = j + 1 :=
        (pow_right_injective₀ (by norm_num : (0 : ℝ) < 2)
          (by norm_num : (2 : ℝ) ≠ 1)) hpows
      omega
    _ = bufferedDyadicScaleCount Δ X := Finset.card_range _

/-- For fixed positive `Δ`, the two elementary largeness conditions used
to count and place the blocks hold for all sufficiently large `X`. -/
theorem eventually_bufferedDyadicScale_size { Δ : ℝ } (hΔ : 0 < Δ) :
    ∀ᶠ X : ℝ in atTop,
      Real.exp 1 < X ∧
        2 ≤ bufferedDyadicScaleRate Δ * Real.log (Real.log X) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hrate : 0 < bufferedDyadicScaleRate Δ := by
    rw [bufferedDyadicScaleRate]
    positivity
  have hloglog :
      Tendsto (fun X : ℝ ↦ Real.log (Real.log X)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hlarge := hloglog.eventually
    (eventually_ge_atTop (2 / bufferedDyadicScaleRate Δ))
  filter_upwards [eventually_gt_atTop (Real.exp 1), hlarge] with X hX hll
  refine ⟨hX, ?_⟩
  have := (div_le_iff₀ hrate).mp hll
  simpa [mul_comm] using this

/-- Every scale in the explicit family satisfies exactly the two buffered
inequalities used in the paper. -/
theorem bufferedDyadicScales_mem_window
    {c Δ X P : ℝ} (hΔ : 0 < Δ)
    (hX : Real.exp 1 < X)
    (hsize : 2 ≤
      bufferedDyadicScaleRate Δ * Real.log (Real.log X))
    (hP : P ∈ bufferedDyadicScales c Δ X) :
    (Real.log X) ^ (bufferedPrimeLowerExponent c Δ) < P ∧
      2 * P ≤
        (Real.log X) ^ (bufferedPrimeUpperExponent c Δ) := by
  rcases mem_bufferedDyadicScales.mp hP with ⟨k, hk, rfl⟩
  have hXone : 1 < X := (Real.one_lt_exp_iff.mpr zero_lt_one).trans hX
  have hlogXpos : 0 < Real.log X := Real.log_pos hXone
  have hA : 0 <
      (Real.log X) ^ (bufferedPrimeLowerExponent c Δ) :=
    Real.rpow_pos_of_pos hlogXpos _
  have hfirstPow : 1 < (2 : ℝ) ^ (k + 1) :=
    one_lt_pow₀ (by norm_num) (by omega)
  constructor
  · nlinarith [mul_lt_mul_of_pos_left hfirstPow hA]
  · have hlog2 : 0 < Real.log (2 : ℝ) :=
      Real.log_pos (by norm_num)
    let y : ℝ :=
      bufferedDyadicScaleRate Δ * Real.log (Real.log X)
    have hy : 2 ≤ y := hsize
    have hkCount : k + 1 ≤ bufferedDyadicScaleCount Δ X := by omega
    have hcountLe : (bufferedDyadicScaleCount Δ X : ℝ) ≤ y := by
      rw [bufferedDyadicScaleCount]
      exact Nat.floor_le (by linarith)
    have hkReal : ((k + 2 : ℕ) : ℝ) ≤ 4 * y := by
      have hkcast : ((k + 1 : ℕ) : ℝ) ≤
          (bufferedDyadicScaleCount Δ X : ℝ) :=
        Nat.cast_le.mpr hkCount
      push_cast at hkcast ⊢
      dsimp [y] at hy ⊢
      nlinarith
    have hexponent : ((k + 2 : ℕ) : ℝ) ≤
        (Δ / (8 * Real.log 2)) * Real.log (Real.log X) := by
      calc
        ((k + 2 : ℕ) : ℝ) ≤ 4 * y := hkReal
        _ = (Δ / (8 * Real.log 2)) * Real.log (Real.log X) := by
          rw [show y = bufferedDyadicScaleRate Δ *
            Real.log (Real.log X) by rfl]
          rw [bufferedDyadicScaleRate]
          field_simp [ne_of_gt hlog2]
          ring
    have hpow : (2 : ℝ) ^ (k + 2) ≤
        (Real.log X) ^ (Δ / 8) := by
      rw [← Real.rpow_natCast]
      calc
        (2 : ℝ) ^ (((k + 2 : ℕ) : ℝ)) ≤
            (2 : ℝ) ^ ((Δ / (8 * Real.log 2)) *
              Real.log (Real.log X)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
        _ = (Real.log X) ^ (Δ / 8) := by
          rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
            Real.rpow_def_of_pos hlogXpos]
          congr 1
          field_simp [ne_of_gt hlog2]
    have hmul :
        (Real.log X) ^ (bufferedPrimeLowerExponent c Δ) *
            (2 : ℝ) ^ (k + 2) ≤
          (Real.log X) ^ (bufferedPrimeLowerExponent c Δ) *
            (Real.log X) ^ (Δ / 8) :=
      mul_le_mul_of_nonneg_left hpow hA.le
    calc
      2 * ((Real.log X) ^ (bufferedPrimeLowerExponent c Δ) *
          (2 : ℝ) ^ (k + 1)) =
          (Real.log X) ^ (bufferedPrimeLowerExponent c Δ) *
            (2 : ℝ) ^ (k + 2) := by
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
        ring
      _ ≤ (Real.log X) ^ (bufferedPrimeLowerExponent c Δ) *
          (Real.log X) ^ (Δ / 8) := hmul
      _ = (Real.log X) ^ (bufferedPrimeUpperExponent c Δ) := by
        rw [← Real.rpow_add hlogXpos]
        congr 1
        simp [bufferedPrimeLowerExponent, bufferedPrimeUpperExponent]
        ring

/-! ## Compatibility with the exact printed `a`-window -/

/-- Every buffered dyadic scale is literally a power `(log X)^a`.  This
elementary logarithmic reparametrization is the bridge needed to apply the
published long-interval theorem, whose scale is stated in that form. -/
theorem bufferedDyadicScale_eq_log_rpow_exponent
    {c Δ X P : ℝ} (hΔ : 0 < Δ)
    (hX : Real.exp 1 < X)
    (hsize : 2 ≤
      bufferedDyadicScaleRate Δ * Real.log (Real.log X))
    (hP : P ∈ bufferedDyadicScales c Δ X) :
    (Real.log X) ^ (bufferedDyadicExponent X P) = P := by
  have hXone : 1 < X := (Real.one_lt_exp_iff.mpr zero_lt_one).trans hX
  have hlogXpos : 0 < Real.log X := Real.log_pos hXone
  have hlogXone : 1 < Real.log X := by
    rw [Real.lt_log_iff_exp_lt (lt_trans zero_lt_one hXone)]
    simpa using hX
  have hw := bufferedDyadicScales_mem_window hΔ hX hsize hP
  have hPpos : 0 < P :=
    (Real.rpow_pos_of_pos hlogXpos _).trans hw.1
  exact Real.rpow_logb hlogXpos hlogXone.ne' hPpos

/-- If `0 < Δ ≤ 1/7500`, then every scale in the buffered family at
`c = 2.1` has a logarithmic exponent in the *exact* interval
`[c-1-1/10000,c-1]` printed in [MT23, Theorem 2.1(ii)].

The constant `1/7500` is forced by
`3Δ/4 ≤ 1/10000`; it does not strengthen the cited theorem. -/
theorem bufferedDyadicExponent_mem_printed_window
    {Δ X P : ℝ} (hΔ : 0 < Δ) (hΔUpper : Δ ≤ 1 / 7500)
    (hX : Real.exp 1 < X)
    (hsize : 2 ≤
      bufferedDyadicScaleRate Δ * Real.log (Real.log X))
    (hP : P ∈ bufferedDyadicScales (21 / 10 : ℝ) Δ X) :
    (21 / 10 : ℝ) - 1 - 1 / 10000 ≤
        bufferedDyadicExponent X P ∧
      bufferedDyadicExponent X P ≤ (21 / 10 : ℝ) - 1 := by
  have hXone : 1 < X := (Real.one_lt_exp_iff.mpr zero_lt_one).trans hX
  have hlogXpos : 0 < Real.log X := Real.log_pos hXone
  have hlogXone : 1 < Real.log X := by
    rw [Real.lt_log_iff_exp_lt (lt_trans zero_lt_one hXone)]
    simpa using hX
  have hw := bufferedDyadicScales_mem_window hΔ hX hsize hP
  have hPpos : 0 < P :=
    (Real.rpow_pos_of_pos hlogXpos _).trans hw.1
  have hLowerExponent :
      bufferedPrimeLowerExponent (21 / 10 : ℝ) Δ ≤
        bufferedDyadicExponent X P := by
    apply (Real.le_logb_iff_rpow_le hlogXone hPpos).2
    exact hw.1.le
  have hPupper :
      P ≤ (Real.log X) ^
        (bufferedPrimeUpperExponent (21 / 10 : ℝ) Δ) := by
    have hPnonneg : 0 ≤ P := hPpos.le
    exact (show P ≤ 2 * P by nlinarith).trans hw.2
  have hUpperExponent :
      bufferedDyadicExponent X P ≤
        bufferedPrimeUpperExponent (21 / 10 : ℝ) Δ :=
    (Real.logb_le_iff_le_rpow hlogXone hPpos).2 hPupper
  constructor
  · dsimp only [bufferedPrimeLowerExponent] at hLowerExponent
    norm_num at hLowerExponent ⊢
    linarith
  · dsimp only [bufferedPrimeUpperExponent] at hUpperExponent
    norm_num at hUpperExponent ⊢
    linarith

/-- Direct existential packaging of the preceding two lemmas: every selected
scale is of the exact form required by the cited theorem, with a witness in
its printed exponent window. -/
theorem exists_printed_exponent_of_mem_bufferedDyadicScales
    {Δ X P : ℝ} (hΔ : 0 < Δ) (hΔUpper : Δ ≤ 1 / 7500)
    (hX : Real.exp 1 < X)
    (hsize : 2 ≤
      bufferedDyadicScaleRate Δ * Real.log (Real.log X))
    (hP : P ∈ bufferedDyadicScales (21 / 10 : ℝ) Δ X) :
    ∃ a : ℝ,
      (21 / 10 : ℝ) - 1 - 1 / 10000 ≤ a ∧
        a ≤ (21 / 10 : ℝ) - 1 ∧
        P = (Real.log X) ^ a := by
  refine ⟨bufferedDyadicExponent X P, ?_, ?_, ?_⟩
  · exact (bufferedDyadicExponent_mem_printed_window
      hΔ hΔUpper hX hsize hP).1
  · exact (bufferedDyadicExponent_mem_printed_window
      hΔ hΔUpper hX hsize hP).2
  · exact (bufferedDyadicScale_eq_log_rpow_exponent
      hΔ hX hsize hP).symm

/-- A quantitative lower bound for the number of selected blocks. -/
theorem bufferedDyadicScales_card_lower
    {c Δ X : ℝ} (hX : Real.exp 1 < X)
    (hsize : 2 ≤
      bufferedDyadicScaleRate Δ * Real.log (Real.log X)) :
    (bufferedDyadicScaleRate Δ / 2) * Real.log (Real.log X) ≤
      ((bufferedDyadicScales c Δ X).card : ℝ) := by
  have hXone : 1 < X := (Real.one_lt_exp_iff.mpr zero_lt_one).trans hX
  rw [card_bufferedDyadicScales hXone]
  have hf := Nat.sub_one_lt_floor
    (bufferedDyadicScaleRate Δ * Real.log (Real.log X))
  change bufferedDyadicScaleRate Δ * Real.log (Real.log X) - 1 <
    (bufferedDyadicScaleCount Δ X : ℝ) at hf
  dsimp [bufferedDyadicScaleCount] at hf
  calc
    (bufferedDyadicScaleRate Δ / 2) * Real.log (Real.log X) =
        (bufferedDyadicScaleRate Δ * Real.log (Real.log X)) / 2 := by
      ring
    _ ≤ bufferedDyadicScaleRate Δ * Real.log (Real.log X) - 1 := by
      linarith
    _ ≤ (bufferedDyadicScaleCount Δ X : ℝ) := hf.le

/-- The common logarithmic upper bound needed in `longTotal_lower_bound`.
It is explicit, uniform over the family, and of order `log log X`. -/
theorem bufferedDyadicScales_log_bound
    {c Δ X P : ℝ} (hΔ : 0 < Δ)
    (ha : 0 < bufferedPrimeLowerExponent c Δ)
    (hX : Real.exp 1 < X)
    (hsize : 2 ≤
      bufferedDyadicScaleRate Δ * Real.log (Real.log X))
    (hP : P ∈ bufferedDyadicScales c Δ X) :
    0 < Real.log P ∧
      Real.log P ≤
        bufferedPrimeUpperExponent c Δ * Real.log (Real.log X) := by
  have hw := bufferedDyadicScales_mem_window hΔ hX hsize hP
  have hXone : 1 < X := (Real.one_lt_exp_iff.mpr zero_lt_one).trans hX
  have hlogXpos : 0 < Real.log X := Real.log_pos hXone
  have hlogXone : 1 < Real.log X := by
    rw [Real.lt_log_iff_exp_lt (lt_trans zero_lt_one hXone)]
    simpa using hX
  have hAone :
      1 < (Real.log X) ^ (bufferedPrimeLowerExponent c Δ) :=
    Real.one_lt_rpow hlogXone ha
  have hPone : 1 < P := hAone.trans hw.1
  have hPpos : 0 < P := zero_lt_one.trans hPone
  constructor
  · exact Real.log_pos hPone
  · have hPle :
        P ≤ (Real.log X) ^ (bufferedPrimeUpperExponent c Δ) := by
      nlinarith
    calc
      Real.log P ≤
          Real.log ((Real.log X) ^ (bufferedPrimeUpperExponent c Δ)) :=
        Real.log_le_log hPpos hPle
      _ = bufferedPrimeUpperExponent c Δ * Real.log (Real.log X) :=
        Real.log_rpow hlogXpos _

/-- Sum of the normalized prime-product averages over a finite family of
dyadic scales.  The selected blocks are disjoint in the paper, but disjointness
is not needed for the lower-bound summation itself. -/
def weightedPrimeProductAverageOverScales
    (weight : ℕ → ℝ) (scales : Finset ℝ) (x h : ℝ) : ℝ :=
  ∑ P ∈ scales, weightedPrimeProductAverage weight P x h

/-- Summing a uniform pointwise lower bound over the selected scales. -/
theorem sum_block_lower_bounds
    {weight : ℕ → ℝ} {scales : Finset ℝ} {x h : ℝ}
    {lower : ℝ → ℝ}
    (hblock : ∀ P ∈ scales,
      lower P ≤ weightedPrimeProductAverage weight P x h) :
    ∑ P ∈ scales, lower P ≤
      weightedPrimeProductAverageOverScales weight scales x h := by
  exact Finset.sum_le_sum fun P hP ↦ hblock P hP

/-- If every selected block satisfies the exact long-interval lower bound,
then their normalized sum is bounded below by the corresponding reciprocal
logarithmic sum. -/
theorem longAverageOverScales_lower_bound
    {weight : ℕ → ℝ} {scales : Finset ℝ} {X x : ℝ}
    (hX : 0 < X)
    (hlong : ∀ P ∈ scales,
      HasLongIntervalMinorantLowerBound weight X P)
    (hxLower : X < x) (hxUpper : x ≤ 2 * X) :
    ∑ P ∈ scales, 1 / (200 * Real.log P * Real.log X) ≤
      weightedPrimeProductAverageOverScales weight scales x
        (X ^ (99 / 100 : ℝ)) := by
  apply sum_block_lower_bounds
  intro P hP
  exact normalized_longAverage_lower_bound hX (hlong P hP) hxLower hxUpper

/-- Replacing each `log P` by a common upper bound `L` gives the expected
factor `card(scales)/L`. -/
theorem reciprocalLogSum_lower_bound
    {scales : Finset ℝ} {X L : ℝ}
    (hlogX : 0 < Real.log X)
    (hscale : ∀ P ∈ scales, 0 < Real.log P ∧ Real.log P ≤ L) :
    (scales.card : ℝ) / (200 * L * Real.log X) ≤
      ∑ P ∈ scales, 1 / (200 * Real.log P * Real.log X) := by
  calc
    (scales.card : ℝ) / (200 * L * Real.log X) =
        ∑ _P ∈ scales, 1 / (200 * L * Real.log X) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ∑ P ∈ scales, 1 / (200 * Real.log P * Real.log X) := by
      apply Finset.sum_le_sum
      intro P hP
      have hdenP : 0 < 200 * Real.log P * Real.log X := by
        exact mul_pos (mul_pos (by norm_num) (hscale P hP).1) hlogX
      have hden :
          200 * Real.log P * Real.log X ≤ 200 * L * Real.log X := by
        gcongr
        exact (hscale P hP).2
      exact one_div_le_one_div_of_le hdenP hden

/-- Abstract form of the cancellation `#blocks ≍ log log X` against
`log P ≍ log log X`: if `γ L ≤ #blocks`, the summed long average has a
fixed multiple of `1/log X` as a lower bound. -/
theorem blockCount_cancels_logScale
    {scales : Finset ℝ} {X L γ : ℝ}
    (hlogX : 0 < Real.log X) (hL : 0 < L)
    (_hγ : 0 ≤ γ)
    (hcard : γ * L ≤ (scales.card : ℝ)) :
    γ / (200 * Real.log X) ≤
      (scales.card : ℝ) / (200 * L * Real.log X) := by
  have hden : 0 < 200 * L * Real.log X := by positivity
  have hrewrite :
      γ / (200 * Real.log X) =
        (γ * L) / (200 * L * Real.log X) := by
    field_simp [ne_of_gt hL, ne_of_gt hlogX]
  rw [hrewrite]
  exact div_le_div_of_nonneg_right hcard hden.le

/-- Complete finite aggregation step used in `(longtotal)`.  The analytic
construction only has to provide the per-block bounds and the two elementary
block-size hypotheses displayed here. -/
theorem longTotal_lower_bound
    {weight : ℕ → ℝ} {scales : Finset ℝ} {X x L γ : ℝ}
    (hXone : 1 < X) (hL : 0 < L) (hγ : 0 ≤ γ)
    (hscale : ∀ P ∈ scales, 0 < Real.log P ∧ Real.log P ≤ L)
    (hcard : γ * L ≤ (scales.card : ℝ))
    (hlong : ∀ P ∈ scales,
      HasLongIntervalMinorantLowerBound weight X P)
    (hxLower : X < x) (hxUpper : x ≤ 2 * X) :
    γ / (200 * Real.log X) ≤
      weightedPrimeProductAverageOverScales weight scales x
        (X ^ (99 / 100 : ℝ)) := by
  have hlogX : 0 < Real.log X := Real.log_pos hXone
  exact (blockCount_cancels_logScale hlogX hL hγ hcard).trans
    ((reciprocalLogSum_lower_bound hlogX hscale).trans
      (longAverageOverScales_lower_bound
        (lt_trans zero_lt_one hXone) hlong hxLower hxUpper))

/-! ## Instantiation for the paper's buffered family -/

/-- The concrete scale family supplies every elementary hypothesis of
`longTotal_lower_bound`.  The remaining hypothesis `hlong` is exactly the
per-block analytic minorant theorem, rather than any hidden counting or
asymptotic assertion. -/
theorem bufferedDyadicScales_longTotal_lower_bound
    {weight : ℕ → ℝ} {c Δ X x : ℝ}
    (hΔ : 0 < Δ)
    (ha : 0 < bufferedPrimeLowerExponent c Δ)
    (hX : Real.exp 1 < X)
    (hsize : 2 ≤
      bufferedDyadicScaleRate Δ * Real.log (Real.log X))
    (hlong : ∀ P ∈ bufferedDyadicScales c Δ X,
      HasLongIntervalMinorantLowerBound weight X P)
    (hxLower : X < x) (hxUpper : x ≤ 2 * X) :
    bufferedDyadicLongTotalConstant c Δ / (200 * Real.log X) ≤
      weightedPrimeProductAverageOverScales weight
        (bufferedDyadicScales c Δ X) x (X ^ (99 / 100 : ℝ)) := by
  have hXone : 1 < X := (Real.one_lt_exp_iff.mpr zero_lt_one).trans hX
  have hrate : 0 < bufferedDyadicScaleRate Δ := by
    rw [bufferedDyadicScaleRate]
    positivity
  have hloglog : 0 < Real.log (Real.log X) := by
    have hproduct :
        0 < bufferedDyadicScaleRate Δ * Real.log (Real.log X) :=
      lt_of_lt_of_le (by norm_num) hsize
    nlinarith
  have hb : 0 < bufferedPrimeUpperExponent c Δ := by
    simp only [bufferedPrimeLowerExponent,
      bufferedPrimeUpperExponent] at ha ⊢
    linarith
  apply longTotal_lower_bound
    (scales := bufferedDyadicScales c Δ X)
    (L := bufferedDyadicCommonLogBound c Δ X)
    (γ := bufferedDyadicLongTotalConstant c Δ)
  · exact hXone
  · exact mul_pos hb hloglog
  · exact le_of_lt (div_pos hrate (mul_pos (by norm_num) hb))
  · intro P hP
    simpa only [bufferedDyadicCommonLogBound] using
      bufferedDyadicScales_log_bound hΔ ha hX hsize hP
  · have hcount := bufferedDyadicScales_card_lower
      (c := c) hX hsize
    calc
      bufferedDyadicLongTotalConstant c Δ *
          bufferedDyadicCommonLogBound c Δ X =
          (bufferedDyadicScaleRate Δ / 2) *
            Real.log (Real.log X) := by
        rw [bufferedDyadicLongTotalConstant,
          bufferedDyadicCommonLogBound]
        field_simp [ne_of_gt hb]
      _ ≤ ((bufferedDyadicScales c Δ X).card : ℝ) := hcount
  · exact hlong
  · exact hxLower
  · exact hxUpper

/-- Fully quantified "for sufficiently large `X`" form.  For fixed
`c,Δ`, all geometry and counting of the buffered family is eventually
automatic; only the already isolated per-block minorant bounds remain to be
provided. -/
theorem eventually_bufferedDyadicScales_longTotal_lower_bound
    {c Δ : ℝ} (hΔ : 0 < Δ)
    (ha : 0 < bufferedPrimeLowerExponent c Δ) :
    ∀ᶠ X : ℝ in atTop, ∀ (weight : ℕ → ℝ) (x : ℝ),
      (∀ P ∈ bufferedDyadicScales c Δ X,
        HasLongIntervalMinorantLowerBound weight X P) →
      X < x → x ≤ 2 * X →
      bufferedDyadicLongTotalConstant c Δ / (200 * Real.log X) ≤
        weightedPrimeProductAverageOverScales weight
          (bufferedDyadicScales c Δ X) x
            (X ^ (99 / 100 : ℝ)) := by
  filter_upwards [eventually_bufferedDyadicScale_size hΔ] with X hX
  intro weight x hlong hxLower hxUpper
  exact bufferedDyadicScales_longTotal_lower_bound
    hΔ ha hX.1 hX.2 hlong hxLower hxUpper

/-! ## The exact MT23 theorem on the buffered family -/

/-- Per-scale form of the printed long-interval theorem on the explicit
buffered family.  The two elementary size hypotheses are displayed here so
that the statement is a direct, audit-friendly composition of the cited
theorem and `bufferedDyadicExponent_mem_printed_window`. -/
theorem printedLongIntervalMinorant_on_bufferedDyadicScales
    (hprinted : PrintedLongIntervalMinorantLowerBoundStatement) :
    ∃ εₘₐₓ : ℝ, 0 < εₘₐₓ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
        ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 7500 →
          ∃ X₀ : ℝ, 3 ≤ X₀ ∧
            ∀ X : ℝ, X₀ ≤ X →
              Real.exp 1 < X →
              2 ≤ bufferedDyadicScaleRate Δ *
                Real.log (Real.log X) →
              ∀ P ∈ bufferedDyadicScales (21 / 10 : ℝ) Δ X,
                HasLongIntervalMinorantLowerBound
                  (matomakiTeravainenMinorant X ε) X P := by
  obtain ⟨εₘₐₓ, hεₘₐₓ, hprinted⟩ := hprinted
  refine ⟨εₘₐₓ, hεₘₐₓ, ?_⟩
  intro ε hε hεUpper Δ hΔ hΔUpper
  obtain ⟨X₀, hX₀, hprinted⟩ := hprinted ε hε hεUpper
  refine ⟨X₀, hX₀, ?_⟩
  intro X hXsource hX hsize P hP
  have ha := bufferedDyadicExponent_mem_printed_window
    hΔ hΔUpper hX hsize hP
  have hscale := bufferedDyadicScale_eq_log_rpow_exponent
    hΔ hX hsize hP
  have hlong := hprinted X hXsource
    (bufferedDyadicExponent X P) ha.1 ha.2
  rw [hscale] at hlong
  exact hlong

/-- Fully aggregated endpoint statement obtained from the exact printed
[MT23, Theorem 2.1(ii)].  It has no remaining per-block analytic premise:
for every fixed `0 < Δ ≤ 1/7500`, all sufficiently large `X` satisfy a
positive `1/log X` lower bound after summing the buffered dyadic blocks. -/
def PrintedBufferedDyadicLongTotalStatement : Prop :=
  ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 7500 →
    ∃ εₘₐₓ : ℝ, 0 < εₘₐₓ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
        ∃ X₀ : ℝ, 3 ≤ X₀ ∧
          ∀ X : ℝ, X₀ ≤ X →
            ∀ x : ℝ, X < x → x ≤ 2 * X →
              bufferedDyadicLongTotalConstant (21 / 10 : ℝ) Δ /
                  (200 * Real.log X) ≤
                weightedPrimeProductAverageOverScales
                  (matomakiTeravainenMinorant X ε)
                  (bufferedDyadicScales (21 / 10 : ℝ) Δ X) x
                  (X ^ (99 / 100 : ℝ))

/-- The exact printed one-block result implies the complete finite dyadic
long-total statement.  All extra work is elementary: logarithmic
reparametrization, window arithmetic, counting, and increasing the starting
height to make the buffered family nonempty and correctly placed. -/
theorem printedBufferedDyadicLongTotal_of_printedLongIntervalMinorant
    (hprinted : PrintedLongIntervalMinorantLowerBoundStatement) :
    PrintedBufferedDyadicLongTotalStatement := by
  intro Δ hΔ hΔUpper
  obtain ⟨εₘₐₓ, hεₘₐₓ, hblocks⟩ :=
    printedLongIntervalMinorant_on_bufferedDyadicScales hprinted
  refine ⟨εₘₐₓ, hεₘₐₓ, ?_⟩
  intro ε hε hεUpper
  obtain ⟨Xsource, hXsource, hblocks⟩ :=
    hblocks ε hε hεUpper Δ hΔ hΔUpper
  obtain ⟨Xgeometry, hgeometry⟩ := Filter.eventually_atTop.1
    (eventually_bufferedDyadicScale_size hΔ)
  refine ⟨max Xsource Xgeometry, le_max_of_le_left hXsource, ?_⟩
  intro X hX x hxLower hxUpper
  have hXsource' : Xsource ≤ X := (le_max_left _ _).trans hX
  have hXgeometry' : Xgeometry ≤ X := (le_max_right _ _).trans hX
  have hgeom := hgeometry X hXgeometry'
  have ha : 0 < bufferedPrimeLowerExponent (21 / 10 : ℝ) Δ := by
    dsimp only [bufferedPrimeLowerExponent]
    norm_num at hΔUpper ⊢
    linarith
  exact bufferedDyadicScales_longTotal_lower_bound
    hΔ ha hgeom.1 hgeom.2
    (hblocks X hXsource' hgeom.1 hgeom.2) hxLower hxUpper

/-- End-to-end citation-facing version of the dyadic long-total theorem. -/
theorem printedBufferedDyadicLongTotal_of_matomakiTeravainenTheoremTwoOnePartTwo
    (hsource : MatomakiTeravainenTheoremTwoOnePartTwoStatement) :
    PrintedBufferedDyadicLongTotalStatement :=
  printedBufferedDyadicLongTotal_of_printedLongIntervalMinorant
    (printedLongIntervalMinorantLowerBound_of_matomakiTeravainenTheoremTwoOnePartTwo
      hsource)

def dyadicPrimeBlocksModule : ProofModule :=
  { name := "Completion.DyadicPrimeBlocks"
    paperLocation := "Section 7.2, construction of P_Δ(X) and the long total"
    purpose :=
      "Construct and count an explicit buffered dyadic-scale family, identify every scale with a power in the exact MT23 parameter window, and derive the summed long lower bound from the cited endpoint theorem."
    dependsOn :=
      ["Completion.LongIntervalMinorant"]
    status := .proved }

end

end Completion
end ExactSemiprimes
