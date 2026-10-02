import ExactSemiprimes.Completion.VarianceBlockSummation

/-! # From variance to an almost-all lower bound -/

namespace ExactSemiprimes
namespace Completion

/-- Finite Markov--Chebyshev inequality.  This is the counting version used
after the variance integral has been discretized. -/
theorem card_filter_le_sum_div {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    {threshold : ℝ} (hthreshold : 0 < threshold)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    ((s.filter fun i ↦ threshold ≤ f i).card : ℝ) ≤
      (∑ i ∈ s, f i) / threshold := by
  let bad := s.filter fun i ↦ threshold ≤ f i
  have hpoint : ∀ i ∈ bad, threshold ≤ f i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hbad : (bad.card : ℝ) * threshold ≤ ∑ i ∈ bad, f i := by
    calc
      (bad.card : ℝ) * threshold = ∑ _i ∈ bad, threshold := by
        simp [mul_comm]
      _ ≤ ∑ i ∈ bad, f i := Finset.sum_le_sum hpoint
  have hsubset : bad ⊆ s := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have htotal : ∑ i ∈ bad, f i ≤ ∑ i ∈ s, f i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun i hi _ ↦ hf i hi
  rw [le_div_iff₀ hthreshold]
  exact hbad.trans htotal

/-- Chebyshev's inequality written for a real-valued deviation and a
positive absolute threshold. -/
theorem card_abs_deviation_le_sum_sq_div {ι : Type*}
    (s : Finset ι) (g : ι → ℝ) {threshold : ℝ}
    (hthreshold : 0 < threshold) :
    ((s.filter fun i ↦ threshold ≤ |g i|).card : ℝ) ≤
      (∑ i ∈ s, (g i) ^ 2) / threshold ^ 2 := by
  have hmarkov := card_filter_le_sum_div s (fun i ↦ (g i) ^ 2)
    (sq_pos_of_pos hthreshold) (fun i _ ↦ sq_nonneg (g i))
  have hfilters :
      s.filter (fun i ↦ threshold ≤ |g i|) =
        s.filter (fun i ↦ threshold ^ 2 ≤ (g i) ^ 2) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, hdev⟩
      refine ⟨hi, ?_⟩
      have hsquare :=
        (sq_le_sq₀ hthreshold.le (abs_nonneg (g i))).2 hdev
      simpa [sq_abs] using hsquare
    · rintro ⟨hi, hsquare⟩
      refine ⟨hi, ?_⟩
      apply (sq_le_sq₀ hthreshold.le (abs_nonneg (g i))).1
      simpa [sq_abs] using hsquare
  rw [hfilters]
  exact hmarkov

/-- Paper-specific finite core of the variance-to-lower-bound passage.  If
the long average is at least `target`, then every point where the short
average is below `target/2` has deviation at least `target/2`. -/
theorem card_short_below_half_long_le_variance {ι : Type*}
    (s : Finset ι) (short long : ι → ℝ) {target : ℝ}
    (htarget : 0 < target)
    (hlong : ∀ i ∈ s, target ≤ long i) :
    ((s.filter fun i ↦ short i < target / 2).card : ℝ) ≤
      (∑ i ∈ s, (short i - long i) ^ 2) / (target / 2) ^ 2 := by
  let bad := s.filter fun i ↦ short i < target / 2
  let dev := s.filter fun i ↦ target / 2 ≤ |short i - long i|
  have hsubset : bad ⊆ dev := by
    intro i hi
    have hi := Finset.mem_filter.mp hi
    have hlongi := hlong i hi.1
    have hnonpos : short i - long i ≤ 0 := by linarith
    rw [Finset.mem_filter]
    refine ⟨hi.1, ?_⟩
    rw [abs_of_nonpos hnonpos]
    linarith
  have hcard : (bad.card : ℝ) ≤ (dev.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hcheb := card_abs_deviation_le_sum_sq_div s
    (fun i ↦ short i - long i) (show 0 < target / 2 by positivity)
  exact hcard.trans hcheb

/-- Equivalent version displaying the familiar factor four. -/
theorem card_short_below_half_long_le_four_mul_variance {ι : Type*}
    (s : Finset ι) (short long : ι → ℝ) {target : ℝ}
    (htarget : 0 < target)
    (hlong : ∀ i ∈ s, target ≤ long i) :
    ((s.filter fun i ↦ short i < target / 2).card : ℝ) ≤
      4 * (∑ i ∈ s, (short i - long i) ^ 2) / target ^ 2 := by
  calc
    ((s.filter fun i ↦ short i < target / 2).card : ℝ)
        ≤ (∑ i ∈ s, (short i - long i) ^ 2) / (target / 2) ^ 2 :=
      card_short_below_half_long_le_variance s short long htarget hlong
    _ = 4 * (∑ i ∈ s, (short i - long i) ^ 2) / target ^ 2 := by
      field_simp [ne_of_gt htarget]
      ring

/-! ## Paper-specific logarithmic-power substitution -/

/-- Exact cancellation of the two logarithmic powers lost when the target
size is `gamma / L`.  A variance saving `L^(-(2 + epsilon₀))` therefore
leaves the exceptional-count saving `L^(-epsilon₀)`. -/
theorem four_mul_logVariance_div_logTarget_sq
    {X L gamma C epsilon₀ : ℝ}
    (hL : 0 < L) (hgamma : 0 < gamma) :
    4 * (C * X / L ^ (2 + epsilon₀)) / (gamma / L) ^ 2 =
      (4 * C / gamma ^ 2) * X / L ^ epsilon₀ := by
  have hLne : L ≠ 0 := ne_of_gt hL
  have hgammaNe : gamma ≠ 0 := ne_of_gt hgamma
  have hLpowNe : L ^ epsilon₀ ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hL _)
  have hsplit : L ^ (2 + epsilon₀) = L ^ 2 * L ^ epsilon₀ := by
    rw [Real.rpow_add hL, Real.rpow_two]
  rw [hsplit]
  field_simp [hLne, hgammaNe, hLpowNe]

/-- Finite version of the paper's final Chebyshev substitution.

If the squared deviation is at most
`C * X / L^(2 + epsilon₀)` and the long average is at least `gamma/L`,
then the number of points where the short average is below half that target
is at most `(4C/gamma²) * X / L^epsilon₀`.  Thus the two powers of `L`
from the Chebyshev denominator are accounted for exactly, with no hidden
constant or exponent loss. -/
theorem card_short_below_logTarget_le_logPower
    {ι : Type*} (s : Finset ι) (short long : ι → ℝ)
    {X L gamma C epsilon₀ : ℝ}
    (hX : 0 ≤ X) (hL : 0 < L) (hgamma : 0 < gamma)
    (hC : 0 ≤ C)
    (hlong : ∀ i ∈ s, gamma / L ≤ long i)
    (hvariance :
      ∑ i ∈ s, (short i - long i) ^ 2 ≤
        C * X / L ^ (2 + epsilon₀)) :
    ((s.filter fun i ↦ short i < (gamma / L) / 2).card : ℝ) ≤
      (4 * C / gamma ^ 2) * X / L ^ epsilon₀ := by
  have htarget : 0 < gamma / L := div_pos hgamma hL
  have hvarianceUpperNonneg : 0 ≤ C * X / L ^ (2 + epsilon₀) := by
    exact div_nonneg (mul_nonneg hC hX)
      (Real.rpow_nonneg hL.le _)
  have hchebyshev :=
    card_short_below_half_long_le_four_mul_variance
      s short long htarget hlong
  calc
    ((s.filter fun i ↦ short i < (gamma / L) / 2).card : ℝ)
        ≤ 4 * (∑ i ∈ s, (short i - long i) ^ 2) /
            (gamma / L) ^ 2 := hchebyshev
    _ ≤ 4 * (C * X / L ^ (2 + epsilon₀)) / (gamma / L) ^ 2 := by
      have hfour :
          4 * (∑ i ∈ s, (short i - long i) ^ 2) ≤
            4 * (C * X / L ^ (2 + epsilon₀)) :=
        mul_le_mul_of_nonneg_left hvariance (by norm_num)
      exact div_le_div_of_nonneg_right hfour (sq_nonneg (gamma / L))
    _ = (4 * C / gamma ^ 2) * X / L ^ epsilon₀ :=
      four_mul_logVariance_div_logTarget_sq hL hgamma

/-- Explicit-constant specialization with `L = log X`.  The hypothesis
`1 < X` supplies exactly the positivity needed for the logarithmic target
and denominators. -/
theorem card_short_below_logXTarget_le_logPower
    {ι : Type*} (s : Finset ι) (short long : ι → ℝ)
    {X gamma C epsilon₀ : ℝ}
    (hX : 1 < X) (hgamma : 0 < gamma) (hC : 0 ≤ C)
    (_hepsilon₀ : 0 < epsilon₀)
    (hlong : ∀ i ∈ s, gamma / Real.log X ≤ long i)
    (hvariance :
      ∑ i ∈ s, (short i - long i) ^ 2 ≤
        C * X / (Real.log X) ^ (2 + epsilon₀)) :
    ((s.filter fun i ↦
      short i < (gamma / Real.log X) / 2).card : ℝ) ≤
      (4 * C / gamma ^ 2) * X / (Real.log X) ^ epsilon₀ := by
  apply card_short_below_logTarget_le_logPower
    (X := X) (L := Real.log X) (gamma := gamma)
    (C := C) (epsilon₀ := epsilon₀)
  · exact (zero_lt_one.trans hX).le
  · exact Real.log_pos hX
  · exact hgamma
  · exact hC
  · exact hlong
  · exact hvariance

def chebyshevPassageModule : ProofModule :=
  { name := "Completion.ChebyshevPassage"
    paperLocation := "Section 7.2, variance plus long total"
    purpose :=
      "Complete the finite variance-to-exceptional-count passage, including the exact loss of two logarithmic powers for target gamma/log X."
    dependsOn :=
      [ "Completion.VarianceBlockSummation",
        "Completion.DyadicPrimeBlocks",
        "Mathlib Chebyshev/Markov inequality" ]
    status := .proved }

end Completion
end ExactSemiprimes
