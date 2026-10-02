import ExactSemiprimes.TypeII.ExtremeLargeAbsorption

/-!
# Weighted assembly of the extreme-large Type-II range

This module closes the bridge from the proved cardinality estimate for
`R₁` to the weighted discrete contribution needed in Proposition 5.1.  The
polylogarithmic coefficient energy is derived from the cited integer moments
of the divisor function; no paper-specific analytic estimate is assumed.
-/

namespace ExactSemiprimes
namespace TypeII

open Filter
open scoped BigOperators

noncomputable section

/-! ## The exponent calculation in the Halasz--Montgomery term -/

/-- The exponent margin behind the `R₁` weighted estimate.  The concrete
smallness condition is exactly

`50 eps + 1/2 ≤ 9/11 - 2 eps`.

Thus the cardinality loss and the square-root loss together are swallowed
by the lower bound for the second polynomial length. -/
theorem extreme_cardinality_rpow_mul_sqrt_le_secondLength
    {T M₂ eps : ℝ} (hT : 1 ≤ T)
    (hepsSmall : eps ≤ 7 / 1144)
    (hM₂lower : T ^ (9 / 11 - 2 * eps) ≤ M₂) :
    T ^ (50 * eps) * T ^ (1 / 2 : ℝ) ≤ M₂ := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hexponent : 50 * eps + 1 / 2 ≤ 9 / 11 - 2 * eps := by
    norm_num at hepsSmall ⊢
    linarith
  calc
    T ^ (50 * eps) * T ^ (1 / 2 : ℝ) =
        T ^ (50 * eps + 1 / 2) := by
      rw [Real.rpow_add hTpos]
    _ ≤ T ^ (9 / 11 - 2 * eps) :=
      Real.rpow_le_rpow_of_exponent_le hT hexponent
    _ ≤ M₂ := hM₂lower

/-- In the paper-shaped Halasz--Montgomery factor, the already proved
`#R₁ ≤ 2 T^(50 eps)` estimate makes the variable cardinality term at most
`2`. -/
theorem extreme_cardinality_term_le_two
    {R₁ : Finset ℝ} {T M₂ eps : ℝ}
    (hT : 1 ≤ T)
    (hepsSmall : eps ≤ 7 / 1144)
    (hM₂lower : T ^ (9 / 11 - 2 * eps) ≤ M₂)
    (hcard : (R₁.card : ℝ) ≤ 2 * T ^ (50 * eps)) :
    (R₁.card : ℝ) * T ^ (1 / 2 : ℝ) / M₂ ≤ 2 := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hM₂pos : 0 < M₂ :=
    (Real.rpow_pos_of_pos hTpos _).trans_le hM₂lower
  have hrpow := extreme_cardinality_rpow_mul_sqrt_le_secondLength
    hT hepsSmall hM₂lower
  have hmul :
      (R₁.card : ℝ) * T ^ (1 / 2 : ℝ) ≤ 2 * M₂ := by
    calc
      (R₁.card : ℝ) * T ^ (1 / 2 : ℝ) ≤
          (2 * T ^ (50 * eps)) * T ^ (1 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hTpos.le _)
      _ = 2 * (T ^ (50 * eps) * T ^ (1 / 2 : ℝ)) := by ring
      _ ≤ 2 * M₂ := mul_le_mul_of_nonneg_left hrpow (by norm_num)
  exact (div_le_iff₀ hM₂pos).2 (by simpa using hmul)

/-! ## Weighted insertion -/

/-- Halasz--Montgomery plus a cardinality factor at most `2` turns an
energy estimate `energy ≤ E/M` into a weighted product bound.  This lemma
contains no divisor estimate: `E` is exposed so that the exact remaining
number-theoretic input is visible. -/
theorem weightedProduct_meanSquare_le_of_energy_and_cardinalityTerm
    (inputs : ExternalInputs) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M T E S : ℝ) (beta : ℕ → ℂ) (A : ℝ → ℂ)
          (R : Finset ℝ),
        1 ≤ M → 1 ≤ T → 0 ≤ E → 0 ≤ S →
        halaszMontgomeryDyadicEnergy beta M ≤ E / M →
        (R.card : ℝ) * T ^ (1 / 2 : ℝ) / M ≤ 2 →
        (∀ t ∈ R, ‖A t‖ ^ (2 : ℕ) ≤ S) →
        (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
        IsOneSpaced (↑R : Set ℝ) →
        (∑ t ∈ R,
            ‖A t * dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^
              (2 : ℕ)) ≤
          4 * C * Real.log (2 * T) * E * S := by
  obtain ⟨C, hC, hmean⟩ :=
    dyadicLineOne_meanSquare_le_of_iwaniecKowalskiNineSix inputs
  refine ⟨C, hC, ?_⟩
  intro M T E S beta A R hM hT hE hS henergy hcardTerm hA hR hspaced
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hlog : 0 ≤ Real.log (2 * T) := by
    exact Real.log_nonneg (by linarith)
  have hlength :
      2 * M + (R.card : ℝ) * T ^ (1 / 2 : ℝ) ≤ 4 * M := by
    have hvariable :
        (R.card : ℝ) * T ^ (1 / 2 : ℝ) ≤ 2 * M :=
      (div_le_iff₀ hMpos).mp hcardTerm
    linarith
  have hbase := hmean M T beta R hM hT hR hspaced
  have henergyNonneg : 0 ≤ halaszMontgomeryDyadicEnergy beta M := by
    unfold halaszMontgomeryDyadicEnergy
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hmeanE :
      (∑ t ∈ R,
          ‖dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^ (2 : ℕ)) ≤
        4 * C * Real.log (2 * T) * E := by
    calc
      (∑ t ∈ R,
          ‖dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^ (2 : ℕ)) ≤
          C * (2 * M + (R.card : ℝ) * T ^ (1 / 2 : ℝ)) *
            Real.log (2 * T) * halaszMontgomeryDyadicEnergy beta M := hbase
      _ ≤ C * (4 * M) * Real.log (2 * T) * (E / M) := by
        gcongr
      _ = 4 * C * Real.log (2 * T) * E := by
        field_simp
  calc
    (∑ t ∈ R,
        ‖A t * dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^ (2 : ℕ)) =
        ∑ t ∈ R, ‖A t‖ ^ (2 : ℕ) *
          ‖dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^ (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [norm_mul, mul_pow]
    _ ≤ ∑ t ∈ R, S *
          ‖dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_right (hA t ht) (sq_nonneg _)
    _ = S * (∑ t ∈ R,
          ‖dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^ (2 : ℕ)) := by
      rw [Finset.mul_sum]
    _ ≤ S * (4 * C * Real.log (2 * T) * E) :=
      mul_le_mul_of_nonneg_left hmeanE hS
    _ = 4 * C * Real.log (2 * T) * E * S := by ring

/-- For `T ≥ 2`, replacing `log(2T)` by `2 log T` costs only an
absolute factor. -/
theorem log_two_mul_le_two_mul_log {T : ℝ} (hT : 2 ≤ T) :
    Real.log (2 * T) ≤ 2 * Real.log T := by
  have hTpos : 0 < T := by linarith
  have hlogTwoLe : Real.log 2 ≤ Real.log T := by
    exact Real.log_le_log (by norm_num) hT
  rw [Real.log_mul (by norm_num) hTpos.ne']
  linarith

/-- Polylogarithmic dyadic energy gives precisely the polylogarithmic
weighted contribution required by Proposition 5.1.  This is the form into
which a fixed-power divisor-moment estimate plugs directly. -/
theorem weightedProduct_meanSquare_le_of_polylog_energy
    (inputs : ExternalInputs) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M T D S : ℝ) (Q : ℕ) (beta : ℕ → ℂ) (A : ℝ → ℂ)
          (R : Finset ℝ),
        1 ≤ M → 2 ≤ T → 0 ≤ D → 0 ≤ S →
        halaszMontgomeryDyadicEnergy beta M ≤
          D * (Real.log T) ^ Q / M →
        (R.card : ℝ) * T ^ (1 / 2 : ℝ) / M ≤ 2 →
        (∀ t ∈ R, ‖A t‖ ^ (2 : ℕ) ≤ S) →
        (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
        IsOneSpaced (↑R : Set ℝ) →
        (∑ t ∈ R,
            ‖A t * dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^
              (2 : ℕ)) ≤
          8 * C * D * (Real.log T) ^ (Q + 1) * S := by
  obtain ⟨C, hC, hweighted⟩ :=
    weightedProduct_meanSquare_le_of_energy_and_cardinalityTerm inputs
  refine ⟨C, hC, ?_⟩
  intro M T D S Q beta A R hM hT hD hS henergy hcard hA hR hspaced
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hE : 0 ≤ D * (Real.log T) ^ Q :=
    mul_nonneg hD (pow_nonneg hlogT Q)
  have hbound := hweighted M T (D * (Real.log T) ^ Q) S beta A R
    hM (by linarith) hE hS henergy hcard hA hR hspaced
  calc
    (∑ t ∈ R,
        ‖A t * dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^
          (2 : ℕ)) ≤
        4 * C * Real.log (2 * T) * (D * (Real.log T) ^ Q) * S := hbound
    _ ≤ 4 * C * (2 * Real.log T) * (D * (Real.log T) ^ Q) * S := by
      gcongr
      exact log_two_mul_le_two_mul_log hT
    _ = 8 * C * D * (Real.log T) ^ (Q + 1) * S := by
      rw [pow_succ]
      ring


/-! ## Source-derived divisor-moment energy -/

theorem divisorMoment_upper_of_lucaToth
    (hLT : LucaTothTheoremOneStatement) (r : ℕ) (hr : 2 ≤ r) :
    ∃ C x₀ : ℝ, 0 < C ∧ 2 ≤ x₀ ∧
      ∀ x : ℝ, x₀ ≤ x →
        (∑ n ∈ natOpenClosedInterval 0 x,
          (divisorCount n : ℝ) ^ r) ≤
            C * x * (Real.log x) ^ (2 ^ r - 1) := by
  obtain ⟨Cᵣ, E, x₀, hCᵣ, hE, hx₀, hasymp⟩ := hLT r hr
  let X₀ := max x₀ (Real.exp 1)
  refine ⟨Cᵣ + E, X₀, add_pos hCᵣ hE,
    hx₀.trans (le_max_left x₀ (Real.exp 1)), ?_⟩
  intro x hx
  have hx₀x : x₀ ≤ x := (le_max_left x₀ (Real.exp 1)).trans hx
  have hexpx : Real.exp 1 ≤ x :=
    (le_max_right x₀ (Real.exp 1)).trans hx
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hexpx
  have hlogOne : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hexpx
    simpa using this
  let S : ℝ := ∑ n ∈ natOpenClosedInterval 0 x,
    (divisorCount n : ℝ) ^ r
  have hrem := hasymp x hx₀x
  have hsum :
      S ≤ x * Cᵣ * (Real.log x) ^ (2 ^ r - 1) +
        E * x * (Real.log x) ^ (2 ^ r - 2) := by
    have hdiff := (le_abs_self
      (S - x * Cᵣ * (Real.log x) ^ (2 ^ r - 1))).trans hrem
    linarith
  have hpow :
      (Real.log x) ^ (2 ^ r - 2) ≤
        (Real.log x) ^ (2 ^ r - 1) :=
    pow_le_pow_right₀ hlogOne (by omega)
  dsimp [S] at hsum ⊢
  calc
    (∑ n ∈ natOpenClosedInterval 0 x,
        (divisorCount n : ℝ) ^ r) ≤
        x * Cᵣ * (Real.log x) ^ (2 ^ r - 1) +
          E * x * (Real.log x) ^ (2 ^ r - 2) := hsum
    _ ≤ x * Cᵣ * (Real.log x) ^ (2 ^ r - 1) +
          E * x * (Real.log x) ^ (2 ^ r - 1) := by
      gcongr
    _ = (Cᵣ + E) * x * (Real.log x) ^ (2 ^ r - 1) := by ring

/-- Positivity supplies the elementary lower bound `1 ≤ d(n)` used to
raise a real divisor exponent to a fixed integer moment. -/
theorem one_le_divisorCount_real {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) ≤ (divisorCount n : ℝ) := by
  have hone : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hn.ne'
  have hcard : 1 ≤ n.divisors.card := Finset.one_le_card.mpr ⟨1, hone⟩
  exact_mod_cast hcard

/-- A source-faithful integer divisor moment implies the precise real-`B`
dyadic coefficient-energy estimate required by the weighted `R₁` bridge.
The integer moment is chosen as `max 2 ⌈2B⌉`; hence no real moment is
placed in the external trust boundary. -/
theorem dyadicEnergy_polylog_of_lucaToth
    (hLT : LucaTothTheoremOneStatement) {B A₀ : ℝ}
    (_hB : 0 ≤ B) (hA₀ : 1 ≤ A₀) :
    ∃ (D M₀ : ℝ) (Q : ℕ),
      0 < D ∧ 2 ≤ M₀ ∧
      ∀ (a : ℕ → ℂ) (M T : ℝ),
        M₀ ≤ M → M ≤ T →
        IsDivisorBoundedByConstant B A₀ a →
        halaszMontgomeryDyadicEnergy a M ≤
          D * (Real.log T) ^ Q / M := by
  let r : ℕ := max 2 ⌈2 * B⌉₊
  have hr : 2 ≤ r := le_max_left _ _
  have hBr : 2 * B ≤ (r : ℝ) := by
    calc
      2 * B ≤ (⌈2 * B⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (r : ℝ) := by exact_mod_cast le_max_right 2 ⌈2 * B⌉₊
  obtain ⟨C, x₀, hC, hx₀, hmoment⟩ :=
    divisorMoment_upper_of_lucaToth hLT r hr
  let Q : ℕ := 2 ^ r - 1
  let D : ℝ := 2 * A₀ ^ (2 : ℕ) * C * (2 : ℝ) ^ Q
  let M₀ : ℝ := max 2 x₀
  have hA₀pos : 0 < A₀ := zero_lt_one.trans_le hA₀
  have hD : 0 < D := by
    dsimp [D]
    positivity
  refine ⟨D, M₀, Q, hD, le_max_left 2 x₀, ?_⟩
  intro a M T hM₀ hMT ha
  have hMtwo : 2 ≤ M := (le_max_left 2 x₀).trans hM₀
  have hx₀M : x₀ ≤ M := (le_max_right 2 x₀).trans hM₀
  have hMpos : 0 < M := by linarith
  have hTtwo : 2 ≤ T := hMtwo.trans hMT
  have hTpos : 0 < T := by linarith
  have htwoMthreshold : x₀ ≤ 2 * M := by linarith
  have hmomentTwo := hmoment (2 * M) htwoMthreshold
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlogCompare : Real.log (2 * M) ≤ 2 * Real.log T := by
    calc
      Real.log (2 * M) ≤ Real.log (2 * T) := by
        exact Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left hMT (by norm_num))
      _ ≤ 2 * Real.log T := log_two_mul_le_two_mul_log hTtwo
  have hpowLog :
      (Real.log (2 * M)) ^ Q ≤
        (2 : ℝ) ^ Q * (Real.log T) ^ Q := by
    calc
      (Real.log (2 * M)) ^ Q ≤ (2 * Real.log T) ^ Q := by
        exact pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlogCompare Q
      _ = (2 : ℝ) ^ Q * (Real.log T) ^ Q := mul_pow 2 (Real.log T) Q
  have hterm : ∀ n ∈ dyadicInterval M,
      ‖a n / (n : ℂ)‖ ^ (2 : ℕ) ≤
        A₀ ^ (2 : ℕ) * (divisorCount n : ℝ) ^ r / M ^ (2 : ℕ) := by
    intro n hn
    have hnrange := (mem_dyadicInterval hMpos.le).mp hn
    have hnposReal : 0 < (n : ℝ) := hMpos.trans hnrange.1
    have hnpos : 0 < n := by exact_mod_cast hnposReal
    have hdOne : (1 : ℝ) ≤ (divisorCount n : ℝ) :=
      one_le_divisorCount_real hnpos
    have hcoeff := ha.2.2 n hnpos
    have hcoeffSq :
        ‖a n‖ ^ (2 : ℕ) ≤
          A₀ ^ (2 : ℕ) * (divisorCount n : ℝ) ^ r := by
      calc
        ‖a n‖ ^ (2 : ℕ) ≤
            (A₀ * (divisorCount n : ℝ) ^ B) ^ (2 : ℕ) :=
          pow_le_pow_left₀ (norm_nonneg _) hcoeff 2
        _ = A₀ ^ (2 : ℕ) * (divisorCount n : ℝ) ^ (2 * B) := by
          have hpower :
              ((divisorCount n : ℝ) ^ B) ^ (2 : ℕ) =
                (divisorCount n : ℝ) ^ (2 * B) := by
            rw [← Real.rpow_natCast,
              ← Real.rpow_mul (zero_le_one.trans hdOne)]
            congr 1
            push_cast
            ring
          rw [mul_pow, hpower]
        _ ≤ A₀ ^ (2 : ℕ) * (divisorCount n : ℝ) ^ (r : ℝ) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hdOne hBr) (sq_nonneg A₀)
        _ = A₀ ^ (2 : ℕ) * (divisorCount n : ℝ) ^ r := by
          rw [Real.rpow_natCast]
    rw [norm_div, Complex.norm_natCast, div_pow]
    exact div_le_div₀ (by positivity) hcoeffSq (by positivity)
      (pow_le_pow_left₀ hMpos.le hnrange.1.le 2)
  have hsubset : dyadicInterval M ⊆ natOpenClosedInterval 0 (2 * M) :=
    dyadicInterval_subset_initial_two_mul hMpos.le
  have hsumSubset :
      (∑ n ∈ dyadicInterval M, (divisorCount n : ℝ) ^ r) ≤
        ∑ n ∈ natOpenClosedInterval 0 (2 * M),
          (divisorCount n : ℝ) ^ r := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ ↦ by positivity)
  rw [halaszMontgomeryDyadicEnergy]
  calc
    (∑ n ∈ dyadicInterval M, ‖a n / (n : ℂ)‖ ^ (2 : ℕ)) ≤
        ∑ n ∈ dyadicInterval M,
          A₀ ^ (2 : ℕ) * (divisorCount n : ℝ) ^ r /
            M ^ (2 : ℕ) := by
      exact Finset.sum_le_sum hterm
    _ = (A₀ ^ (2 : ℕ) / M ^ (2 : ℕ)) *
          ∑ n ∈ dyadicInterval M, (divisorCount n : ℝ) ^ r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      field_simp
    _ ≤ (A₀ ^ (2 : ℕ) / M ^ (2 : ℕ)) *
          ∑ n ∈ natOpenClosedInterval 0 (2 * M),
            (divisorCount n : ℝ) ^ r := by
      exact mul_le_mul_of_nonneg_left hsumSubset (by positivity)
    _ ≤ (A₀ ^ (2 : ℕ) / M ^ (2 : ℕ)) *
          (C * (2 * M) * (Real.log (2 * M)) ^ Q) := by
      exact mul_le_mul_of_nonneg_left (by simpa [Q] using hmomentTwo)
        (by positivity)
    _ ≤ (A₀ ^ (2 : ℕ) / M ^ (2 : ℕ)) *
          (C * (2 * M) * ((2 : ℝ) ^ Q * (Real.log T) ^ Q)) := by
      gcongr
    _ = D * (Real.log T) ^ Q / M := by
      dsimp [D]
      field_simp

/-! ## Source-closed weighted endpoint on `extremePairPoints` -/

/-- The complete weighted `R₁` endpoint, stated directly on the finite set
controlled by `ExtremeLargeAbsorption`.  It uses only the three named source
inputs IK04 Theorems 9.4 and 9.6 and Luca--Tóth Theorem 1.  In particular,
there is no dependency on `TypeIIEstimate`, so this theorem can live
upstream of the final deterministic partition without creating an import
cycle.

The constant `C` is the absolute IK9.6 constant.  For fixed displayed
coefficient data `B,A₀`, Luca--Tóth supplies `D,Q`; the eventual height
threshold may depend on all fixed parameters but is chosen before the
coefficients, lengths, finite set, and pointwise bound `S`. -/
theorem eventually_weighted_extremePairPoints_le_polylog
    (inputs : ExternalInputs) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B eps : ℝ) (K : ℕ),
        0 ≤ B → 0 < eps → eps ≤ 7 / 1144 → 1 ≤ K →
        ∀ A₀ : ℝ, 1 ≤ A₀ →
          ∃ (D : ℝ) (Q : ℕ), 0 < D ∧
            ∀ᶠ T : ℝ in atTop,
              ∀ (a₁ a₂ : ℕ → ℂ) (M₁ M₂ : ℝ) (R : Finset ℝ)
                  (S : ℝ),
                1 < M₁ → M₁ ≤ T →
                1 < M₂ → M₂ ≤ T →
                T ^ (9 / 11 - 2 * eps) ≤ M₂ →
                extremePowerExponent T M₁ ≤ K →
                extremePowerExponent T M₂ ≤ K →
                IsDivisorBoundedByConstant B A₀ a₁ →
                IsDivisorBoundedByConstant B A₀ a₂ →
                (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
                IsOneSpaced (↑R : Set ℝ) →
                0 ≤ S →
                (∀ t ∈ R,
                  ‖dyadicDirichletPolynomial a₁ M₁ (onePlusIT t)‖ ^
                    (2 : ℕ) ≤ S) →
                (∑ t ∈ extremePairPoints R a₁ a₂ M₁ M₂ eps,
                  ‖dyadicDirichletPolynomial a₁ M₁ (onePlusIT t) *
                    dyadicDirichletPolynomial a₂ M₂ (onePlusIT t)‖ ^
                      (2 : ℕ)) ≤
                    8 * C * D * (Real.log T) ^ (Q + 1) * S := by
  obtain ⟨C, hC, hweighted⟩ :=
    weightedProduct_meanSquare_le_of_polylog_energy inputs
  obtain ⟨Ccard, hCcard, hcard⟩ :=
    eventually_card_extremePairPoints_le_two_mul_fifty_eps_of_divisorBounded_boundedOrder
      inputs.iwaniecKowalskiTheoremNineFour
  refine ⟨C, hC, ?_⟩
  intro B eps K hB heps hepsSmall hK A₀ hA₀
  obtain ⟨Dcard, hDcard, hcardA⟩ := hcard B eps K hB heps hK
  obtain ⟨D, M₀, Q, hD, hM₀, henergy⟩ :=
    dyadicEnergy_polylog_of_lucaToth inputs.lucaTothTheoremOne hB hA₀
  refine ⟨D, Q, hD, ?_⟩
  have halpha : 0 < 9 / 11 - 2 * eps := by
    norm_num at hepsSmall ⊢
    linarith
  have hgrow : ∀ᶠ T : ℝ in atTop, M₀ ≤ T ^ (9 / 11 - 2 * eps) :=
    (tendsto_rpow_atTop halpha).eventually_ge_atTop M₀
  filter_upwards [hcardA A₀ hA₀, hgrow, eventually_ge_atTop (2 : ℝ)] with
      T hcardT hgrowT hTtwo
  intro a₁ a₂ M₁ M₂ R S hM₁ hM₁T hM₂ hM₂T hM₂lower
    hell₁ hell₂ ha₁ ha₂ hR hspaced hS hSbound
  let R₁ := extremePairPoints R a₁ a₂ M₁ M₂ eps
  have hR₁subset : (↑R₁ : Set ℝ) ⊆ (↑R : Set ℝ) := by
    intro t ht
    exact (Finset.mem_filter.mp ht).1
  have hcardR₁ : (R₁.card : ℝ) ≤ 2 * T ^ (50 * eps) := by
    exact hcardT a₁ a₂ M₁ M₂ R hM₁ hM₁T hM₂ hM₂T
      hell₁ hell₂ ha₁ ha₂ hR hspaced
  have hcardTerm :
      (R₁.card : ℝ) * T ^ (1 / 2 : ℝ) / M₂ ≤ 2 :=
    extreme_cardinality_term_le_two (by linarith) hepsSmall hM₂lower hcardR₁
  have henergyM₂ :
      halaszMontgomeryDyadicEnergy a₂ M₂ ≤
        D * (Real.log T) ^ Q / M₂ :=
    henergy a₂ M₂ T (hgrowT.trans hM₂lower) hM₂T ha₂
  exact hweighted M₂ T D S Q a₂
    (fun t ↦ dyadicDirichletPolynomial a₁ M₁ (onePlusIT t)) R₁
    hM₂.le hTtwo hD.le hS henergyM₂ hcardTerm
    (fun t ht ↦ hSbound t (hR₁subset ht))
    (fun t ht ↦ hR t (hR₁subset ht))
    (Set.Pairwise.mono hR₁subset hspaced)


/-- Metadata for the source-closed weighted extreme-range layer. -/
def weightedExtremeRangeModule : ProofModule :=
  { name := "TypeII.WeightedExtremeRange"
    paperLocation :=
      "Proof of Proposition 5.1, weighted R₁ contribution"
    purpose :=
      "Derive the dyadic coefficient-energy estimate from the Luca--Tóth integer divisor moment, combine it with the completed extreme-pair cardinality bound and IK04 Theorem 9.6, and prove the required polylogarithmic weighted R₁ estimate."
    dependsOn :=
      ["TypeII.ExtremeLargeAbsorption", "TypeII.HalaszMontgomery",
        "Assumptions.lucaTothTheoremOne"]
    status := .proved }

end

end TypeII
end ExactSemiprimes

