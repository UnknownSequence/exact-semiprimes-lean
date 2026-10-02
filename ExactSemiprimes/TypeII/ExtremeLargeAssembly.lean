import ExactSemiprimes.TypeII.ExtremeRanges

/-!
# The powered-polynomial assembly on the extreme-large range

This file formalizes the elementary, but quantitatively important, part of
the `R₁` argument in Matomäki--Teräväinen, Proposition 5.1.  For a
polynomial of length `M` at height `T` the paper chooses

`ell = ceil (log T / log M)`.

The lemmas below prove that this is a positive, uniformly bounded integer,
that `M^ell` lies between `T` and `T*M`, and that the support enlargement
from `M^ell` to `(2*M)^ell` costs only the fixed factor `2^ell`.  They also
make the paper's two key exponent simplifications literal:

* `M^(20*eps*ell) <= T^(40*eps)` when `M <= T`;
* the remaining subpower losses fit under `T^(50*eps)` once they total at
  most `10*eps`.

No analytic estimate or asymptotic convention is used in this file.
-/

namespace ExactSemiprimes
namespace TypeII

open Filter

noncomputable section

/-! ## Exact finite set representing the two extreme-large alternatives -/

/-- Points where one fixed dyadic polynomial exceeds its extreme-large
threshold. -/
def extremeFactorPoints (R : Finset ℝ) (a : ℕ → ℂ)
    (M eps : ℝ) : Finset ℝ :=
  R.filter fun t ↦
    M ^ (-10 * eps) ≤ ‖dyadicDirichletPolynomial a M (onePlusIT t)‖

/-- The finite `R₁` set, before deterministic allocation against `R₃`. -/
def extremePairPoints (R : Finset ℝ) (a₁ a₂ : ℕ → ℂ)
    (M₁ M₂ eps : ℝ) : Finset ℝ :=
  R.filter fun t ↦
    M₁ ^ (-10 * eps) ≤
        ‖dyadicDirichletPolynomial a₁ M₁ (onePlusIT t)‖ ∨
      M₂ ^ (-10 * eps) ≤
        ‖dyadicDirichletPolynomial a₂ M₂ (onePlusIT t)‖

/-- The two-factor `R₁` set is exactly the union of its alternatives. -/
theorem extremePairPoints_eq_union
    (R : Finset ℝ) (a₁ a₂ : ℕ → ℂ) (M₁ M₂ eps : ℝ) :
    extremePairPoints R a₁ a₂ M₁ M₂ eps =
      extremeFactorPoints R a₁ M₁ eps ∪
        extremeFactorPoints R a₂ M₂ eps := by
  classical
  ext t
  simp [extremePairPoints, extremeFactorPoints, and_or_left]

/-- Consequently, equal bounds for the two alternatives give the precise
factor `2` in the cardinality of `R₁`. -/
theorem card_extremePairPoints_le_two_mul
    {R : Finset ℝ} {a₁ a₂ : ℕ → ℂ} {M₁ M₂ eps K : ℝ}
    (h₁ : ((extremeFactorPoints R a₁ M₁ eps).card : ℝ) ≤ K)
    (h₂ : ((extremeFactorPoints R a₂ M₂ eps).card : ℝ) ≤ K) :
    ((extremePairPoints R a₁ a₂ M₁ M₂ eps).card : ℝ) ≤
      2 * K := by
  rw [extremePairPoints_eq_union]
  have hcard :
      (((extremeFactorPoints R a₁ M₁ eps ∪
          extremeFactorPoints R a₂ M₂ eps).card : ℕ) : ℝ) ≤
        ((extremeFactorPoints R a₁ M₁ eps).card : ℝ) +
          ((extremeFactorPoints R a₂ M₂ eps).card : ℝ) := by
    exact_mod_cast Finset.card_union_le
      (extremeFactorPoints R a₁ M₁ eps)
      (extremeFactorPoints R a₂ M₂ eps)
  calc
    (((extremeFactorPoints R a₁ M₁ eps ∪
        extremeFactorPoints R a₂ M₂ eps).card : ℕ) : ℝ) ≤
        ((extremeFactorPoints R a₁ M₁ eps).card : ℝ) +
          ((extremeFactorPoints R a₂ M₂ eps).card : ℝ) := hcard
    _ ≤ K + K := add_le_add h₁ h₂
    _ = 2 * K := by ring

/-- The integer power used for either factor on the extreme-large set. -/
def extremePowerExponent (T M : ℝ) : ℕ :=
  ⌈Real.log T / Real.log M⌉₊

/-- The real number before rounding in `extremePowerExponent` is positive. -/
theorem extremePowerExponent_ratio_pos {T M : ℝ}
    (hT : 1 < T) (hM : 1 < M) :
    0 < Real.log T / Real.log M := by
  exact div_pos (Real.log_pos hT) (Real.log_pos hM)

/-- The chosen integer power is nonzero. -/
theorem extremePowerExponent_pos {T M : ℝ}
    (hT : 1 < T) (hM : 1 < M) :
    1 ≤ extremePowerExponent T M := by
  rw [extremePowerExponent, Nat.one_le_iff_ne_zero]
  exact (Nat.ceil_pos.mpr (extremePowerExponent_ratio_pos hT hM)).ne'

/-- Exact lower and upper bounds supplied by the ceiling choice.

The strict upper bound is useful: it avoids introducing an unnecessary
extra power of `T` when the discrete mean-value theorem is simplified. -/
theorem extremePowerExponent_pow_bounds {T M : ℝ}
    (hT : 1 < T) (hM : 1 < M) :
    T ≤ M ^ extremePowerExponent T M ∧
      M ^ extremePowerExponent T M < T * M := by
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hMpos : 0 < M := zero_lt_one.trans hM
  have hratioNonneg : 0 ≤ Real.log T / Real.log M :=
    (extremePowerExponent_ratio_pos hT hM).le
  have hlower :
      Real.log T / Real.log M ≤ (extremePowerExponent T M : ℝ) := by
    exact Nat.le_ceil _
  have hupper :
      (extremePowerExponent T M : ℝ) <
        Real.log T / Real.log M + 1 := by
    exact Nat.ceil_lt_add_one hratioNonneg
  constructor
  · rw [← Real.rpow_natCast]
    have hlogb :
        Real.logb M T ≤ (extremePowerExponent T M : ℝ) := by
      simpa [Real.logb] using hlower
    exact (Real.logb_le_iff_le_rpow hM hTpos).mp hlogb
  · rw [← Real.rpow_natCast]
    calc
      M ^ (extremePowerExponent T M : ℝ) <
          M ^ (Real.log T / Real.log M + 1) :=
        Real.rpow_lt_rpow_of_exponent_lt hM hupper
      _ = T * M := by
        rw [show Real.log T / Real.log M = Real.logb M T by rfl,
          Real.rpow_add hMpos, Real.rpow_logb hMpos hM.ne' hTpos,
          Real.rpow_one]

/-- If the polynomial has length at least `T^(eps/5)`, then the chosen
power is bounded in terms of `eps` alone.  This is the exact uniformity
behind the paper's notation `ell_j \ll 1`. -/
theorem extremePowerExponent_le_ceil_five_div {T M eps : ℝ}
    (hT : 1 < T) (heps : 0 < eps)
    (hMlower : T ^ (eps / 5) ≤ M) :
    extremePowerExponent T M ≤ ⌈5 / eps⌉₊ := by
  have hexponent : 0 < eps / 5 := by positivity
  have hTpow : 1 < T ^ (eps / 5) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_lt_rpow_of_exponent_lt hT hexponent
  have hM : 1 < M := hTpow.trans_le hMlower
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hMpos : 0 < M := zero_lt_one.trans hM
  have hlogM : 0 < Real.log M := Real.log_pos hM
  have hlog :
      (eps / 5) * Real.log T ≤ Real.log M := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hTpos _) hMlower
    simpa only [Real.log_rpow hTpos] using this
  apply Nat.ceil_mono
  rw [div_le_iff₀ hlogM]
  have hepspos : 0 < eps := heps
  have hlogT : 0 < Real.log T := Real.log_pos hT
  calc
    Real.log T ≤ (5 / eps) * ((eps / 5) * Real.log T) := by
      field_simp [heps.ne']
      norm_num
    _ ≤ (5 / eps) * Real.log M := by
      exact mul_le_mul_of_nonneg_left hlog (by positivity)

/-- Under the natural upper bound `M <= T`, the powered length is at most
`T^2`. -/
theorem extremePowerExponent_pow_le_sq {T M : ℝ}
    (hT : 1 < T) (hM : 1 < M) (hMupper : M ≤ T) :
    M ^ extremePowerExponent T M ≤ T ^ (2 : ℕ) := by
  calc
    M ^ extremePowerExponent T M ≤ T * M :=
      (extremePowerExponent_pow_bounds hT hM).2.le
    _ ≤ T * T :=
      mul_le_mul_of_nonneg_left hMupper (zero_lt_one.trans hT).le
    _ = T ^ (2 : ℕ) := by ring

/-- All ceiling-power facts needed for the first factor in Proposition 5.1,
under its printed scale range.  The concrete `eps <= 1/10` is only a
convenient explicit version of "eps sufficiently small". -/
theorem firstFactor_extremePower_data {T M eps : ℝ}
    (hT : 1 < T) (heps : 0 < eps) (hepsSmall : eps ≤ 1 / 10)
    (hMlower : T ^ (eps / 5) ≤ M)
    (hMupper : M ≤ T ^ (2 / 11 + eps)) :
    1 ≤ extremePowerExponent T M ∧
      extremePowerExponent T M ≤ ⌈5 / eps⌉₊ ∧
      T ≤ M ^ extremePowerExponent T M ∧
      M ^ extremePowerExponent T M ≤ T ^ (2 : ℕ) := by
  have hexponent : 0 < eps / 5 := by positivity
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hTpow : 1 < T ^ (eps / 5) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_lt_rpow_of_exponent_lt hT hexponent
  have hM : 1 < M := hTpow.trans_le hMlower
  have hexponentUpper : 2 / 11 + eps ≤ (1 : ℝ) := by
    norm_num at hepsSmall ⊢
    linarith
  have hMleT : M ≤ T := by
    calc
      M ≤ T ^ (2 / 11 + eps) := hMupper
      _ ≤ T ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT.le hexponentUpper
      _ = T := Real.rpow_one T
  exact ⟨extremePowerExponent_pos hT hM,
    extremePowerExponent_le_ceil_five_div hT heps hMlower,
    (extremePowerExponent_pow_bounds hT hM).1,
    extremePowerExponent_pow_le_sq hT hM hMleT⟩

/-- The same ceiling-power package for the complementary factor.  Its
concrete interval is the one proved in `complementaryLengthBounds`. -/
theorem secondFactor_extremePower_data {T M eps : ℝ}
    (hT : 1 < T) (heps : 0 < eps) (hepsSmall : eps ≤ 1 / 10)
    (hMlower : T ^ (9 / 11 - 2 * eps) ≤ M)
    (hMupper : M ≤ T ^ (1 - eps / 6)) :
    1 ≤ extremePowerExponent T M ∧
      extremePowerExponent T M ≤ ⌈5 / eps⌉₊ ∧
      T ≤ M ^ extremePowerExponent T M ∧
      M ^ extremePowerExponent T M ≤ T ^ (2 : ℕ) := by
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hlowerExponent : eps / 5 ≤ 9 / 11 - 2 * eps := by
    norm_num at hepsSmall ⊢
    linarith
  have hbaseLower : T ^ (eps / 5) ≤ M := by
    exact (Real.rpow_le_rpow_of_exponent_le hT.le hlowerExponent).trans
      hMlower
  have hTpow : 1 < T ^ (eps / 5) := by
    have : 0 < eps / 5 := by positivity
    simpa only [Real.rpow_zero] using
      Real.rpow_lt_rpow_of_exponent_lt hT this
  have hM : 1 < M := hTpow.trans_le hbaseLower
  have hMleT : M ≤ T := by
    calc
      M ≤ T ^ (1 - eps / 6) := hMupper
      _ ≤ T ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)
      _ = T := Real.rpow_one T
  exact ⟨extremePowerExponent_pos hT hM,
    extremePowerExponent_le_ceil_five_div hT heps hbaseLower,
    (extremePowerExponent_pow_bounds hT hM).1,
    extremePowerExponent_pow_le_sq hT hM hMleT⟩

/-- A bounded ceiling exponent also gives a uniform upper bound for the
expanded support `(2M)^ell`. -/
theorem poweredSupport_le_of_exponent_bound {T M : ℝ} {ell K : ℕ}
    (hM : 0 ≤ M) (hpow : M ^ ell ≤ T ^ (2 : ℕ)) (hell : ell ≤ K) :
    (2 * M) ^ ell ≤ (2 : ℝ) ^ K * T ^ (2 : ℕ) := by
  rw [mul_pow]
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hell) hpow
    (pow_nonneg hM ell) (by positivity)

/-- The logarithm and the bounded support-expansion factors use only
`T^(2*eps)` of the available `T^(10*eps)` budget, uniformly over all
`ell <= K` and all powered supports below `T^2`. -/
theorem eventually_extreme_geometricFactor_le
    (C : ℝ) (hC : 0 ≤ C) (K : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ T : ℝ in atTop, ∀ (M : ℝ) (ell : ℕ),
      1 ≤ M → ell ≤ K → M ^ ell ≤ T ^ (2 : ℕ) →
      C * Real.log (2 * (2 * M) ^ ell) *
          ((1 + (2 : ℝ) ^ ell) * (2 : ℝ) ^ ell) ≤
        T ^ (2 * eps) := by
  let A : ℝ := 2 * (2 : ℝ) ^ K
  let Q : ℝ := C * 3 * ((1 + (2 : ℝ) ^ K) * (2 : ℝ) ^ K)
  have hApos : 0 < A := by simp [A]
  have hQnonneg : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hconst : ∀ᶠ T : ℝ in atTop, Q ≤ T ^ eps :=
    (tendsto_rpow_atTop heps).eventually_ge_atTop Q
  have hlog : ∀ᶠ T : ℝ in atTop, Real.log T ≤ T ^ eps := by
    simpa only [Real.rpow_one] using eventually_log_rpow_le_rpow 1 heps
  filter_upwards [eventually_ge_atTop (max 2 A), hconst, hlog] with
      T hT hconstT hlogT
  intro M ell hM hell hpow
  have hTtwo : 2 ≤ T := le_trans (le_max_left 2 A) hT
  have hTpos : 0 < T := by linarith
  have hAT : A ≤ T := le_trans (le_max_right 2 A) hT
  have hMnonneg : 0 ≤ M := zero_le_one.trans hM
  have hsupport : (2 * M) ^ ell ≤ (2 : ℝ) ^ K * T ^ (2 : ℕ) :=
    poweredSupport_le_of_exponent_bound hMnonneg hpow hell
  have harg : 2 * (2 * M) ^ ell ≤ A * T ^ (2 : ℕ) := by
    dsimp [A]
    nlinarith
  have hlogArg :
      Real.log (2 * (2 * M) ^ ell) ≤ 3 * Real.log T := by
    have hpositive : 0 < 2 * (2 * M) ^ ell := by positivity
    calc
      Real.log (2 * (2 * M) ^ ell) ≤
          Real.log (A * T ^ (2 : ℕ)) :=
        Real.log_le_log hpositive harg
      _ = Real.log A + 2 * Real.log T := by
        rw [Real.log_mul hApos.ne' (ne_of_gt (pow_pos hTpos 2)),
          Real.log_pow]
        norm_num
      _ ≤ Real.log T + 2 * Real.log T := by
        gcongr
      _ = 3 * Real.log T := by ring
  have htwoPow : (2 : ℝ) ^ ell ≤ (2 : ℝ) ^ K :=
    pow_le_pow_right₀ (by norm_num) hell
  have hfixed :
      (1 + (2 : ℝ) ^ ell) * (2 : ℝ) ^ ell ≤
        (1 + (2 : ℝ) ^ K) * (2 : ℝ) ^ K := by
    exact mul_le_mul (add_le_add_right htwoPow 1) htwoPow (by positivity)
      (by positivity)
  have hlogTnonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hgeometric :
      C * Real.log (2 * (2 * M) ^ ell) *
          ((1 + (2 : ℝ) ^ ell) * (2 : ℝ) ^ ell) ≤
        Q * Real.log T := by
    dsimp [Q]
    calc
      C * Real.log (2 * (2 * M) ^ ell) *
            ((1 + (2 : ℝ) ^ ell) * (2 : ℝ) ^ ell) ≤
          C * (3 * Real.log T) *
            ((1 + (2 : ℝ) ^ ell) * (2 : ℝ) ^ ell) := by
        gcongr
      _ ≤ C * (3 * Real.log T) *
            ((1 + (2 : ℝ) ^ K) * (2 : ℝ) ^ K) := by
        gcongr
      _ = (C * 3 * ((1 + (2 : ℝ) ^ K) * (2 : ℝ) ^ K)) *
            Real.log T := by ring
  calc
    C * Real.log (2 * (2 * M) ^ ell) *
          ((1 + (2 : ℝ) ^ ell) * (2 : ℝ) ^ ell) ≤
        Q * Real.log T := hgeometric
    _ ≤ T ^ eps * T ^ eps :=
      mul_le_mul hconstT hlogT hlogTnonneg (Real.rpow_nonneg hTpos.le _)
    _ = T ^ (2 * eps) := by
      rw [← Real.rpow_add hTpos]
      congr 1
      ring

/-- The support enlargement in the powered polynomial is exactly the fixed
factor `2^ell`. -/
theorem poweredSupport_ratio_eq_twoPow {M : ℝ} (hM : 0 < M) (ell : ℕ) :
    (2 * M) ^ ell / M ^ ell = (2 : ℝ) ^ ell := by
  rw [mul_pow]
  field_simp [ne_of_gt (pow_pos hM ell)]

/-- The mean-value length factor is bounded by `1 + 2^ell`. -/
theorem meanValue_length_ratio_le {T M : ℝ} {ell : ℕ}
    (hM : 0 < M) (hTle : T ≤ M ^ ell) :
    (T + (2 * M) ^ ell) / M ^ ell ≤ 1 + (2 : ℝ) ^ ell := by
  have hMpow : 0 < M ^ ell := pow_pos hM ell
  rw [add_div, poweredSupport_ratio_eq_twoPow hM]
  simpa only [add_comm] using
    add_le_add_right ((div_le_one hMpow).mpr hTle) ((2 : ℝ) ^ ell)

/-- The large-value threshold contributes at most `T^(40*eps)`.

Indeed the reciprocal square of the threshold is
`M^(20*eps*ell)`, while the ceiling choice gives `M^ell <= T^2`.
This is the first displayed exponent simplification in the paper's `R₁`
calculation. -/
theorem extremeThreshold_growth_le {T M eps : ℝ}
    (hT : 1 < T) (hM : 1 < M) (hMupper : M ≤ T)
    (heps : 0 ≤ eps) :
    M ^ (20 * eps * (extremePowerExponent T M : ℝ)) ≤
      T ^ (40 * eps) := by
  let ell := extremePowerExponent T M
  have hpow : M ^ ell ≤ T ^ (2 : ℕ) :=
    extremePowerExponent_pow_le_sq hT hM hMupper
  have hMpos : 0 < M := zero_lt_one.trans hM
  have hTpos : 0 < T := zero_lt_one.trans hT
  calc
    M ^ (20 * eps * (ell : ℝ)) =
        (M ^ ell) ^ (20 * eps) := by
      rw [show 20 * eps * (ell : ℝ) = (ell : ℝ) * (20 * eps) by ring,
        Real.rpow_mul hMpos.le, Real.rpow_natCast]
    _ ≤ (T ^ (2 : ℕ)) ^ (20 * eps) := by
      exact Real.rpow_le_rpow (pow_nonneg hMpos.le ell) hpow (by positivity)
    _ = T ^ (40 * eps) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
      congr 1
      ring

/-- The threshold denominator in the exact discrete mean-value quotient is
precisely the growth factor appearing in `extremeThreshold_growth_le`. -/
theorem reciprocal_extremeThreshold_sq {M eps : ℝ} (hM : 0 < M)
    (ell : ℕ) :
    (((M ^ (-10 * eps)) ^ ell) ^ (2 : ℕ))⁻¹ =
      M ^ (20 * eps * (ell : ℝ)) := by
  calc
    (((M ^ (-10 * eps)) ^ ell) ^ (2 : ℕ))⁻¹ =
        ((M ^ (-10 * eps))⁻¹) ^ (ell * 2) := by
      rw [← pow_mul, inv_pow]
    _ = (M ^ (10 * eps)) ^ (ell * 2) := by
      congr 1
      rw [← Real.rpow_neg hM.le]
      congr 1
      ring
    _ = M ^ ((10 * eps) * ((ell * 2 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    _ = M ^ (20 * eps * (ell : ℝ)) := by
      congr 1
      push_cast
      ring

/-- Exact algebraic simplification of the quotient delivered by
`card_largePoweredDyadic_le_of_convolution_bound`.  The two length ratios
are replaced by `1+2^ell` and `2^ell`, and the reciprocal threshold is
written as `M^(20*eps*ell)`. -/
theorem poweredMeanValue_quotient_le
    {C T M eps B logFactor : ℝ} {ell : ℕ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hM : 0 < M)
    (hlog : 0 ≤ logFactor) (hTle : T ≤ M ^ ell) :
    (C * (T + (2 * M) ^ ell) * logFactor *
          ((2 * M) ^ ell * (B / M ^ ell) ^ (2 : ℕ))) /
        ((M ^ (-10 * eps)) ^ ell) ^ (2 : ℕ) ≤
      (C * logFactor *
          ((1 + (2 : ℝ) ^ ell) * (2 : ℝ) ^ ell) * B ^ (2 : ℕ)) *
        M ^ (20 * eps * (ell : ℝ)) := by
  have hMpow : 0 < M ^ ell := pow_pos hM ell
  have hthreshold : 0 < ((M ^ (-10 * eps)) ^ ell) ^ (2 : ℕ) := by
    positivity
  have hlength := meanValue_length_ratio_le (T := T) hM hTle
  have hsupport := poweredSupport_ratio_eq_twoPow hM ell
  have hratioNonneg :
      0 ≤ (T + (2 * M) ^ ell) / M ^ ell := by positivity
  have hsupportNonneg : 0 ≤ (2 * M) ^ ell / M ^ ell := by positivity
  have hratioProduct :
      ((T + (2 * M) ^ ell) / M ^ ell) *
          ((2 * M) ^ ell / M ^ ell) ≤
        (1 + (2 : ℝ) ^ ell) * (2 : ℝ) ^ ell := by
    apply mul_le_mul hlength
    · exact hsupport.le
    · exact hsupportNonneg
    · positivity
  have hrearrange :
      (C * (T + (2 * M) ^ ell) * logFactor *
            ((2 * M) ^ ell * (B / M ^ ell) ^ (2 : ℕ))) /
          ((M ^ (-10 * eps)) ^ ell) ^ (2 : ℕ) =
        (C * logFactor *
            (((T + (2 * M) ^ ell) / M ^ ell) *
              ((2 * M) ^ ell / M ^ ell)) * B ^ (2 : ℕ)) *
          (((M ^ (-10 * eps)) ^ ell) ^ (2 : ℕ))⁻¹ := by
    field_simp [ne_of_gt hMpow, ne_of_gt hthreshold]
  rw [hrearrange, reciprocal_extremeThreshold_sq hM]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hM.le _)
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg B)
  exact mul_le_mul_of_nonneg_left hratioProduct
    (mul_nonneg hC hlog)

/-- Abstract final exponent bookkeeping: a `T^(40*eps)` threshold loss and
at most `T^(10*eps)` of all remaining subpower losses fit in the paper's
`T^(50*eps)` envelope. -/
theorem forty_eps_mul_ten_eps_le_fifty_eps {T eps A B : ℝ}
    (hT : 1 ≤ T)
    (hA : A ≤ T ^ (40 * eps)) (hB : B ≤ T ^ (10 * eps))
    (hBnonneg : 0 ≤ B) :
    A * B ≤ T ^ (50 * eps) := by
  calc
    A * B ≤ T ^ (40 * eps) * T ^ (10 * eps) :=
      mul_le_mul hA hB hBnonneg (Real.rpow_nonneg (by positivity) _)
    _ = T ^ (50 * eps) := by
      rw [← Real.rpow_add (by positivity : 0 < T)]
      congr 1
      ring

/-- Exact `T^(50*eps)` endpoint for one of the two extreme-large factors.

Everything analytic that remains is isolated in `hremaining`: it says that
the logarithm, the bounded support-expansion constants, and the squared
convolution-coefficient bound together cost at most `T^(10*eps)`.  The
theorem then combines the source-faithful IK04 Theorem 9.4 application with
the ceiling-power arithmetic above. -/
theorem card_largePoweredDyadic_le_fifty_eps_of_remaining_bound
    (hIK : IwaniecKowalskiTheoremNineFourStatement) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : ℕ → ℂ) (M T eps B : ℝ) (R : Finset ℝ),
        1 < M → M ≤ T → 0 < eps → 0 ≤ B →
        (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
        IsOneSpaced (↑R : Set ℝ) →
        (∀ t ∈ R,
          M ^ (-10 * eps) ≤
            ‖dyadicDirichletPolynomial a M (onePlusIT t)‖) →
        (∀ n ∈
            (powerTuples (dyadicInterval M) (extremePowerExponent T M)).image
              tupleProduct,
          ‖powerConvolutionCoefficient a (dyadicInterval M)
              (extremePowerExponent T M) n‖ ≤ B) →
        C * Real.log
              (2 * (2 * M) ^ (extremePowerExponent T M)) *
              ((1 + (2 : ℝ) ^ (extremePowerExponent T M)) *
                (2 : ℝ) ^ (extremePowerExponent T M)) *
              B ^ (2 : ℕ) ≤
            T ^ (10 * eps) →
        (R.card : ℝ) ≤ T ^ (50 * eps) := by
  obtain ⟨C, hC, hcard⟩ :=
    card_largePoweredDyadic_le_of_convolution_bound hIK
  refine ⟨C, hC, ?_⟩
  intro a M T eps B R hM hMupper heps hB hR hspaced hlarge hcoeff
    hremaining
  let ell := extremePowerExponent T M
  have hT : 1 < T := hM.trans_le hMupper
  have hMpos : 0 < M := zero_lt_one.trans hM
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hTle : T ≤ M ^ ell :=
    (extremePowerExponent_pow_bounds hT hM).1
  have hlog : 0 ≤ Real.log (2 * (2 * M) ^ ell) := by
    apply Real.log_nonneg
    have : 1 ≤ (2 * M) ^ ell := by
      exact one_le_pow₀ (by linarith)
    nlinarith
  have hraw := hcard a M T eps B ell R hM.le hT.le hB hR hspaced
    hlarge hcoeff
  have hquotient := poweredMeanValue_quotient_le (eps := eps) (B := B)
    hC.le hTpos.le hMpos hlog hTle
  have hthreshold := extremeThreshold_growth_le hT hM hMupper heps.le
  have hcombine := forty_eps_mul_ten_eps_le_fifty_eps hT.le
    hthreshold hremaining
    (by positivity :
      0 ≤ C * Real.log (2 * (2 * M) ^ ell) *
        ((1 + (2 : ℝ) ^ ell) * (2 : ℝ) ^ ell) * B ^ (2 : ℕ))
  exact hraw.trans (hquotient.trans (by simpa [ell, mul_comm] using hcombine))

/-- Two applications of the preceding one-factor theorem give the paper's
full extreme-large cardinality bound, with the harmless factor `2` exposed:
`#R₁ <= 2*T^(50*eps)`. -/
theorem card_extremePairPoints_le_two_mul_fifty_eps_of_remaining_bounds
    (hIK : IwaniecKowalskiTheoremNineFourStatement) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a₁ a₂ : ℕ → ℂ) (M₁ M₂ T eps B₁ B₂ : ℝ) (R : Finset ℝ),
        1 < M₁ → M₁ ≤ T → 1 < M₂ → M₂ ≤ T →
        0 < eps → 0 ≤ B₁ → 0 ≤ B₂ →
        (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
        IsOneSpaced (↑R : Set ℝ) →
        (∀ n ∈
            (powerTuples (dyadicInterval M₁)
              (extremePowerExponent T M₁)).image tupleProduct,
          ‖powerConvolutionCoefficient a₁ (dyadicInterval M₁)
              (extremePowerExponent T M₁) n‖ ≤ B₁) →
        (∀ n ∈
            (powerTuples (dyadicInterval M₂)
              (extremePowerExponent T M₂)).image tupleProduct,
          ‖powerConvolutionCoefficient a₂ (dyadicInterval M₂)
              (extremePowerExponent T M₂) n‖ ≤ B₂) →
        C * Real.log
              (2 * (2 * M₁) ^ (extremePowerExponent T M₁)) *
              ((1 + (2 : ℝ) ^ (extremePowerExponent T M₁)) *
                (2 : ℝ) ^ (extremePowerExponent T M₁)) *
              B₁ ^ (2 : ℕ) ≤ T ^ (10 * eps) →
        C * Real.log
              (2 * (2 * M₂) ^ (extremePowerExponent T M₂)) *
              ((1 + (2 : ℝ) ^ (extremePowerExponent T M₂)) *
                (2 : ℝ) ^ (extremePowerExponent T M₂)) *
              B₂ ^ (2 : ℕ) ≤ T ^ (10 * eps) →
        ((extremePairPoints R a₁ a₂ M₁ M₂ eps).card : ℝ) ≤
          2 * T ^ (50 * eps) := by
  obtain ⟨C, hC, hone⟩ :=
    card_largePoweredDyadic_le_fifty_eps_of_remaining_bound hIK
  refine ⟨C, hC, ?_⟩
  intro a₁ a₂ M₁ M₂ T eps B₁ B₂ R hM₁ hM₁T hM₂ hM₂T heps
    hB₁ hB₂ hR hspaced hcoeff₁ hcoeff₂ hremaining₁ hremaining₂
  let R₁ := extremeFactorPoints R a₁ M₁ eps
  let R₂ := extremeFactorPoints R a₂ M₂ eps
  have hsubset₁ : (↑R₁ : Set ℝ) ⊆ (↑R : Set ℝ) := by
    intro t ht
    exact (Finset.mem_filter.mp ht).1
  have hsubset₂ : (↑R₂ : Set ℝ) ⊆ (↑R : Set ℝ) := by
    intro t ht
    exact (Finset.mem_filter.mp ht).1
  have hcard₁ : (R₁.card : ℝ) ≤ T ^ (50 * eps) := by
    apply hone a₁ M₁ T eps B₁ R₁ hM₁ hM₁T heps hB₁
    · intro t ht
      exact hR t (hsubset₁ ht)
    · exact Set.Pairwise.mono hsubset₁ hspaced
    · intro t ht
      exact (Finset.mem_filter.mp ht).2
    · exact hcoeff₁
    · exact hremaining₁
  have hcard₂ : (R₂.card : ℝ) ≤ T ^ (50 * eps) := by
    apply hone a₂ M₂ T eps B₂ R₂ hM₂ hM₂T heps hB₂
    · intro t ht
      exact hR t (hsubset₂ ht)
    · exact Set.Pairwise.mono hsubset₂ hspaced
    · intro t ht
      exact (Finset.mem_filter.mp ht).2
    · exact hcoeff₂
    · exact hremaining₂
  exact card_extremePairPoints_le_two_mul
    (R := R) (a₁ := a₁) (a₂ := a₂) (M₁ := M₁) (M₂ := M₂)
    (eps := eps) (K := T ^ (50 * eps)) (by simpa [R₁] using hcard₁)
    (by simpa [R₂] using hcard₂)

/-- Metadata for the newly closed elementary `R₁` assembly layer. -/
def extremeLargeAssemblyModule : ProofModule :=
  { name := "TypeII.ExtremeLargeAssembly"
    paperLocation :=
      "Proof of Proposition 5.1, R₁: ell_j=ceil(log T/log M_j) and exponent simplification"
    purpose :=
      "Prove the ceiling-power bounds, uniform boundedness in eps, exact support ratio, and the 40eps+10eps=50eps exponent bookkeeping."
    dependsOn := ["TypeII.ExtremeRanges", "TypeII.PoweredMeanValue"]
    status := .proved }

end

end TypeII
end ExactSemiprimes
