import ExactSemiprimes.Definitions

/-!
# Transfer of buffered prime windows from `log X` to `log x`

The analytic argument selects dyadic blocks using powers of `log X`, but the
theorem is stated using powers of `log x`, uniformly for `x ∈ [X,2X]`.
The only non-immediate direction is the lower endpoint: the fixed positive
gap between its two exponents absorbs the bounded change from `log X` to
`log (2X)`.

The statements below are exact `Filter.Eventually` statements.  In
particular, no asymptotic notation is used as a hypothesis.
-/

namespace ExactSemiprimes
namespace Completion

open Filter

/-- A positive exponent gap absorbs replacing `log X` by `log (2X)`.

More precisely, if `0 ≤ ℓ < a`, then eventually
`(log (2X))^ℓ < (log X)^a`.  This is the quantitative core of the
uniform buffered-window transfer. -/
theorem eventually_log_two_mul_rpow_lt_log_rpow {ell a : ℝ}
    (hell : 0 ≤ ell) (hgap : ell < a) :
    ∀ᶠ X : ℝ in atTop,
      (Real.log (2 * X)) ^ ell < (Real.log X) ^ a := by
  have hgapPos : 0 < a - ell := sub_pos.mpr hgap
  have hgapEventually :
      ∀ᶠ X : ℝ in atTop, (2 : ℝ) ^ ell < (Real.log X) ^ (a - ell) := by
    exact
      (((_root_.tendsto_rpow_atTop hgapPos).comp Real.tendsto_log_atTop).eventually
        (eventually_gt_atTop ((2 : ℝ) ^ ell)))
  filter_upwards [eventually_ge_atTop (2 : ℝ), hgapEventually] with X hX hpow
  have hXpos : 0 < X := by linarith
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogTwo_le : Real.log (2 : ℝ) ≤ Real.log X :=
    Real.log_le_log (by norm_num) hX
  have hlogTwoX_le : Real.log (2 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num) hXpos.ne']
    linarith
  calc
    (Real.log (2 * X)) ^ ell
        ≤ (2 * Real.log X) ^ ell :=
          Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hlogTwoX_le hell
    _ = (2 : ℝ) ^ ell * (Real.log X) ^ ell := by
          rw [Real.mul_rpow (by norm_num) hlogXpos.le]
    _ < (Real.log X) ^ (a - ell) * (Real.log X) ^ ell :=
          mul_lt_mul_of_pos_right hpow (Real.rpow_pos_of_pos hlogXpos ell)
    _ = (Real.log X) ^ a := by
          rw [← Real.rpow_add hlogXpos]
          ring_nf

/-- Exact uniform transfer for a buffered dyadic block.

The hypotheses say that `(P,2P]` lies between the inner powers
`(log X)^a` and `(log X)^b`.  If the outer exponents satisfy
`0 ≤ ℓ < a` and `0 ≤ b ≤ u`, then, for every sufficiently large `X`,
every point of that block lies in `((log x)^ℓ,(log x)^u]` simultaneously
for every `x ∈ [X,2X]`. -/
theorem eventually_buffered_dyadic_window_transfer
    {ell a b u : ℝ}
    (hell : 0 ≤ ell) (hella : ell < a)
    (hb : 0 ≤ b) (hbu : b ≤ u) :
    ∀ᶠ X : ℝ in atTop, ∀ x P p : ℝ,
      X ≤ x → x ≤ 2 * X →
      (Real.log X) ^ a < P → P < p →
      p ≤ 2 * P → 2 * P ≤ (Real.log X) ^ b →
      (Real.log x) ^ ell < p ∧ p ≤ (Real.log x) ^ u := by
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    eventually_log_two_mul_rpow_lt_log_rpow hell hella] with X hX hLower
  intro x P p hXx hxTwo hInnerLower hPp hpTwoP hInnerUpper
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hX
  have hxpos : 0 < x := hXpos.trans_le hXx
  have hlogX_one : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hX
  have hlogX_le_logx : Real.log X ≤ Real.log x :=
    Real.log_le_log hXpos hXx
  have hlogx_nonneg : 0 ≤ Real.log x :=
    (zero_le_one.trans hlogX_one).trans hlogX_le_logx
  have hlogx_one : 1 ≤ Real.log x := hlogX_one.trans hlogX_le_logx
  have hlogx_le_logTwoX : Real.log x ≤ Real.log (2 * X) :=
    Real.log_le_log hxpos hxTwo
  constructor
  · exact
      (Real.rpow_le_rpow hlogx_nonneg hlogx_le_logTwoX hell).trans_lt
        (hLower.trans (hInnerLower.trans hPp))
  · calc
      p ≤ 2 * P := hpTwoP
      _ ≤ (Real.log X) ^ b := hInnerUpper
      _ ≤ (Real.log x) ^ b :=
        Real.rpow_le_rpow (zero_le_one.trans hlogX_one) hlogX_le_logx hb
      _ ≤ (Real.log x) ^ u :=
        Real.rpow_le_rpow_of_exponent_le hlogx_one hbu

/-- The version used directly for the paper's natural-number dyadic prime
blocks.  Primality is irrelevant to the transfer, so the conclusion holds
for every natural number in the block. -/
theorem eventually_dyadicRange_subset_log_window
    {ell a b u : ℝ}
    (hell : 0 ≤ ell) (hella : ell < a)
    (hb : 0 ≤ b) (hbu : b ≤ u) :
    ∀ᶠ X : ℝ in atTop, ∀ x P : ℝ, ∀ p : ℕ,
      X ≤ x → x ≤ 2 * X →
      (Real.log X) ^ a < P →
      2 * P ≤ (Real.log X) ^ b →
      InDyadicRange P p →
      (Real.log x) ^ ell < (p : ℝ) ∧
        (p : ℝ) ≤ (Real.log x) ^ u := by
  filter_upwards [eventually_buffered_dyadic_window_transfer hell hella hb hbu]
    with X hX
  intro x P p hXx hxTwo hInnerLower hInnerUpper hp
  exact hX x P p hXx hxTwo hInnerLower hp.1 hp.2 hInnerUpper

/-- Specialization to the four buffered exponents in Section 7.2 of the
paper.  The sole size assumptions are `Δ > 0` and nonnegativity of the
outer lower exponent. -/
theorem eventually_parameter_prime_window_transfer {c Δ : ℝ}
    (hΔ : 0 < Δ) (houter : 0 ≤ c - 1 - Δ) :
    ∀ᶠ X : ℝ in atTop, ∀ x P : ℝ, ∀ p : ℕ,
      X ≤ x → x ≤ 2 * X →
      (Real.log X) ^ (c - 1 - 3 * Δ / 4) < P →
      2 * P ≤ (Real.log X) ^ (c - 1 - 5 * Δ / 8) →
      InDyadicRange P p →
      (Real.log x) ^ (c - 1 - Δ) < (p : ℝ) ∧
        (p : ℝ) ≤ (Real.log x) ^ (c - 1 - Δ / 2) := by
  apply eventually_dyadicRange_subset_log_window
  · exact houter
  · linarith
  · linarith
  · linarith

def primeWindowTransferModule : ProofModule :=
  { name := "Completion.PrimeWindowTransfer"
    paperLocation := "Section 7.2, buffered inclusion for x in [X,2X]"
    purpose :=
      "Uniformly transfer every selected dyadic prime block from its buffered log-X window to the theorem's log-x window."
    dependsOn := ["Definitions", "Mathlib real logarithm and real-power estimates"]
    status := .proved }

end Completion
end ExactSemiprimes
