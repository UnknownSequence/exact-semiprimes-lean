import ExactSemiprimes.Completion.DyadicGlobalization
import ExactSemiprimes.Completion.IntervalMonotonicity
import ExactSemiprimes.Sparse.EndpointAlgebra

/-!
# Parameter theorem for every `c > 3688/1763` (paper Theorem 1.3)

The paper has two conclusions: existence for every exponent above
`3688/1763 = 2.09188…`,
and, up to exponent `21/10`, a quantitative lower bound for products whose
displayed prime factor lies in a prescribed logarithmic window.  We
record both conclusions separately and combine them in
`ParameterTheoremStatement`.  None of the analytic estimates needed to prove
these statements is assumed in this file.
-/

namespace ExactSemiprimes
namespace Results

/-- The quantitative existence part of the paper's parameter theorem.  It is
kept as a named projection of the full target for compatibility with modules
that only use existence. -/
def ParameterExistenceStatement : Prop :=
  ∀ c : ℝ, (3688 : ℝ) / 1763 < c →
    ∃ δ : ℝ, 0 < δ ∧
      HasLogPowerExceptionalBound (LogIntervalContainsSemiprime c) δ

/-- The pointwise counting conclusion in Theorem 1.3.  It says that the
interval `(x, x + (log x)^c]` contains at least a positive constant times
`(log x)^(c-1)` products `p*q`, where the displayed prime `p` belongs to

`((log x)^(c-1-Δ), (log x)^(c-1-Δ/2)]`.

The constant `κ` is quantified outside the exceptional-set predicate, so it
is uniform in `x` (while being allowed to depend on the fixed `c` and `Δ`). -/
def ParameterWindowCountProperty (c Δ κ : ℝ) (x : ℕ) : Prop :=
  κ * logarithmicLength (c - 1) x ≤
    (windowedPrimeProductCount
      (x : ℝ)
      (logarithmicLength c x)
      (logarithmicLength (c - 1 - Δ) x)
      (logarithmicLength (c - 1 - Δ / 2) x) : ℝ)

/-- The quantitative prime-window refinement of paper Theorem 1.3.  This is
the formal counterpart of the notation `\gg_{c,Δ} (log x)^(c-1)` together
with a power-saving exceptional set. -/
def ParameterWindowCountStatement : Prop :=
  ∀ c : ℝ, (3688 : ℝ) / 1763 < c → c ≤ (21 : ℝ) / 10 →
    ∀ Δ : ℝ, 0 < Δ → (1925 : ℝ) / 1763 < c - 1 - Δ →
      ∃ κ δ : ℝ, 0 < κ ∧ 0 < δ ∧
        HasLogPowerExceptionalBound (ParameterWindowCountProperty c Δ κ) δ

/-- The complete target corresponding to paper Theorem 1.3.  Keeping the two
conjuncts visible prevents the prime-window lower bound from being silently
weakened to mere semiprime existence. -/
def ParameterTheoremStatement : Prop :=
  ParameterExistenceStatement ∧ ParameterWindowCountStatement

theorem parameterExistence_of_parameterTheorem
    (h : ParameterTheoremStatement) : ParameterExistenceStatement :=
  h.1

theorem parameterWindowCount_of_parameterTheorem
    (h : ParameterTheoremStatement) : ParameterWindowCountStatement :=
  h.2

/-- Enlarging the allowed prime-factor window cannot decrease the number of
products counted. -/
theorem windowedPrimeProductCount_mono_window
    {x h L₁ U₁ L₂ U₂ : ℝ} (hL : L₂ ≤ L₁) (hU : U₁ ≤ U₂) :
    windowedPrimeProductCount x h L₁ U₁ ≤
      windowedPrimeProductCount x h L₂ U₂ := by
  classical
  simp only [windowedPrimeProductCount, intervalCount]
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  refine ⟨hn.1, ?_⟩
  rcases hn.2 with ⟨p, q, hp, hq, hn, hpL, hpU⟩
  exact ⟨p, q, hp, hq, hn, lt_of_le_of_lt hL hpL, hpU.trans hU⟩

/-- A nonempty windowed-product count gives an exact semiprime in the same
short interval, independently of the particular factor window. -/
theorem logIntervalContainsSemiprime_of_windowedPrimeProductCount_pos
    {c L U : ℝ} {x : ℕ}
    (hcount : 0 < windowedPrimeProductCount
      (x : ℝ) (logarithmicLength c x) L U) :
    LogIntervalContainsSemiprime c x := by
  classical
  rw [windowedPrimeProductCount, intervalCount] at hcount
  obtain ⟨n, hn⟩ := Finset.card_pos.mp hcount
  rw [Finset.mem_filter] at hn
  exact ⟨n, hn.1, exactSemiprime_of_windowedPrimeProduct hn.2⟩

/-- At every `x > 1`, a positive quantitative lower bound in the advertised
prime window already supplies an exact semiprime in the interval.  The global
exceptional-set passage only has to discard the finitely many smaller `x`. -/
theorem logIntervalContainsSemiprime_of_parameterWindowCount
    {c Δ κ : ℝ} {x : ℕ} (hx : 2 ≤ x) (hκ : 0 < κ)
    (hcount : ParameterWindowCountProperty c Δ κ x) :
    LogIntervalContainsSemiprime c x := by
  have hxReal : (1 : ℝ) < (x : ℝ) := by
    exact_mod_cast (show 1 < x by omega)
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos hxReal
  have hlength : 0 < logarithmicLength (c - 1) x := by
    exact Real.rpow_pos_of_pos hlog _
  have hcountReal :
      0 < (windowedPrimeProductCount
        (x : ℝ)
        (logarithmicLength c x)
        (logarithmicLength (c - 1 - Δ) x)
        (logarithmicLength (c - 1 - Δ / 2) x) : ℝ) :=
    (mul_pos hκ hlength).trans_le hcount
  have hcountNat :
      0 < windowedPrimeProductCount
        (x : ℝ)
        (logarithmicLength c x)
        (logarithmicLength (c - 1 - Δ) x)
        (logarithmicLength (c - 1 - Δ / 2) x) := by
    exact_mod_cast hcountReal
  exact logIntervalContainsSemiprime_of_windowedPrimeProductCount_pos hcountNat

/-! ## Stability of exceptional-set bounds under finite changes -/

/-- If `P n → Q n` beyond a fixed cutoff, the exceptions to `Q` up to `X`
are contained in the initial segment together with the exceptions to `P`. -/
theorem card_exceptionalUpTo_le_initial_add
    (P Q : ℕ → Prop) (N X : ℕ)
    (himp : ∀ n, N ≤ n → P n → Q n) :
    (exceptionalUpTo Q X).card ≤
      N + (exceptionalUpTo P X).card := by
  classical
  have hsubset : exceptionalUpTo Q X ⊆
      Finset.range N ∪ exceptionalUpTo P X := by
    intro n hn
    have hnQ := Finset.mem_filter.mp hn
    by_cases hnN : N ≤ n
    · rw [Finset.mem_union]
      right
      rw [exceptionalUpTo, Finset.mem_filter]
      refine ⟨hnQ.1, ?_⟩
      intro hPn
      exact hnQ.2 (himp n hnN hPn)
    · rw [Finset.mem_union]
      left
      exact Finset.mem_range.mpr (Nat.lt_of_not_ge hnN)
  calc
    (exceptionalUpTo Q X).card ≤
        (Finset.range N ∪ exceptionalUpTo P X).card :=
      Finset.card_le_card hsubset
    _ ≤ (Finset.range N).card + (exceptionalUpTo P X).card :=
      Finset.card_union_le _ _
    _ = N + (exceptionalUpTo P X).card := by simp

/-- The logarithmic exceptional-set majorant is eventually at least one,
for every real exponent `δ`. -/
theorem eventually_one_le_logPowerExceptionalMajorant (δ : ℝ) :
    ∀ᶠ X : ℕ in Filter.atTop,
      1 ≤ (X : ℝ) / (Real.log (X : ℝ)) ^ δ := by
  have hlo :=
    (isLittleO_log_rpow_rpow_atTop δ
      (by norm_num : (0 : ℝ) < 1)).comp_tendsto
      tendsto_natCast_atTop_atTop
  change (fun X : ℕ ↦ (Real.log (X : ℝ)) ^ δ) =o[Filter.atTop]
    (fun X : ℕ ↦ ((X : ℝ) ^ (1 : ℝ))) at hlo
  have hbound := hlo.bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hbound, Filter.eventually_ge_atTop (3 : ℕ)] with X hX hX3
  have hXpos : (0 : ℝ) < X := by
    exact_mod_cast (show 0 < X by omega)
  have hlogpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hdenpos : 0 < (Real.log (X : ℝ)) ^ δ :=
    Real.rpow_pos_of_pos hlogpos δ
  rw [Real.norm_of_nonneg hdenpos.le, Real.rpow_one,
    Real.norm_of_nonneg hXpos.le] at hX
  apply (le_div_iff₀ hdenpos).2
  simpa using hX

/-- A power-of-log exceptional-set estimate survives changing the underlying
property at finitely many integers. -/
theorem hasLogPowerExceptionalBound_of_imp_from
    (P Q : ℕ → Prop) {δ : ℝ} (N : ℕ)
    (himp : ∀ n, N ≤ n → P n → Q n)
    (hP : HasLogPowerExceptionalBound P δ) :
    HasLogPowerExceptionalBound Q δ := by
  rw [HasLogPowerExceptionalBound] at hP ⊢
  obtain ⟨c, hc⟩ := hP.bound
  apply Asymptotics.IsBigO.of_bound ((N : ℝ) + |c|)
  filter_upwards [hc, eventually_one_le_logPowerExceptionalMajorant δ]
    with X hPX hGX
  have hcardNat := card_exceptionalUpTo_le_initial_add P Q N X himp
  have hcard : ((exceptionalUpTo Q X).card : ℝ) ≤
      (N : ℝ) + ((exceptionalUpTo P X).card : ℝ) := by
    exact_mod_cast hcardNat
  have hQnonneg : 0 ≤ ((exceptionalUpTo Q X).card : ℝ) := by positivity
  have hPnonneg : 0 ≤ ((exceptionalUpTo P X).card : ℝ) := by positivity
  have hGnonneg :
      0 ≤ ‖(X : ℝ) / Real.log (X : ℝ) ^ δ‖ := norm_nonneg _
  have hcabs : c ≤ |c| := le_abs_self c
  rw [Real.norm_of_nonneg hPnonneg] at hPX
  rw [Real.norm_of_nonneg hQnonneg]
  have hGone :
      1 ≤ ‖(X : ℝ) / Real.log (X : ℝ) ^ δ‖ := by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (le_trans zero_le_one hGX)]
    exact hGX
  calc
    ((exceptionalUpTo Q X).card : ℝ)
        ≤ (N : ℝ) + ((exceptionalUpTo P X).card : ℝ) := hcard
    _ ≤ (N : ℝ) +
        |c| * ‖(X : ℝ) / Real.log (X : ℝ) ^ δ‖ := by
      have hpBound : ((exceptionalUpTo P X).card : ℝ) ≤
          |c| * ‖(X : ℝ) / Real.log (X : ℝ) ^ δ‖ :=
        hPX.trans (mul_le_mul_of_nonneg_right hcabs hGnonneg)
      linarith
    _ ≤ ((N : ℝ) + |c|) *
        ‖(X : ℝ) / Real.log (X : ℝ) ^ δ‖ := by
      nlinarith [show (0 : ℝ) ≤ (N : ℝ) by positivity, abs_nonneg c]

/-! ## The quantitative conclusion already contains existence -/

/-- At a fixed admissible parameter, the prime-window exceptional-set bound
implies the semiprime-existence bound with the same saving exponent. -/
theorem parameterExistenceAt_of_parameterWindowCount
    {c Δ κ δ : ℝ} (hκ : 0 < κ)
    (hcount :
      HasLogPowerExceptionalBound
        (ParameterWindowCountProperty c Δ κ) δ) :
    HasLogPowerExceptionalBound (LogIntervalContainsSemiprime c) δ := by
  exact hasLogPowerExceptionalBound_of_imp_from
    (ParameterWindowCountProperty c Δ κ)
    (LogIntervalContainsSemiprime c) 2
    (fun n hn ↦ logIntervalContainsSemiprime_of_parameterWindowCount hn hκ)
    hcount

/-- The quantitative prime-window statement implies the existence statement
for every `c > 3688/1763`.  Up to `21/10` we use a window at the same `c`; above
`21/10` we use the endpoint window and enlarge the interval. -/
theorem parameterExistence_of_parameterWindowCount
    (h : ParameterWindowCountStatement) : ParameterExistenceStatement := by
  intro c hc
  by_cases hcUpper : c ≤ (21 : ℝ) / 10
  · let Δ : ℝ := (c - (3688 : ℝ) / 1763) / 2
    have hΔ : 0 < Δ := by
      dsimp [Δ]
      linarith
    have hwindow : (1925 : ℝ) / 1763 < c - 1 - Δ := by
      dsimp [Δ]
      linarith
    obtain ⟨κ, δ, hκ, hδ, hcount⟩ :=
      h c hc hcUpper Δ hΔ hwindow
    exact ⟨δ, hδ,
      parameterExistenceAt_of_parameterWindowCount hκ hcount⟩
  · have hcEndpoint : (21 : ℝ) / 10 < c := lt_of_not_ge hcUpper
    obtain ⟨κ, δ, hκ, hδ, hcount⟩ :=
      h ((21 : ℝ) / 10) (by norm_num) (by norm_num)
        ((1 : ℝ) / 10000) (by norm_num) (by norm_num)
    have hendpoint :
        HasLogPowerExceptionalBound
          (LogIntervalContainsSemiprime ((21 : ℝ) / 10)) δ :=
      parameterExistenceAt_of_parameterWindowCount hκ hcount
    refine ⟨δ, hδ, ?_⟩
    exact hasLogPowerExceptionalBound_of_imp_from
      (LogIntervalContainsSemiprime ((21 : ℝ) / 10))
      (LogIntervalContainsSemiprime c) 3
      (fun n hn hsemi ↦ by
        have hthree : (1 : ℝ) ≤ Real.log 3 := by
          have hlogThree := Real.log_three_gt_d9
          norm_num at hlogThree ⊢
          linarith
        have hncast : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hlog : Real.log 3 ≤ Real.log (n : ℝ) := by
          exact Real.strictMonoOn_log.monotoneOn (by norm_num)
            (show (0 : ℝ) < (n : ℝ) by positivity) hncast
        exact Completion.logIntervalContainsSemiprime_mono
          (hthree.trans hlog) hcEndpoint.le hsemi)
      hendpoint

/-- Consequently the complete parameter theorem is equivalent to proving
its quantitative prime-window half. -/
theorem parameterTheorem_of_parameterWindowCount
    (h : ParameterWindowCountStatement) : ParameterTheoremStatement :=
  ⟨parameterExistence_of_parameterWindowCount h, h⟩

/-! ## The dyadic analytic interface -/

/-- The blockwise form of the quantitative conclusion.  This is the precise
local statement delivered by the variance, long-average, Chebyshev, and
real-to-integer argument on scales `[2^k,2^(k+1)]`. -/
def ParameterDyadicWindowCountStatement : Prop :=
  ∀ c : ℝ, (3688 : ℝ) / 1763 < c → c ≤ (21 : ℝ) / 10 →
    ∀ Δ : ℝ, 0 < Δ → (1925 : ℝ) / 1763 < c - 1 - Δ →
      ∃ κ δ : ℝ, 0 < κ ∧ 0 < δ ∧
        (fun k : ℕ ↦
          ((exceptionalOnDyadicBlock
            (ParameterWindowCountProperty c Δ κ) (2 ^ k)).card : ℝ))
          =O[Filter.atTop] Completion.dyadicLogPowerMajorant δ

/-- Quantitative dyadic globalization loses no logarithmic power, so the
blockwise analytic statement implies the global prime-window theorem. -/
theorem parameterWindowCount_of_dyadicWindowCount
    (h : ParameterDyadicWindowCountStatement) :
    ParameterWindowCountStatement := by
  intro c hc hcUpper Δ hΔ hwindow
  obtain ⟨κ, δ, hκ, hδ, hlocal⟩ :=
    h c hc hcUpper Δ hΔ hwindow
  exact ⟨κ, δ, hκ, hδ,
    Completion.hasLogPowerExceptionalBound_of_dyadic_logPower
      (ParameterWindowCountProperty c Δ κ) hδ hlocal⟩

/-- End-to-end deterministic final assembly: after the local dyadic analytic
estimate is supplied, all globalization, interval monotonicity, and
existence deductions are already formalized. -/
theorem parameterTheorem_of_dyadicWindowCount
    (h : ParameterDyadicWindowCountStatement) : ParameterTheoremStatement :=
  parameterTheorem_of_parameterWindowCount
    (parameterWindowCount_of_dyadicWindowCount h)

def parameterTheoremModule : ProofModule :=
  { name := "Results.ParameterTheorem"
    paperLocation := "Theorem 1.3"
    purpose :=
      "Globalize the dyadic prime-window estimate, deduce existence for every c > 3688/1763 from the quantitative half, and package Theorem 1.3."
    dependsOn :=
      [ "Completion.DyadicGlobalization",
        "Completion.IntervalMonotonicity",
        "Sparse.EndpointAlgebra" ]
    status := .proved }

end Results
end ExactSemiprimes
