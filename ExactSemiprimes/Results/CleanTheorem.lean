import ExactSemiprimes.Results.ParameterTheorem
import ExactSemiprimes.Results.ExplicitExponentArithmetic

/-!
# Explicit exponent `2.092` (paper Theorem 1.2)

The theorem's advertised conclusion is a lower bound of order
`(log x)^1.092` for products with a prime factor in
`((log x)^1.091, (log x)^1.092]`; existence is only its corollary.  Both
interfaces are recorded below.
-/

namespace ExactSemiprimes
namespace Results

/-- The quantitative existence assertion at the exact rational value
`2.092 = 523/250`. -/
def CleanExistenceStatement : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    HasLogPowerExceptionalBound
      (LogIntervalContainsSemiprime ((523 : ℝ) / 250)) δ

/-- The pointwise quantitative assertion in paper Theorem 1.2, with every
decimal represented by its exact rational value. -/
def CleanWindowCountProperty (κ : ℝ) (x : ℕ) : Prop :=
  κ * logarithmicLength ((273 : ℝ) / 250) x ≤
    (windowedPrimeProductCount
      (x : ℝ)
      (logarithmicLength ((523 : ℝ) / 250) x)
      (logarithmicLength ((1091 : ℝ) / 1000) x)
      (logarithmicLength ((273 : ℝ) / 250) x) : ℝ)

/-- The full quantitative counting conclusion of paper Theorem 1.2.  The
positive constant `κ` formalizes `c₀`, while `δ` is the power saving in the
exceptional-set estimate. -/
def CleanWindowCountStatement : Prop :=
  ∃ κ δ : ℝ, 0 < κ ∧ 0 < δ ∧
    HasLogPowerExceptionalBound (CleanWindowCountProperty κ) δ

/-- The complete target corresponding to paper Theorem 1.2. -/
def CleanTheoremStatement : Prop :=
  CleanExistenceStatement ∧ CleanWindowCountStatement

theorem cleanExistence_of_cleanTheorem
    (h : CleanTheoremStatement) : CleanExistenceStatement :=
  h.1

theorem cleanWindowCount_of_cleanTheorem
    (h : CleanTheoremStatement) : CleanWindowCountStatement :=
  h.2

/-- The clean existence statement is an exact specialization of the parameter
statement.  This theorem contains no analytic assumption beyond its explicit
hypothesis. -/
theorem cleanExistence_of_parameterExistence
    (h : ParameterExistenceStatement) : CleanExistenceStatement := by
  exact h ((523 : ℝ) / 250) (by norm_num)

/-- The numerical choice `c = 2.092`, `Δ = 0.0001` satisfies every
hypothesis of the quantitative parameter theorem. -/
theorem cleanParameterWindowBound_of_parameterWindowCount
    (h : ParameterWindowCountStatement) :
    ∃ κ δ : ℝ, 0 < κ ∧ 0 < δ ∧
      HasLogPowerExceptionalBound
        (ParameterWindowCountProperty
          ((523 : ℝ) / 250) ((1 : ℝ) / 10000) κ) δ := by
  exact h ((523 : ℝ) / 250) (by norm_num) (by norm_num)
    ((1 : ℝ) / 10000) (by norm_num) (by norm_num)

/-- For `x ≥ 2`, the lower bound in the clean prime window implies the
existence assertion pointwise. -/
theorem logIntervalContainsSemiprime_of_cleanWindowCount
    {κ : ℝ} {x : ℕ} (hx : 2 ≤ x) (hκ : 0 < κ)
    (hcount : CleanWindowCountProperty κ x) :
    LogIntervalContainsSemiprime ((523 : ℝ) / 250) x := by
  have hxReal : (1 : ℝ) < (x : ℝ) := by
    exact_mod_cast (show 1 < x by omega)
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos hxReal
  have hlength : 0 < logarithmicLength ((273 : ℝ) / 250) x := by
    exact Real.rpow_pos_of_pos hlog _
  have hcountReal :
      0 < (windowedPrimeProductCount
        (x : ℝ)
        (logarithmicLength ((523 : ℝ) / 250) x)
        (logarithmicLength ((1091 : ℝ) / 1000) x)
        (logarithmicLength ((273 : ℝ) / 250) x) : ℝ) :=
    (mul_pos hκ hlength).trans_le hcount
  have hcountNat :
      0 < windowedPrimeProductCount
        (x : ℝ)
        (logarithmicLength ((523 : ℝ) / 250) x)
        (logarithmicLength ((1091 : ℝ) / 1000) x)
        (logarithmicLength ((273 : ℝ) / 250) x) := by
    exact_mod_cast hcountReal
  exact logIntervalContainsSemiprime_of_windowedPrimeProductCount_pos hcountNat

/-- The parameter-window count at `c = 2.092` and `Δ = 0.0001` counts a
subwindow of the clean theorem's prime window.  This `Δ` is admissible because
`1.092 - 0.0001 > 1925/1763`.  Thus its pointwise lower bound specializes to the
clean lower bound once `log x ≥ 1`. -/
theorem cleanWindowCount_of_parameterWindowCount
    {κ : ℝ} {x : ℕ} (hx : 1 ≤ Real.log (x : ℝ))
    (hcount : ParameterWindowCountProperty
      ((523 : ℝ) / 250) ((1 : ℝ) / 10000) κ x) :
    CleanWindowCountProperty κ x := by
  have hLower :
      logarithmicLength ((1091 : ℝ) / 1000) x ≤
        logarithmicLength ((10919 : ℝ) / 10000) x :=
    Completion.logarithmicLength_mono_exponent hx (by norm_num)
  have hUpper :
      logarithmicLength ((21839 : ℝ) / 20000) x ≤
        logarithmicLength ((273 : ℝ) / 250) x :=
    Completion.logarithmicLength_mono_exponent hx (by norm_num)
  have hmono :
      windowedPrimeProductCount
          (x : ℝ)
          (logarithmicLength ((523 : ℝ) / 250) x)
          (logarithmicLength ((10919 : ℝ) / 10000) x)
          (logarithmicLength ((21839 : ℝ) / 20000) x) ≤
        windowedPrimeProductCount
          (x : ℝ)
          (logarithmicLength ((523 : ℝ) / 250) x)
          (logarithmicLength ((1091 : ℝ) / 1000) x)
          (logarithmicLength ((273 : ℝ) / 250) x) :=
    windowedPrimeProductCount_mono_window hLower hUpper
  norm_num [ParameterWindowCountProperty, CleanWindowCountProperty] at hcount ⊢
  exact hcount.trans (by exact_mod_cast hmono)

/-- For every integer `x≥3`, the parameter-window conclusion at
`c=2.092`, `Δ=10⁻⁴` implies the advertised clean-window conclusion. -/
theorem cleanWindowCount_of_parameterWindowCount_from_three
    {κ : ℝ} {x : ℕ} (hx : 3 ≤ x)
    (hcount : ParameterWindowCountProperty
      ((523 : ℝ) / 250) ((1 : ℝ) / 10000) κ x) :
    CleanWindowCountProperty κ x := by
  have hthree : (1 : ℝ) ≤ Real.log 3 := by
    have h := Real.log_three_gt_d9
    norm_num at h ⊢
    linarith
  have hxcast : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlog : Real.log 3 ≤ Real.log (x : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num)
      (show (0 : ℝ) < (x : ℝ) by linarith) hxcast
  exact cleanWindowCount_of_parameterWindowCount (hthree.trans hlog) hcount

/-- The quantitative clean-window theorem is a genuine consequence of the
parameter-window theorem, including the power-saving exceptional-set bound;
the finitely many values below `3` are absorbed explicitly. -/
theorem cleanWindowCountStatement_of_parameterWindowCount
    (h : ParameterWindowCountStatement) : CleanWindowCountStatement := by
  obtain ⟨κ, δ, hκ, hδ, hparam⟩ :=
    cleanParameterWindowBound_of_parameterWindowCount h
  refine ⟨κ, δ, hκ, hδ, ?_⟩
  exact hasLogPowerExceptionalBound_of_imp_from
    (ParameterWindowCountProperty
      ((523 : ℝ) / 250) ((1 : ℝ) / 10000) κ)
    (CleanWindowCountProperty κ) 3
    (fun n hn ↦ cleanWindowCount_of_parameterWindowCount_from_three hn)
    hparam

/-- Complete formal specialization of paper Theorem 1.3 to Theorem 1.2. -/
theorem cleanTheorem_of_parameterTheorem
    (h : ParameterTheoremStatement) : CleanTheoremStatement := by
  exact ⟨cleanExistence_of_parameterExistence h.1,
    cleanWindowCountStatement_of_parameterWindowCount h.2⟩

/-- Since the existence half of the parameter theorem follows from its
quantitative half, the prime-window statement alone already implies the full
advertised `2.092` theorem. -/
theorem cleanTheorem_of_parameterWindowCount
    (h : ParameterWindowCountStatement) : CleanTheoremStatement :=
  cleanTheorem_of_parameterTheorem
    (parameterTheorem_of_parameterWindowCount h)

def cleanTheoremModule : ProofModule :=
  { name := "Results.CleanTheorem"
    paperLocation := "Theorem 1.2"
    purpose :=
      "Specialize the parameter theorem to the c₀(log x)^1.092 clean window, preserve its exceptional-set bound, and deduce semiprime existence at exponent 2.092."
    dependsOn := ["Results.ParameterTheorem", "Results.ExplicitExponentArithmetic"]
    status := .proved }

end Results
end ExactSemiprimes
