import ExactSemiprimes.Sparse.PrimePowerPolynomial

/-! # Lower bound for Q(1+it) on the large-prime-polynomial set -/

namespace ExactSemiprimes
namespace Sparse

noncomputable section

/-- A real upper bound for `k` also bounds `k!` by the corresponding `k`th
power.  This elementary estimate is sufficient for the essential
`M^(1/a)` loss; Stirling is not needed for this part of the argument. -/
theorem factorial_cast_le_pow_of_natCast_le {k : ℕ} {L : ℝ}
    (hkL : (k : ℝ) ≤ L) :
    (k.factorial : ℝ) ≤ L ^ k := by
  calc
    (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
      exact_mod_cast Nat.factorial_le_pow k
    _ ≤ L ^ k := pow_le_pow_left₀ (Nat.cast_nonneg k) hkL k

/-- Convenient real-power form of the elementary factorial estimate.  It
isolates the remaining parameter comparison needed to show
`k! ≤ M^(1/a+ω)` in the sparse-polynomial application. -/
theorem factorial_cast_le_rpow_of_natCast_le
    {k : ℕ} {M d : ℝ} (hk : 0 < k) (hM : 0 < M)
    (hkM : (k : ℝ) ≤ M ^ (d / (k : ℝ))) :
    (k.factorial : ℝ) ≤ M ^ d := by
  calc
    (k.factorial : ℝ) ≤ (M ^ (d / (k : ℝ))) ^ k :=
      factorial_cast_le_pow_of_natCast_le hkM
    _ = M ^ d := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
      congr 1
      field_simp [Nat.cast_ne_zero.mpr (ne_of_gt hk)]

/-- A parameter form better adapted to the paper: if the chosen power `k`
is no larger than `P^(1/a)` and `M=P^k`, the elementary bound `k!≤k^k`
already gives the full `M^(1/a)` loss.  Thus Stirling is not needed for
this upper bound. -/
theorem factorial_cast_le_sparseScale
    {k : ℕ} {P M a : ℝ} (hP : 0 < P)
    (hkP : (k : ℝ) ≤ P ^ (1 / a)) (hM : M = P ^ k) :
    (k.factorial : ℝ) ≤ M ^ (1 / a) := by
  calc
    (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
      exact_mod_cast Nat.factorial_le_pow k
    _ ≤ (P ^ (1 / a)) ^ k :=
      pow_le_pow_left₀ (Nat.cast_nonneg k) hkP k
    _ = (P ^ k) ^ (1 / a) :=
      Real.rpow_pow_comm hP.le (1 / a) k
    _ = M ^ (1 / a) := by rw [hM]

/-- For the logarithmic choice `P=(log X)^a`, positive `a` makes
`P^(1/a)=log X` exactly. -/
theorem logPower_rpow_one_div {X a P : ℝ}
    (hX : 1 < X) (ha : 0 < a) (hP : P = (Real.log X) ^ a) :
    P ^ (1 / a) = Real.log X := by
  have hlog : 0 < Real.log X := Real.log_pos hX
  rw [hP, ← Real.rpow_mul hlog.le]
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hexp : a * (1 / a) = 1 := by field_simp
  rw [hexp, Real.rpow_one]

/-- Concrete factorial control for the paper's logarithmic parameters.
It isolates the elementary inequality `k≤log X`; the floor definition of
`k` supplies this once `log(2P)≥1`. -/
theorem factorial_cast_le_logPowerScale
    {k : ℕ} {X P M a : ℝ}
    (hX : 1 < X) (ha : 0 < a)
    (hP : P = (Real.log X) ^ a)
    (hkX : (k : ℝ) ≤ Real.log X)
    (hM : M = P ^ k) :
    (k.factorial : ℝ) ≤ M ^ (1 / a) := by
  apply factorial_cast_le_sparseScale (P := P) (M := M) (a := a)
  · rw [hP]
    exact Real.rpow_pos_of_pos (Real.log_pos hX) a
  · calc
      (k : ℝ) ≤ Real.log X := hkX
      _ = P ^ (1 / a) := (logPower_rpow_one_div hX ha hP).symm
  · exact hM

/-- The natural floor in the paper's definition of `k` is at most
`log X` as soon as its denominator is at least one. -/
theorem paperSparseExponent_le_log
    {X P : ℝ} (hlogX : 0 ≤ Real.log X)
    (hden : 1 ≤ Real.log (2 * P)) :
    ((⌊Real.log X / Real.log (2 * P)⌋₊ : ℕ) : ℝ) ≤
      Real.log X := by
  have hdenNonneg : 0 ≤ Real.log (2 * P) := zero_le_one.trans hden
  have hquotNonneg : 0 ≤ Real.log X / Real.log (2 * P) :=
    div_nonneg hlogX hdenNonneg
  calc
    ((⌊Real.log X / Real.log (2 * P)⌋₊ : ℕ) : ℝ) ≤
        Real.log X / Real.log (2 * P) := Nat.floor_le hquotNonneg
    _ ≤ Real.log X := div_le_self hlogX hden

/-- The factorial estimate for the literal floor choice made in Section 6.
The mild denominator hypothesis is eventually automatic for the paper's
polylogarithmic `P`. -/
theorem factorial_cast_le_paperSparseScale
    {X P M a : ℝ} (hX : 1 < X) (ha : 0 < a)
    (hP : P = (Real.log X) ^ a)
    (hden : 1 ≤ Real.log (2 * P))
    (hM : M = P ^ (⌊Real.log X / Real.log (2 * P)⌋₊ : ℕ)) :
    ((⌊Real.log X / Real.log (2 * P)⌋₊ : ℕ).factorial : ℝ) ≤
      M ^ (1 / a) := by
  exact factorial_cast_le_logPowerScale hX ha hP
    (paperSparseExponent_le_log (Real.log_pos hX).le hden) hM

/-- The value `z^k/k!` occurring in the sparse polynomial. -/
def factorialNormalizedPower (z : ℂ) (k : ℕ) : ℂ :=
  z ^ k / (k.factorial : ℂ)

@[simp]
theorem norm_factorialNormalizedPower (z : ℂ) (k : ℕ) :
    ‖factorialNormalizedPower z k‖ = ‖z‖ ^ k / (k.factorial : ℝ) := by
  simp [factorialNormalizedPower]

/-- If `r ≤ ‖z‖` and `k ≤ L`, then
`(r/L)^k ≤ ‖z^k/k!‖`.  This is the exact elementary inequality behind
equation (6.4) before substituting the paper's logarithmic parameters. -/
theorem div_pow_le_norm_factorialNormalizedPower {z : ℂ} {r L : ℝ}
    {k : ℕ} (hr : 0 ≤ r) (hrz : r ≤ ‖z‖) (hkL : (k : ℝ) ≤ L) :
    (r / L) ^ k ≤ ‖factorialNormalizedPower z k‖ := by
  rw [norm_factorialNormalizedPower, div_pow]
  apply div_le_div₀
  · positivity
  · exact pow_le_pow_left₀ hr hrz k
  · positivity
  · exact factorial_cast_le_pow_of_natCast_le hkL

/-- Raising a pointwise lower bound to the `k`th power is compatible with
the relation `M=P^k`, even when the exponent on `P` is real. -/
theorem rpow_le_norm_pow_of_pow_eq
    {z : ℂ} {P M r : ℝ} {k : ℕ}
    (hP : 0 < P) (hM : M = P ^ k)
    (hz : P ^ r ≤ ‖z‖) :
    M ^ r ≤ ‖z‖ ^ k := by
  calc
    M ^ r = (P ^ k) ^ r := by rw [hM]
    _ = (P ^ r) ^ k := (Real.rpow_pow_comm hP.le r k).symm
    _ ≤ ‖z‖ ^ k := pow_le_pow_left₀ (Real.rpow_nonneg hP.le r) hz k

/-- Abstract quotient step in the lower bound for `Q`: a lower bound for
the numerator power and an upper bound for `k!` combine with the correct
direction because the factorial occurs in the denominator. -/
theorem rpow_sub_le_norm_factorialNormalizedPower
    {z : ℂ} {M e d : ℝ} {k : ℕ}
    (hM : 0 < M)
    (hnumerator : M ^ (-e) ≤ ‖z‖ ^ k)
    (hfactorial : (k.factorial : ℝ) ≤ M ^ d) :
    M ^ (-e - d) ≤ ‖factorialNormalizedPower z k‖ := by
  rw [norm_factorialNormalizedPower, Real.rpow_sub hM]
  apply div_le_div₀
  · positivity
  · exact hnumerator
  · positivity
  · exact hfactorial

/-- Exact finite form of the lower bound for `|Q(1+it)|` (paper,
Section 6.1), given the factorial estimate `k! ≤ M^(1/a+ω)` as a
hypothesis.  The normalized prime power then has the essential loss
`M^(1/a)` and no coefficient normalization is omitted. -/
theorem paper_Q_lower_bound_of_factorial_estimate
    {z : ℂ} {P M ε a ω : ℝ} {k : ℕ}
    (hP : 0 < P) (hMdef : M = P ^ k) (hM : 0 < M)
    (hU : P ^ (-ε / 10) ≤ ‖z‖)
    (hfactorial : (k.factorial : ℝ) ≤ M ^ (1 / a + ω)) :
    M ^ (-ε / 10 - 1 / a - ω) ≤
      ‖factorialNormalizedPower z k‖ := by
  have hnum : M ^ (-ε / 10) ≤ ‖z‖ ^ k :=
    rpow_le_norm_pow_of_pow_eq hP hMdef hU
  have hnum' : M ^ (-(ε / 10)) ≤ ‖z‖ ^ k := by
    simpa only [neg_div] using hnum
  have hmain := rpow_sub_le_norm_factorialNormalizedPower
    (z := z) (M := M) (e := ε / 10) (d := 1 / a + ω) (k := k)
    hM hnum' hfactorial
  convert hmain using 1
  ring_nf

/-- The lower bound for `|Q(1+it)|` for the literal paper choice
`k=⌊log X/log(2P)⌋`.  The conclusion is slightly sharper than the displayed
`o(1)` form: under the explicit large-parameter condition
`log(2P)≥1`, the factorial costs at most `M^(1/a)` with no extra power. -/
theorem paper_Q_lower_bound_for_floor_choice
    {z : ℂ} {X P M ε a : ℝ}
    (hX : 1 < X) (ha : 0 < a)
    (hP : P = (Real.log X) ^ a)
    (hden : 1 ≤ Real.log (2 * P))
    (hMdef : M = P ^ (⌊Real.log X / Real.log (2 * P)⌋₊ : ℕ))
    (hU : P ^ (-ε / 10) ≤ ‖z‖) :
    M ^ (-ε / 10 - 1 / a) ≤
      ‖factorialNormalizedPower z
        (⌊Real.log X / Real.log (2 * P)⌋₊ : ℕ)‖ := by
  have hPpos : 0 < P := by
    rw [hP]
    exact Real.rpow_pos_of_pos (Real.log_pos hX) a
  have hMpos : 0 < M := by
    rw [hMdef]
    positivity
  have hfactorial := factorial_cast_le_paperSparseScale
    hX ha hP hden hMdef
  have hmain := paper_Q_lower_bound_of_factorial_estimate
    (z := z) (P := P) (M := M) (ε := ε) (a := a) (ω := 0)
    hPpos hMdef hMpos hU
    (by simpa using hfactorial)
  simpa using hmain

def qLowerBoundModule : ProofModule :=
  { name := "Sparse.QLowerBound"
    paperLocation := "Section 6.1, equation giving |Q(1+it)|"
    purpose :=
      "Prove the normalized-power lower bound, including the essential factorial/M^(1/a) loss, for the paper's floor choice of k."
    dependsOn := ["Sparse.PrimePowerPolynomial", "Mathlib factorial bound"]
    status := .proved }

end

end Sparse
end ExactSemiprimes
