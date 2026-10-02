import ExactSemiprimes.Definitions

/-! # Monotonicity in the logarithmic interval exponent -/

namespace ExactSemiprimes
namespace Completion

/-- Once `log x ≥ 1`, increasing the exponent can only increase the
logarithmic interval length. -/
theorem logarithmicLength_mono_exponent {c d : ℝ} {x : ℕ}
    (hx : 1 ≤ Real.log (x : ℝ)) (hcd : c ≤ d) :
    logarithmicLength c x ≤ logarithmicLength d x := by
  exact Real.rpow_le_rpow_of_exponent_le hx hcd

/-- Enlarging the length of an interval `(x, x + h]` preserves all of its
natural-number members. -/
theorem shortInterval_mono {x h₁ h₂ : ℝ} (hh : h₁ ≤ h₂) :
    shortInterval x h₁ ⊆ shortInterval x h₂ := by
  intro n hn
  simp only [shortInterval, natOpenClosedInterval, Finset.mem_Ioc] at hn ⊢
  exact ⟨hn.1, hn.2.trans (Nat.floor_mono (add_le_add_right hh x))⟩

/-- A semiprime found in a shorter logarithmic interval remains in every
longer logarithmic interval obtained by increasing the exponent. -/
theorem logIntervalContainsSemiprime_mono {c d : ℝ} {x : ℕ}
    (hx : 1 ≤ Real.log (x : ℝ)) (hcd : c ≤ d)
    (h : LogIntervalContainsSemiprime c x) :
    LogIntervalContainsSemiprime d x := by
  obtain ⟨n, hn, hnSemi⟩ := h
  refine ⟨n, shortInterval_mono (logarithmicLength_mono_exponent hx hcd) hn, hnSemi⟩

def intervalMonotonicityModule : ProofModule :=
  { name := "Completion.IntervalMonotonicity"
    paperLocation := "After Theorem 1.3"
    purpose :=
      "Extend existence from one exponent below 2.1 to every larger exponent by Real.rpow monotonicity."
    dependsOn := ["Definitions"]
    status := .proved }

end Completion
end ExactSemiprimes
