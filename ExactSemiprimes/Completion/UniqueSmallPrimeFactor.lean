import ExactSemiprimes.Definitions

/-! # Uniqueness of the polylogarithmic prime factor -/

namespace ExactSemiprimes
namespace Completion

/-- If `n > X` and `U² ≤ X`, a factorization `n = p q` cannot have both
factors at most `U`.  Primality is not needed for this arithmetic core. -/
theorem not_both_factors_le_cutoff {X U : ℝ} {n p q : ℕ}
    (hXn : X < (n : ℝ)) (hU : U ^ 2 ≤ X) (hn : n = p * q) :
    ¬ ((p : ℝ) ≤ U ∧ (q : ℝ) ≤ U) := by
  rintro ⟨hpU, hqU⟩
  have hU_nonneg : 0 ≤ U := (Nat.cast_nonneg q).trans hqU
  have hnU : (n : ℝ) ≤ U ^ 2 := by
    calc
      (n : ℝ) = (p : ℝ) * (q : ℝ) := by simp [hn]
      _ ≤ U * U := mul_le_mul hpU hqU (Nat.cast_nonneg q) hU_nonneg
      _ = U ^ 2 := by ring
  exact (not_lt_of_ge (hnU.trans hU)) hXn

/-- In a displayed factorization above `X`, a factor at most `U` forces the
other factor to exceed `U`, provided `U² ≤ X`. -/
theorem other_factor_gt_cutoff {X U : ℝ} {n p q : ℕ}
    (hXn : X < (n : ℝ)) (hU : U ^ 2 ≤ X) (hn : n = p * q)
    (hpU : (p : ℝ) ≤ U) :
    U < (q : ℝ) := by
  exact lt_of_not_ge fun hqU ↦ not_both_factors_le_cutoff hXn hU hn ⟨hpU, hqU⟩

/-- For a semiprime written as `n = p q`, the prime factor at most `U` is
unique when `n > X ≥ U²`: every prime divisor of `n` below the cutoff is
the displayed factor `p`. -/
theorem unique_prime_factor_le_cutoff {X U : ℝ} {n p q r : ℕ}
    (hXn : X < (n : ℝ)) (hU : U ^ 2 ≤ X)
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hn : n = p * q) (hpU : (p : ℝ) ≤ U)
    (hrU : (r : ℝ) ≤ U) (hrn : r ∣ n) :
    r = p := by
  have hqU : U < (q : ℝ) := other_factor_gt_cutoff hXn hU hn hpU
  have hrpq : r ∣ p * q := by simpa [hn] using hrn
  rcases (hr.dvd_mul.mp hrpq) with hrp | hrq
  · exact (Nat.prime_dvd_prime_iff_eq hr hp).mp hrp
  · have hr_eq_q : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp hrq
    exact False.elim (not_le_of_gt hqU (hr_eq_q ▸ hrU))

def uniqueSmallPrimeFactorModule : ProofModule :=
  { name := "Completion.UniqueSmallPrimeFactor"
    paperLocation := "Section 7.2, distinctness of the counted products"
    purpose := "Prove that a semiprime near X has at most one factor in the selected small-prime window."
    dependsOn := ["Definitions"]
    status := .proved }

end Completion
end ExactSemiprimes
