import ExactSemiprimes.Assumptions

/-! # Coefficientwise transfer in the improved mean-value theorem

This file isolates the elementary bridge used in the complement-of-`U`
argument.  A pointwise majorant for a finite coefficient vector dominates
both its diagonal energy and the shifted correlations in MT23, Lemma 3.3.
No analytic estimate is assumed here.
-/

namespace ExactSemiprimes
namespace Completion

open MeasureTheory

noncomputable section

/-- Coefficientwise norm domination survives the zero extension used in
the shifted-correlation term of MT23, Lemma 3.3. -/
theorem zeroExtendedCoefficient_norm_le
    {a b : ℕ → ℂ} {N K : ℝ}
    (hab : ∀ n : ℕ, ‖a n‖ ≤ K * ‖b n‖) (m : ℤ) :
    ‖matomakiTeravainenZeroExtendedCoefficient a N m‖ ≤
      K * ‖matomakiTeravainenZeroExtendedCoefficient b N m‖ := by
  unfold matomakiTeravainenZeroExtendedCoefficient
  split_ifs with hm
  · exact hab m.toNat
  · simp

/-- A coefficientwise factor `K` costs `K²` in the diagonal energy. -/
theorem coefficientEnergy_le
    {a b : ℕ → ℂ} {N K : ℝ}
    (hab : ∀ n : ℕ, ‖a n‖ ≤ K * ‖b n‖) :
    (∑ n ∈ natOpenClosedInterval 0 N, ‖a n‖ ^ (2 : ℕ)) ≤
      K ^ (2 : ℕ) *
        ∑ n ∈ natOpenClosedInterval 0 N, ‖b n‖ ^ (2 : ℕ) := by
  calc
    (∑ n ∈ natOpenClosedInterval 0 N, ‖a n‖ ^ (2 : ℕ)) ≤
        ∑ n ∈ natOpenClosedInterval 0 N,
          (K * ‖b n‖) ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ (norm_nonneg _) (hab n) 2
    _ = K ^ (2 : ℕ) *
        ∑ n ∈ natOpenClosedInterval 0 N, ‖b n‖ ^ (2 : ℕ) := by
      simp only [mul_pow, Finset.mul_sum]

/-- A coefficientwise factor `K` also costs `K²` in every shifted
correlation appearing in MT23, Lemma 3.3. -/
theorem shiftedCorrelation_le
    {a b : ℕ → ℂ} {N T K : ℝ} (hK : 0 ≤ K)
    (hab : ∀ n : ℕ, ‖a n‖ ≤ K * ‖b n‖) :
    matomakiTeravainenShiftedCorrelation a N T ≤
      K ^ (2 : ℕ) * matomakiTeravainenShiftedCorrelation b N T := by
  unfold matomakiTeravainenShiftedCorrelation
  calc
    (∑ k ∈ matomakiTeravainenNonzeroIntegerShifts (N / T),
        ∑ n ∈ natOpenClosedInterval 0 N,
          ‖a n‖ *
            ‖matomakiTeravainenZeroExtendedCoefficient a N
              ((n : ℤ) + k)‖) ≤
      ∑ k ∈ matomakiTeravainenNonzeroIntegerShifts (N / T),
        ∑ n ∈ natOpenClosedInterval 0 N,
          (K * ‖b n‖) *
            (K * ‖matomakiTeravainenZeroExtendedCoefficient b N
              ((n : ℤ) + k)‖) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul (hab n)
        (zeroExtendedCoefficient_norm_le hab ((n : ℤ) + k))
        (norm_nonneg _)
        (mul_nonneg hK (norm_nonneg _))
    _ = K ^ (2 : ℕ) *
        (∑ k ∈ matomakiTeravainenNonzeroIntegerShifts (N / T),
          ∑ n ∈ natOpenClosedInterval 0 N,
            ‖b n‖ *
              ‖matomakiTeravainenZeroExtendedCoefficient b N
                ((n : ℤ) + k)‖) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro n hn
      ring

/-- MT23, Lemma 3.3 may be applied to a coefficient vector and then reduced
to any coefficientwise nonnegative majorant.  This is the exact elementary
step used with equation (2.4). -/
theorem lemmaThreeThree_of_coefficientMajorant
    (hmean : MatomakiTeravainenLemmaThreeThreeStatement)
    {a b : ℕ → ℂ} {N T K : ℝ}
    (hN : 1 ≤ N) (hT : 1 ≤ T) (hK : 0 ≤ K)
    (hab : ∀ n : ℕ, ‖a n‖ ≤ K * ‖b n‖) :
    ∃ C : ℝ, 0 < C ∧
      (∫ t in Set.Icc (-T) T,
          ‖matomakiTeravainenInitialDirichletPolynomial a N
              ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)) ≤
        C * K ^ (2 : ℕ) *
          (T * (∑ n ∈ natOpenClosedInterval 0 N,
              ‖b n‖ ^ (2 : ℕ)) +
            T * matomakiTeravainenShiftedCorrelation b N T) := by
  obtain ⟨C, hC, hmeanBound⟩ := hmean
  refine ⟨C, hC, ?_⟩
  have henergy := coefficientEnergy_le hab (N := N)
  have hcorrelation := shiftedCorrelation_le hK hab (N := N) (T := T)
  have hTnonneg : 0 ≤ T := zero_le_one.trans hT
  calc
    (∫ t in Set.Icc (-T) T,
        ‖matomakiTeravainenInitialDirichletPolynomial a N
            ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)) ≤
        C *
          (T * (∑ n ∈ natOpenClosedInterval 0 N,
              ‖a n‖ ^ (2 : ℕ)) +
            T * matomakiTeravainenShiftedCorrelation a N T) :=
      hmeanBound N T a hN hT
    _ ≤ C *
        (T * (K ^ (2 : ℕ) *
            ∑ n ∈ natOpenClosedInterval 0 N, ‖b n‖ ^ (2 : ℕ)) +
          T * (K ^ (2 : ℕ) *
            matomakiTeravainenShiftedCorrelation b N T)) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact add_le_add
        (mul_le_mul_of_nonneg_left henergy hTnonneg)
        (mul_le_mul_of_nonneg_left hcorrelation hTnonneg)
    _ = C * K ^ (2 : ℕ) *
          (T * (∑ n ∈ natOpenClosedInterval 0 N,
              ‖b n‖ ^ (2 : ℕ)) +
            T * matomakiTeravainenShiftedCorrelation b N T) := by ring

def roughCoefficientTransferModule : ProofModule :=
  { name := "Completion.RoughCoefficientTransfer"
    paperLocation := "MT23, Section 5, equation (2.4) followed by Lemma 3.3"
    purpose :=
      "Prove internally that a coefficientwise rough-number majorant controls both terms in the improved mean-value theorem."
    dependsOn := ["Assumptions.matomakiTeravainenLemmaThreeThree"]
    status := .proved }

end

end Completion
end ExactSemiprimes
