import ExactSemiprimes.Assumptions

/-!
# The Halasz--Montgomery specialization used for a Type-II factor

This file changes the line of evaluation, but not the content, of
Iwaniec--Kowalski, Theorem 9.6.  A polynomial

`M(s) = \sum_{m \sim M} beta_m m^{-s}`

on `Re(s)=1` is the zero-line polynomial with coefficient
`a_m = beta_m / m`, extended by zero outside `(M,2M]`.  We prove the exact
finite-sum identity, identify and bound its coefficient energy, and then
invoke the typed external theorem.  This is the normalization used in the
`T_1` part of Matomaki--Teravainen, Proposition 5.1.
-/

namespace ExactSemiprimes
namespace TypeII

open scoped BigOperators

noncomputable section

/-- The coefficient `beta_n/n` on `(M,2M]`, extended by zero. -/
def halaszMontgomeryDyadicCoefficient
    (beta : ℕ → ℂ) (M : ℝ) (n : ℕ) : ℂ :=
  if n ∈ dyadicInterval M then beta n / (n : ℂ) else 0

@[simp]
theorem halaszMontgomeryDyadicCoefficient_of_mem
    {beta : ℕ → ℂ} {M : ℝ} {n : ℕ} (hn : n ∈ dyadicInterval M) :
    halaszMontgomeryDyadicCoefficient beta M n = beta n / (n : ℂ) := by
  simp [halaszMontgomeryDyadicCoefficient, hn]

@[simp]
theorem halaszMontgomeryDyadicCoefficient_of_not_mem
    {beta : ℕ → ℂ} {M : ℝ} {n : ℕ} (hn : n ∉ dyadicInterval M) :
    halaszMontgomeryDyadicCoefficient beta M n = 0 := by
  simp [halaszMontgomeryDyadicCoefficient, hn]

/-- The dyadic support is contained in the initial interval to which
Theorem 9.6 is applied, with length parameter `2M`. -/
theorem dyadicInterval_subset_initial_two_mul
    {M : ℝ} (hM : 0 ≤ M) :
    dyadicInterval M ⊆ natOpenClosedInterval 0 (2 * M) := by
  intro n hn
  rw [mem_dyadicInterval hM] at hn
  rw [mem_natOpenClosedInterval (by norm_num) (by positivity)]
  exact ⟨hM.trans_lt hn.1, hn.2⟩

/-- Termwise line-change identity: `(beta_n/n)n^{-it}` is
`beta_n n^{-(1+it)}`. -/
theorem halaszMontgomery_term_identity
    {beta : ℕ → ℂ} {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (beta n / (n : ℂ)) * (n : ℂ) ^ (-((t : ℂ) * Complex.I)) =
      beta n * (n : ℂ) ^ (-onePlusIT t) := by
  have hnzero : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hexponent :
      -onePlusIT t = (-1 : ℂ) + (-((t : ℂ) * Complex.I)) := by
    simp only [onePlusIT]
    ring
  rw [hexponent, Complex.cpow_add _ _ hnzero, Complex.cpow_neg_one]
  field_simp [hnzero]

/-- Exact polynomial identity connecting the zero-line normalization in
Theorem 9.6 to the paper's line-one dyadic polynomial. -/
theorem initialPolynomial_halaszMontgomeryDyadicCoefficient_eq
    (beta : ℕ → ℂ) {M : ℝ} (hM : 0 ≤ M) (t : ℝ) :
    matomakiTeravainenInitialDirichletPolynomial
        (halaszMontgomeryDyadicCoefficient beta M) (2 * M)
        ((t : ℂ) * Complex.I) =
      dyadicDirichletPolynomial beta M (onePlusIT t) := by
  classical
  simp only [matomakiTeravainenInitialDirichletPolynomial,
    dyadicDirichletPolynomial, dirichletPolynomial]
  rw [← Finset.sum_subset (dyadicInterval_subset_initial_two_mul hM)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [halaszMontgomeryDyadicCoefficient_of_mem hn]
    have hnrange := (mem_dyadicInterval hM).mp hn
    have hnpos : 0 < n := by
      exact_mod_cast hM.trans_lt hnrange.1
    exact halaszMontgomery_term_identity hnpos t
  · intro n hnInitial hnNotDyadic
    simp [halaszMontgomeryDyadicCoefficient_of_not_mem hnNotDyadic]

/-! ## Coefficient energy -/

/-- The squared coefficient norm occurring after the line change. -/
def halaszMontgomeryDyadicEnergy (beta : ℕ → ℂ) (M : ℝ) : ℝ :=
  ∑ n ∈ dyadicInterval M, ‖beta n / (n : ℂ)‖ ^ (2 : ℕ)

/-- The energy over the initial interval in Theorem 9.6 is exactly the
dyadic line-one energy: the zero extension contributes nothing. -/
theorem initialEnergy_halaszMontgomeryDyadicCoefficient_eq
    (beta : ℕ → ℂ) {M : ℝ} (hM : 0 ≤ M) :
    (∑ n ∈ natOpenClosedInterval 0 (2 * M),
        ‖halaszMontgomeryDyadicCoefficient beta M n‖ ^ (2 : ℕ)) =
      halaszMontgomeryDyadicEnergy beta M := by
  classical
  rw [halaszMontgomeryDyadicEnergy,
    ← Finset.sum_subset (dyadicInterval_subset_initial_two_mul hM)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [halaszMontgomeryDyadicCoefficient_of_mem hn]
  · intro n hnInitial hnNotDyadic
    simp [halaszMontgomeryDyadicCoefficient_of_not_mem hnNotDyadic]

/-- A soft but explicit cardinality bound for `(M,2M]`. -/
theorem card_dyadicInterval_le_two_mul {M : ℝ} (hM : 0 ≤ M) :
    ((dyadicInterval M).card : ℝ) ≤ 2 * M := by
  have hcardNat : (dyadicInterval M).card ≤ ⌊2 * M⌋₊ := by
    simp only [dyadicInterval, Nat.card_Ioc]
    exact Nat.sub_le _ _
  have hcast : ((dyadicInterval M).card : ℝ) ≤ (⌊2 * M⌋₊ : ℝ) := by
    exact_mod_cast hcardNat
  exact hcast.trans (Nat.floor_le (by positivity))

/-- If `|beta_n|≤K` on the dyadic interval, then the zero-line coefficient
`beta_n/n` has squared energy at most `2K²/M`.  This is the elementary
`1/M` energy saving used after Theorem 9.6. -/
theorem halaszMontgomeryDyadicEnergy_le
    {beta : ℕ → ℂ} {M K : ℝ} (hM : 0 < M) (hK : 0 ≤ K)
    (hbeta : ∀ n ∈ dyadicInterval M, ‖beta n‖ ≤ K) :
    halaszMontgomeryDyadicEnergy beta M ≤ 2 * K ^ 2 / M := by
  have hterm : ∀ n ∈ dyadicInterval M,
      ‖beta n / (n : ℂ)‖ ≤ K / M := by
    intro n hn
    have hnrange := (mem_dyadicInterval hM.le).mp hn
    have hnpos : 0 < (n : ℝ) := hM.le.trans_lt hnrange.1
    rw [norm_div]
    simp only [Complex.norm_natCast]
    apply (div_le_div_iff₀ hnpos hM).2
    calc
      ‖beta n‖ * M ≤ K * M :=
        mul_le_mul_of_nonneg_right (hbeta n hn) hM.le
      _ ≤ K * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hnrange.1.le hK
  rw [halaszMontgomeryDyadicEnergy]
  calc
    (∑ n ∈ dyadicInterval M, ‖beta n / (n : ℂ)‖ ^ (2 : ℕ)) ≤
        ∑ _n ∈ dyadicInterval M, (K / M) ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ (norm_nonneg _) (hterm n hn) 2
    _ = ((dyadicInterval M).card : ℝ) * (K / M) ^ (2 : ℕ) := by
      simp
    _ ≤ (2 * M) * (K / M) ^ (2 : ℕ) := by
      apply mul_le_mul_of_nonneg_right (card_dyadicInterval_le_two_mul hM.le)
      positivity
    _ = 2 * K ^ 2 / M := by
      field_simp

/-! ## Specialization of Iwaniec--Kowalski, Theorem 9.6 -/

/-- Theorem 9.6 after the exact zero-extension and line change.  No
coefficient estimate has yet been inserted: the last factor is precisely
the dyadic energy of `beta_n/n`. -/
theorem dyadicLineOne_meanSquare_le_of_iwaniecKowalskiNineSix
    (inputs : ExternalInputs) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M T : ℝ) (beta : ℕ → ℂ) (R : Finset ℝ),
        1 ≤ M → 1 ≤ T →
        (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
        IsOneSpaced (↑R : Set ℝ) →
        (∑ t ∈ R,
            ‖dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^
              (2 : ℕ)) ≤
          C * (2 * M + (R.card : ℝ) * T ^ (1 / 2 : ℝ)) *
            Real.log (2 * T) * halaszMontgomeryDyadicEnergy beta M := by
  rcases inputs.iwaniecKowalskiTheoremNineSix with ⟨C, hC, hIK⟩
  refine ⟨C, hC, ?_⟩
  intro M T beta R hM hT hR hspaced
  have hIK' := hIK (2 * M) T
    (halaszMontgomeryDyadicCoefficient beta M) R
    (by linarith) hT hR hspaced
  simpa [initialPolynomial_halaszMontgomeryDyadicCoefficient_eq beta
      (zero_le_one.trans hM),
    initialEnergy_halaszMontgomeryDyadicCoefficient_eq beta
      (zero_le_one.trans hM)] using hIK'

/-- The concrete bounded-coefficient form used in the `T_1` calculation.
The factor `2K²/M` is explicit rather than absorbed into logarithmic
notation. -/
theorem dyadicLineOne_meanSquare_le_of_norm_le
    (inputs : ExternalInputs) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M T K : ℝ) (beta : ℕ → ℂ) (R : Finset ℝ),
        1 ≤ M → 1 ≤ T → 0 ≤ K →
        (∀ n ∈ dyadicInterval M, ‖beta n‖ ≤ K) →
        (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
        IsOneSpaced (↑R : Set ℝ) →
        (∑ t ∈ R,
            ‖dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^
              (2 : ℕ)) ≤
          C * (2 * M + (R.card : ℝ) * T ^ (1 / 2 : ℝ)) *
            Real.log (2 * T) * (2 * K ^ 2 / M) := by
  rcases dyadicLineOne_meanSquare_le_of_iwaniecKowalskiNineSix inputs with
    ⟨C, hC, hIK⟩
  refine ⟨C, hC, ?_⟩
  intro M T K beta R hM hT hK hbeta hR hspaced
  calc
    (∑ t ∈ R,
        ‖dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^ (2 : ℕ)) ≤
        C * (2 * M + (R.card : ℝ) * T ^ (1 / 2 : ℝ)) *
          Real.log (2 * T) * halaszMontgomeryDyadicEnergy beta M :=
      hIK M T beta R hM hT hR hspaced
    _ ≤ C * (2 * M + (R.card : ℝ) * T ^ (1 / 2 : ℝ)) *
          Real.log (2 * T) * (2 * K ^ 2 / M) := by
      apply mul_le_mul_of_nonneg_left
        (halaszMontgomeryDyadicEnergy_le (zero_lt_one.trans_le hM) hK hbeta)
      have hsum : 0 ≤ 2 * M + (R.card : ℝ) * T ^ (1 / 2 : ℝ) := by
        positivity
      have hlog : 0 ≤ Real.log (2 * T) := by
        apply Real.log_nonneg
        linarith
      positivity

/-- Algebraically simplified version of the preceding estimate.  Its
central factor `2 + #R sqrt(T)/M` is the paper's
`1 + |T_1|T^(1/2)/M_2`, up to an absolute constant. -/
theorem dyadicLineOne_meanSquare_le_paperShape
    (inputs : ExternalInputs) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M T K : ℝ) (beta : ℕ → ℂ) (R : Finset ℝ),
        1 ≤ M → 1 ≤ T → 0 ≤ K →
        (∀ n ∈ dyadicInterval M, ‖beta n‖ ≤ K) →
        (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
        IsOneSpaced (↑R : Set ℝ) →
        (∑ t ∈ R,
            ‖dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^
              (2 : ℕ)) ≤
          2 * C * (2 + (R.card : ℝ) * T ^ (1 / 2 : ℝ) / M) *
            Real.log (2 * T) * K ^ 2 := by
  rcases dyadicLineOne_meanSquare_le_of_norm_le inputs with ⟨C, hC, hIK⟩
  refine ⟨C, hC, ?_⟩
  intro M T K beta R hM hT hK hbeta hR hspaced
  have hbound := hIK M T K beta R hM hT hK hbeta hR hspaced
  calc
    (∑ t ∈ R,
        ‖dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^ (2 : ℕ)) ≤
        C * (2 * M + (R.card : ℝ) * T ^ (1 / 2 : ℝ)) *
          Real.log (2 * T) * (2 * K ^ 2 / M) := hbound
    _ = 2 * C * (2 + (R.card : ℝ) * T ^ (1 / 2 : ℝ) / M) *
          Real.log (2 * T) * K ^ 2 := by
      field_simp

/-- The exact form of the Halasz--Montgomery step in Proposition 5.1:
the other Type-II factor is removed by its pointwise squared bound `S`.
Taking `S` to be the supremum over the ambient measurable set recovers the
display in the paper. -/
theorem typeIIProduct_meanSquare_le_paperShape
    (inputs : ExternalInputs) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M T K S : ℝ) (beta : ℕ → ℂ) (A : ℝ → ℂ) (R : Finset ℝ),
        1 ≤ M → 1 ≤ T → 0 ≤ K → 0 ≤ S →
        (∀ n ∈ dyadicInterval M, ‖beta n‖ ≤ K) →
        (∀ t ∈ R, ‖A t‖ ^ (2 : ℕ) ≤ S) →
        (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
        IsOneSpaced (↑R : Set ℝ) →
        (∑ t ∈ R,
            ‖A t * dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^
              (2 : ℕ)) ≤
          S * (2 * C *
            (2 + (R.card : ℝ) * T ^ (1 / 2 : ℝ) / M) *
            Real.log (2 * T) * K ^ 2) := by
  rcases dyadicLineOne_meanSquare_le_paperShape inputs with ⟨C, hC, hIK⟩
  refine ⟨C, hC, ?_⟩
  intro M T K S beta A R hM hT hK hS hbeta hA hR hspaced
  calc
    (∑ t ∈ R,
        ‖A t * dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^
          (2 : ℕ)) =
        ∑ t ∈ R, ‖A t‖ ^ (2 : ℕ) *
          ‖dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^
            (2 : ℕ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [norm_mul, mul_pow]
    _ ≤ ∑ t ∈ R, S *
          ‖dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^
            (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_right (hA t ht) (sq_nonneg _)
    _ = S * (∑ t ∈ R,
          ‖dyadicDirichletPolynomial beta M (onePlusIT t)‖ ^
            (2 : ℕ)) := by
      rw [Finset.mul_sum]
    _ ≤ S * (2 * C *
          (2 + (R.card : ℝ) * T ^ (1 / 2 : ℝ) / M) *
          Real.log (2 * T) * K ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (hIK M T K beta R hM hT hK hbeta hR hspaced) hS

def halaszMontgomeryModule : ProofModule :=
  { name := "TypeII.HalaszMontgomery"
    paperLocation :=
      "Proof of Proposition 5.1, Halasz--Montgomery treatment of T_1"
    purpose :=
      "Perform the exact line-one coefficient normalization and specialize Iwaniec--Kowalski Theorem 9.6, including the explicit dyadic energy bound."
    dependsOn := ["Assumptions.iwaniecKowalskiTheoremNineSix"]
    status := .proved }

end

end TypeII
end ExactSemiprimes
