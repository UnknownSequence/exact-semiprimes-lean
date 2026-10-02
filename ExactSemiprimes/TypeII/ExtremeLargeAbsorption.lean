import ExactSemiprimes.TypeII.ExtremeLargeAssembly

/-!
# Uniform subpower absorption in the extreme-large branch

This file closes the remaining eventual-growth estimate in the `R₁`
argument.  All constants are fixed before the height and the dyadic scale;
the final estimate is uniform over every positive power in a prescribed
bounded range.
-/

namespace ExactSemiprimes
namespace TypeII

open Filter

noncomputable section

/-- For fixed coefficient constants and a fixed upper bound on the powering
order, the complete factor left over after the threshold loss is eventually
at most `T^(10*eps)`.  The subpower exponent in the convolution coefficient
is chosen to be `eps`.

The eventual lower threshold for `T` is chosen before `M` and `ell`, and
hence works uniformly for every `ell ≤ K` and every powered length
`M^ell ≤ T^2`. -/
theorem eventually_extreme_remaining_bound
    (C A₀ D : ℝ) (hC : 0 ≤ C) (hA₀ : 1 ≤ A₀) (hD : 1 ≤ D)
    (K : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ T : ℝ in atTop, ∀ (M : ℝ) (ell : ℕ),
      1 ≤ M → ell ≤ K → M ^ ell ≤ T ^ (2 : ℕ) →
      C * Real.log (2 * (2 * M) ^ ell) *
          ((1 + (2 : ℝ) ^ ell) * (2 : ℝ) ^ ell) *
          (A₀ ^ ell * D * ((2 * M) ^ ell) ^ eps) ^ (2 : ℕ) ≤
        T ^ (10 * eps) := by
  let Q : ℝ := A₀ ^ K * D
  have hQnonneg : 0 ≤ Q := by
    dsimp [Q]
    exact mul_nonneg (pow_nonneg (zero_le_one.trans hA₀) K)
      (zero_le_one.trans hD)
  have hfixed : ∀ᶠ T : ℝ in atTop, Q ≤ T ^ eps :=
    (tendsto_rpow_atTop heps).eventually_ge_atTop Q
  have hgeometric :=
    eventually_extreme_geometricFactor_le C hC K heps
  filter_upwards [hfixed, hgeometric,
      eventually_ge_atTop (max 1 ((2 : ℝ) ^ K))] with
      T hfixedT hgeometricT hT
  intro M ell hM hell hpow
  have hTOne : 1 ≤ T :=
    (le_max_left 1 ((2 : ℝ) ^ K)).trans hT
  have hTpos : 0 < T := zero_lt_one.trans_le hTOne
  have htwoK : (2 : ℝ) ^ K ≤ T :=
    (le_max_right 1 ((2 : ℝ) ^ K)).trans hT
  have hMnonneg : 0 ≤ M := zero_le_one.trans hM
  have hsupport :
      (2 * M) ^ ell ≤ (2 : ℝ) ^ K * T ^ (2 : ℕ) :=
    poweredSupport_le_of_exponent_bound hMnonneg hpow hell
  have hsupportCube : (2 * M) ^ ell ≤ T ^ (3 : ℕ) := by
    calc
      (2 * M) ^ ell ≤ (2 : ℝ) ^ K * T ^ (2 : ℕ) := hsupport
      _ ≤ T * T ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right htwoK (sq_nonneg T)
      _ = T ^ (3 : ℕ) := by ring
  have hsupportNonneg : 0 ≤ (2 * M) ^ ell := by positivity
  have hsupportRpow :
      ((2 * M) ^ ell) ^ eps ≤ T ^ (3 * eps) := by
    calc
      ((2 * M) ^ ell) ^ eps ≤ (T ^ (3 : ℕ)) ^ eps :=
        Real.rpow_le_rpow hsupportNonneg hsupportCube heps.le
      _ = T ^ (3 * eps) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
        norm_num
  have hAorder : A₀ ^ ell ≤ A₀ ^ K :=
    pow_le_pow_right₀ hA₀ hell
  have hAD : A₀ ^ ell * D ≤ Q := by
    dsimp [Q]
    exact mul_le_mul_of_nonneg_right hAorder (zero_le_one.trans hD)
  have hADnonneg : 0 ≤ A₀ ^ ell * D := by positivity
  have hB :
      A₀ ^ ell * D * ((2 * M) ^ ell) ^ eps ≤ T ^ (4 * eps) := by
    calc
      A₀ ^ ell * D * ((2 * M) ^ ell) ^ eps ≤
          Q * T ^ (3 * eps) :=
        mul_le_mul hAD hsupportRpow
          (Real.rpow_nonneg hsupportNonneg _) hQnonneg
      _ ≤ T ^ eps * T ^ (3 * eps) :=
        mul_le_mul_of_nonneg_right hfixedT
          (Real.rpow_nonneg hTpos.le _)
      _ = T ^ (4 * eps) := by
        rw [← Real.rpow_add hTpos]
        congr 1
        ring
  have hBnonneg :
      0 ≤ A₀ ^ ell * D * ((2 * M) ^ ell) ^ eps := by
    positivity
  have hBsq :
      (A₀ ^ ell * D * ((2 * M) ^ ell) ^ eps) ^ (2 : ℕ) ≤
        T ^ (8 * eps) := by
    calc
      (A₀ ^ ell * D * ((2 * M) ^ ell) ^ eps) ^ (2 : ℕ) ≤
          (T ^ (4 * eps)) ^ (2 : ℕ) :=
        pow_le_pow_left₀ hBnonneg hB 2
      _ = T ^ (8 * eps) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
        congr 1
        ring
  have hgeom := hgeometricT M ell hM hell hpow
  calc
    C * Real.log (2 * (2 * M) ^ ell) *
          ((1 + (2 : ℝ) ^ ell) * (2 : ℝ) ^ ell) *
          (A₀ ^ ell * D * ((2 * M) ^ ell) ^ eps) ^ (2 : ℕ) ≤
        T ^ (2 * eps) * T ^ (8 * eps) :=
      mul_le_mul hgeom hBsq (sq_nonneg _)
        (Real.rpow_nonneg hTpos.le _)
    _ = T ^ (10 * eps) := by
      rw [← Real.rpow_add hTpos]
      congr 1
      ring

/-- One-factor `R₁` bound after plugging the bounded-order convolution
estimate into the preceding eventual absorption.  The divisor-subpower
constant `D` is chosen before `A₀`, the coefficient sequence, the dyadic
scale, the height, and the powering order.  Only the eventual height
threshold may depend on the fixed displayed coefficient constant `A₀`. -/
theorem
    eventually_card_largePoweredDyadic_le_fifty_eps_of_divisorBounded_boundedOrder
    (hIK : IwaniecKowalskiTheoremNineFourStatement) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B₀ eps : ℝ) (K : ℕ),
        0 ≤ B₀ → 0 < eps → 1 ≤ K →
        ∃ D : ℝ, 1 ≤ D ∧
          ∀ A₀ : ℝ, 1 ≤ A₀ →
            ∀ᶠ T : ℝ in atTop, ∀ (a : ℕ → ℂ) (M : ℝ)
                (R : Finset ℝ),
              1 < M → M ≤ T →
              extremePowerExponent T M ≤ K →
              IsDivisorBoundedByConstant B₀ A₀ a →
              (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
              IsOneSpaced (↑R : Set ℝ) →
              (∀ t ∈ R,
                M ^ (-10 * eps) ≤
                  ‖dyadicDirichletPolynomial a M (onePlusIT t)‖) →
              (R.card : ℝ) ≤ T ^ (50 * eps) := by
  obtain ⟨C, hC, hfinal⟩ :=
    card_largePoweredDyadic_le_fifty_eps_of_remaining_bound hIK
  refine ⟨C, hC, ?_⟩
  intro B₀ eps K hB₀ heps hK
  obtain ⟨D, hD, hcoefficient⟩ :=
    exists_uniform_boundedOrder_powerConvolution_bound_subpower
      hB₀ hK heps
  refine ⟨D, hD, ?_⟩
  intro A₀ hA₀
  have hremaining :=
    eventually_extreme_remaining_bound C A₀ D hC.le hA₀ hD K heps
  filter_upwards [hremaining] with T hremainingT
  intro a M R hM hMT hellK ha hR hspaced hlarge
  let ell := extremePowerExponent T M
  let Bconv := A₀ ^ ell * D * ((2 * M) ^ ell) ^ eps
  have hT : 1 < T := hM.trans_le hMT
  have hell : 1 ≤ ell := extremePowerExponent_pos hT hM
  have hMpos : 0 < M := zero_lt_one.trans hM
  have hpow : M ^ ell ≤ T ^ (2 : ℕ) :=
    extremePowerExponent_pow_le_sq hT hM hMT
  have hBconv : 0 ≤ Bconv := by
    dsimp [Bconv]
    positivity
  have hcoeff :
      ∀ n ∈ (powerTuples (dyadicInterval M) ell).image tupleProduct,
        ‖powerConvolutionCoefficient a (dyadicInterval M) ell n‖ ≤
          Bconv := by
    exact hcoefficient ell hell hellK a M A₀ hMpos ha
  have hrem :
      C * Real.log (2 * (2 * M) ^ ell) *
            ((1 + (2 : ℝ) ^ ell) * (2 : ℝ) ^ ell) *
            Bconv ^ (2 : ℕ) ≤
          T ^ (10 * eps) := by
    exact hremainingT M ell hM.le hellK hpow
  exact hfinal a M T eps Bconv R hM hMT heps hBconv hR hspaced
    hlarge (by simpa [ell] using hcoeff) (by simpa [ell] using hrem)

/-- Uniform two-factor `R₁` corollary.  Both alternatives use the same
mean-value constant `C`, divisor-subpower constant `D`, and eventual height
threshold.  Filtering by the two alternatives preserves the height bound
and one-spacing; the union bound costs exactly the displayed factor `2`. -/
theorem
    eventually_card_extremePairPoints_le_two_mul_fifty_eps_of_divisorBounded_boundedOrder
    (hIK : IwaniecKowalskiTheoremNineFourStatement) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (B₀ eps : ℝ) (K : ℕ),
        0 ≤ B₀ → 0 < eps → 1 ≤ K →
        ∃ D : ℝ, 1 ≤ D ∧
          ∀ A₀ : ℝ, 1 ≤ A₀ →
            ∀ᶠ T : ℝ in atTop,
              ∀ (a₁ a₂ : ℕ → ℂ) (M₁ M₂ : ℝ) (R : Finset ℝ),
                1 < M₁ → M₁ ≤ T →
                1 < M₂ → M₂ ≤ T →
                extremePowerExponent T M₁ ≤ K →
                extremePowerExponent T M₂ ≤ K →
                IsDivisorBoundedByConstant B₀ A₀ a₁ →
                IsDivisorBoundedByConstant B₀ A₀ a₂ →
                (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
                IsOneSpaced (↑R : Set ℝ) →
                ((extremePairPoints R a₁ a₂ M₁ M₂ eps).card : ℝ) ≤
                  2 * T ^ (50 * eps) := by
  obtain ⟨C, hC, hone⟩ :=
    eventually_card_largePoweredDyadic_le_fifty_eps_of_divisorBounded_boundedOrder
      hIK
  refine ⟨C, hC, ?_⟩
  intro B₀ eps K hB₀ heps hK
  obtain ⟨D, hD, honeA⟩ := hone B₀ eps K hB₀ heps hK
  refine ⟨D, hD, ?_⟩
  intro A₀ hA₀
  filter_upwards [honeA A₀ hA₀] with T honeT
  intro a₁ a₂ M₁ M₂ R hM₁ hM₁T hM₂ hM₂T hell₁ hell₂
    ha₁ ha₂ hR hspaced
  let R₁ := extremeFactorPoints R a₁ M₁ eps
  let R₂ := extremeFactorPoints R a₂ M₂ eps
  have hsubset₁ : (↑R₁ : Set ℝ) ⊆ (↑R : Set ℝ) := by
    intro t ht
    exact (Finset.mem_filter.mp ht).1
  have hsubset₂ : (↑R₂ : Set ℝ) ⊆ (↑R : Set ℝ) := by
    intro t ht
    exact (Finset.mem_filter.mp ht).1
  have hcard₁ : (R₁.card : ℝ) ≤ T ^ (50 * eps) := by
    apply honeT a₁ M₁ R₁ hM₁ hM₁T hell₁ ha₁
    · intro t ht
      exact hR t (hsubset₁ ht)
    · exact Set.Pairwise.mono hsubset₁ hspaced
    · intro t ht
      exact (Finset.mem_filter.mp ht).2
  have hcard₂ : (R₂.card : ℝ) ≤ T ^ (50 * eps) := by
    apply honeT a₂ M₂ R₂ hM₂ hM₂T hell₂ ha₂
    · intro t ht
      exact hR t (hsubset₂ ht)
    · exact Set.Pairwise.mono hsubset₂ hspaced
    · intro t ht
      exact (Finset.mem_filter.mp ht).2
  exact card_extremePairPoints_le_two_mul
    (R := R) (a₁ := a₁) (a₂ := a₂) (M₁ := M₁) (M₂ := M₂)
    (eps := eps) (K := T ^ (50 * eps)) (by simpa [R₁] using hcard₁)
    (by simpa [R₂] using hcard₂)

def extremeLargeAbsorptionModule : ProofModule :=
  { name := "TypeII.ExtremeLargeAbsorption"
    paperLocation :=
      "Proof of Proposition 5.1, R₁: uniform subpower absorption"
    purpose :=
      "Absorb every fixed, logarithmic, support-expansion, and divisor-convolution loss uniformly over bounded powers, and prove the two-factor bound #R₁ ≤ 2*T^(50*eps)."
    dependsOn := ["TypeII.ExtremeLargeAssembly", "TypeII.PoweredMeanValue"]
    status := .proved }

end

end TypeII
end ExactSemiprimes
