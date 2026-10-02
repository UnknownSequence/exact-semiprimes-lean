import ExactSemiprimes.TypeII.ExtremeRanges
import ExactSemiprimes.Hybrid.HybridDensity

/-!
# Source-closed assembly of the tiny Type-II range

This module proves the two deterministic estimates omitted by the paper's
phrase that the tiny range is unchanged: the cardinality of a finite
one-spaced subset of `[0,T]`, and a uniform subpower pointwise estimate for
divisor-bounded dyadic Dirichlet polynomials. Their combination gives the
claimed `2*T^(-1/2)` discrete contribution without a new external input.
-/

namespace ExactSemiprimes
namespace TypeII

open Filter
open scoped BigOperators

noncomputable section

/-! ## Cardinality of a one-spaced set in `[0,T]` -/

theorem card_oneSpaced_le_two_mul
    {R : Finset ℝ} {T : ℝ} (hT : 1 ≤ T)
    (hR : ∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T)
    (hspaced : IsOneSpaced (↑R : Set ℝ)) :
    (R.card : ℝ) ≤ 2 * T := by
  classical
  let f : ℝ → ℕ := fun t ↦ ⌊t⌋₊
  have hinj : Set.InjOn f (↑R : Set ℝ) := by
    intro x hx y hy hfloor
    by_contra hxy
    have hxBounds := hR x hx
    have hyBounds := hR y hy
    have hxLower : (f x : ℝ) ≤ x := by
      exact Nat.floor_le hxBounds.1
    have hyLower : (f y : ℝ) ≤ y := by
      exact Nat.floor_le hyBounds.1
    have hxUpper : x < (f x : ℝ) + 1 := Nat.lt_floor_add_one x
    have hyUpper : y < (f y : ℝ) + 1 := Nat.lt_floor_add_one y
    have hfloorReal : (f x : ℝ) = (f y : ℝ) := by
      exact_mod_cast hfloor
    have hxyAbs : |x - y| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [hfloorReal]
    exact (not_lt_of_ge (hspaced hx hy hxy)) hxyAbs
  have himageSubset : R.image f ⊆ Finset.range (⌊T⌋₊ + 1) := by
    intro n hn
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
    rw [Finset.mem_range]
    have htBounds := hR t ht
    exact Nat.lt_succ_of_le (Nat.floor_mono htBounds.2)
  have hcardNat : R.card ≤ ⌊T⌋₊ + 1 := by
    calc
      R.card = (R.image f).card := (Finset.card_image_iff.mpr hinj).symm
      _ ≤ (Finset.range (⌊T⌋₊ + 1)).card :=
        Finset.card_le_card himageSubset
      _ = ⌊T⌋₊ + 1 := Finset.card_range _
  have hcardReal : (R.card : ℝ) ≤ (⌊T⌋₊ : ℝ) + 1 := by
    exact_mod_cast hcardNat
  calc
    (R.card : ℝ) ≤ (⌊T⌋₊ : ℝ) + 1 := hcardReal
    _ ≤ T + 1 := by
      simpa only [add_comm] using
        add_le_add_right (Nat.floor_le (zero_le_one.trans hT)) 1
    _ ≤ 2 * T := by linarith

/-! ## A uniform pointwise bound for divisor-bounded polynomials -/

theorem norm_cpow_neg_onePlusIT_eq_inv {n : ℕ} (hn : 0 < n) (t : ℝ) :
    ‖(n : ℂ) ^ (-onePlusIT t)‖ = ((n : ℝ)⁻¹) := by
  rw [Hybrid.cpow_neg_onePlusIT_eq_circleMap hn t]
  rw [norm_circleMap_zero, abs_of_pos]
  positivity

theorem norm_dyadicDirichletPolynomial_le_of_globalDivisorBound
    {a : ℕ → ℂ} {N A₀ B D rho : ℝ}
    (hN : 1 ≤ N) (hA₀ : 0 < A₀) (hrho : 0 < rho)
    (ha : IsDivisorBoundedByConstant B A₀ a)
    (hdiv : ∀ n : ℕ, 0 < n →
      (divisorCount n : ℝ) ^ B ≤ D * (n : ℝ) ^ rho)
    (t : ℝ) :
    ‖dyadicDirichletPolynomial a N (onePlusIT t)‖ ≤
      2 * A₀ * D * (2 : ℝ) ^ rho * N ^ rho := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hDnonneg : 0 ≤ D := by
    have hone := hdiv 1 (by omega)
    simpa using (le_trans (by positivity : 0 ≤ (divisorCount 1 : ℝ) ^ B) hone)
  have hterm : ∀ n ∈ dyadicInterval N,
      ‖a n * (n : ℂ) ^ (-onePlusIT t)‖ ≤
        A₀ * D * (2 * N) ^ rho / N := by
    intro n hn
    have hnrange := (mem_dyadicInterval (zero_le_one.trans hN)).mp hn
    have hnposReal : 0 < (n : ℝ) := hNpos.trans hnrange.1
    have hnpos : 0 < n := by exact_mod_cast hnposReal
    have hcoeff : ‖a n‖ ≤ A₀ * D * (n : ℝ) ^ rho := by
      calc
        ‖a n‖ ≤ A₀ * (divisorCount n : ℝ) ^ B := ha.2.2 n hnpos
        _ ≤ A₀ * (D * (n : ℝ) ^ rho) :=
          mul_le_mul_of_nonneg_left (hdiv n hnpos) hA₀.le
        _ = A₀ * D * (n : ℝ) ^ rho := by ring
    have hnrho : (n : ℝ) ^ rho ≤ (2 * N) ^ rho :=
      Real.rpow_le_rpow hnposReal.le hnrange.2 hrho.le
    rw [norm_mul, norm_cpow_neg_onePlusIT_eq_inv hnpos t]
    calc
      ‖a n‖ * (n : ℝ)⁻¹ ≤
          (A₀ * D * (n : ℝ) ^ rho) * (n : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hcoeff (inv_nonneg.mpr hnposReal.le)
      _ ≤ (A₀ * D * (2 * N) ^ rho) * N⁻¹ := by
        have hfirst : A₀ * D * (n : ℝ) ^ rho ≤
            A₀ * D * (2 * N) ^ rho := by
          exact mul_le_mul_of_nonneg_left hnrho
            (mul_nonneg hA₀.le hDnonneg)
        have hinv : (n : ℝ)⁻¹ ≤ N⁻¹ := by
          exact (inv_le_inv₀ hnposReal hNpos).2 hnrange.1.le
        exact mul_le_mul hfirst hinv (inv_nonneg.mpr hnposReal.le)
          (mul_nonneg (mul_nonneg hA₀.le hDnonneg)
            (Real.rpow_nonneg (by positivity) rho))
      _ = A₀ * D * (2 * N) ^ rho / N := by
        rw [div_eq_mul_inv]
  simp only [dyadicDirichletPolynomial, dirichletPolynomial]
  calc
    ‖∑ n ∈ dyadicInterval N, a n * (n : ℂ) ^ (-onePlusIT t)‖ ≤
        ∑ n ∈ dyadicInterval N,
          ‖a n * (n : ℂ) ^ (-onePlusIT t)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ dyadicInterval N,
          A₀ * D * (2 * N) ^ rho / N := by
      apply Finset.sum_le_sum
      intro n hn
      exact hterm n hn
    _ = ((dyadicInterval N).card : ℝ) *
          (A₀ * D * (2 * N) ^ rho / N) := by simp
    _ ≤ (2 * N) * (A₀ * D * (2 * N) ^ rho / N) := by
      apply mul_le_mul_of_nonneg_right
        (card_dyadicInterval_le_two_mul (zero_le_one.trans hN))
      positivity
    _ = 2 * A₀ * D * (2 : ℝ) ^ rho * N ^ rho := by
      rw [Real.mul_rpow (by norm_num) (zero_le_one.trans hN), div_eq_mul_inv]
      field_simp [ne_of_gt hNpos]

theorem eventually_norm_dyadicDirichletPolynomial_le_quarter
    {A₀ B : ℝ} (hA₀ : 0 < A₀) (hB : 0 ≤ B) :
    ∀ᶠ T : ℝ in atTop, ∀ (a : ℕ → ℂ) (N t : ℝ),
      IsDivisorBoundedByConstant B A₀ a →
      1 ≤ N → N ≤ T →
      ‖dyadicDirichletPolynomial a N (onePlusIT t)‖ ≤
        T ^ (1 / 4 : ℝ) := by
  let rho : ℝ := 1 / 16
  have hrho : 0 < rho := by norm_num [rho]
  obtain ⟨D, hD, hdiv⟩ := Hybrid.globalDivisorSubpower B rho hB hrho
  let K : ℝ := 2 * A₀ * D * (2 : ℝ) ^ rho
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hgap : 0 < (3 / 16 : ℝ) := by norm_num
  have hconst : ∀ᶠ T : ℝ in atTop, K ≤ T ^ (3 / 16 : ℝ) :=
    (tendsto_rpow_atTop hgap).eventually_ge_atTop K
  filter_upwards [eventually_ge_atTop (1 : ℝ), hconst] with T hT hconstT
  intro a N t ha hN hNT
  have hTnonneg : 0 ≤ T := zero_le_one.trans hT
  have hNbound := norm_dyadicDirichletPolynomial_le_of_globalDivisorBound
    hN hA₀ hrho ha hdiv t
  have hNrho : N ^ rho ≤ T ^ rho :=
    Real.rpow_le_rpow (zero_le_one.trans hN) hNT hrho.le
  calc
    ‖dyadicDirichletPolynomial a N (onePlusIT t)‖ ≤ K * N ^ rho := by
      simpa [K] using hNbound
    _ ≤ K * T ^ rho := mul_le_mul_of_nonneg_left hNrho hKnonneg
    _ ≤ T ^ (3 / 16 : ℝ) * T ^ rho :=
      mul_le_mul_of_nonneg_right hconstT (Real.rpow_nonneg hTnonneg rho)
    _ = T ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hT)]
      norm_num [rho]

/-! ## Source-closed discrete `R₃` estimate -/

theorem eventually_sum_smallExtremeRange_divisorBounded
    {A₀ B : ℝ} (hA₀ : 0 < A₀) (hB : 0 ≤ B) :
    ∀ᶠ T : ℝ in atTop,
      1 ≤ T ∧
      ∀ (a₁ a₂ : ℕ → ℂ) (N₁ N₂ : ℝ) (R : Finset ℝ),
        IsDivisorBoundedByConstant B A₀ a₁ →
        IsDivisorBoundedByConstant B A₀ a₂ →
        1 ≤ N₁ → N₁ ≤ T → 1 ≤ N₂ → N₂ ≤ T →
        (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
        IsOneSpaced (↑R : Set ℝ) →
        (∀ t ∈ R,
          ‖dyadicDirichletPolynomial a₁ N₁ (onePlusIT t)‖ ≤ T⁻¹ ∨
          ‖dyadicDirichletPolynomial a₂ N₂ (onePlusIT t)‖ ≤ T⁻¹) →
        ∑ t ∈ R,
            ‖dyadicDirichletPolynomial a₁ N₁ (onePlusIT t) *
              dyadicDirichletPolynomial a₂ N₂ (onePlusIT t)‖ ^ (2 : ℕ) ≤
          2 * T ^ (-1 / 2 : ℝ) := by
  have hpoint := eventually_norm_dyadicDirichletPolynomial_le_quarter hA₀ hB
  filter_upwards [eventually_ge_atTop (1 : ℝ), hpoint] with T hT hpointT
  refine ⟨hT, ?_⟩
  intro a₁ a₂ N₁ N₂ R ha₁ ha₂ hN₁ hN₁T hN₂ hN₂T hR hspaced hsmall
  apply sum_smallExtremeRange_le_two_mul_rpow_neg_half
    R
    (fun t ↦ dyadicDirichletPolynomial a₁ N₁ (onePlusIT t))
    (fun t ↦ dyadicDirichletPolynomial a₂ N₂ (onePlusIT t))
    hT (Real.rpow_nonneg (zero_le_one.trans hT) _)
  · exact card_oneSpaced_le_two_mul hT hR hspaced
  · exact le_rfl
  · intro t ht
    exact hpointT a₁ N₁ t ha₁ hN₁ hN₁T
  · intro t ht
    exact hpointT a₂ N₂ t ha₂ hN₂ hN₂T
  · exact hsmall

/-- Metadata for the complete discrete tiny-range estimate. -/
def extremeSmallAssemblyModule : ProofModule :=
  { name := "TypeII.ExtremeSmallAssembly"
    paperLocation :=
      "Proof of Proposition 5.1, tiny R₃ contribution"
    purpose :=
      "Bound a one-spaced set in [0,T] by 2T, derive a uniform T^(1/4) pointwise bound from the proved divisor-subpower theorem, and obtain the source-closed 2*T^(-1/2) R₃ estimate."
    dependsOn := ["TypeII.ExtremeRanges", "Hybrid.HybridDensity"]
    status := .proved }

end

end TypeII
end ExactSemiprimes

