import ExactSemiprimes.TypeII.FullTypeIIEstimate
import ExactSemiprimes.Sparse.Propagation
import ExactSemiprimes.Completion.StructuredVKDecay
import ExactSemiprimes.Assumptions

/-! # Closure of Type-II convolution components -/

namespace ExactSemiprimes
namespace Completion

open Filter Asymptotics
open scoped BigOperators

noncomputable section

/-! ## Exact identification of the structured Type-II factor -/

/-- The first factor in the source Type-II representation is exactly the
product of its short prime polynomials.  This is the finite-fibre identity
needed to feed the short-segment estimate into the convolution argument. -/
theorem representedStructuredFirstFactor_eq_shortPrimeProduct
    {delta M₁ t : ℝ} {R : ℕ} {Q : Fin R → ℝ}
    {alpha : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hR : 1 ≤ R)
    (hQ : ∀ j, 0 < Q j) (hprodQ : (∏ j, Q j) = M₁)
    (halpha : ∀ m, alpha m =
      matomakiTeravainenStructuredTypeIICoefficient delta R Q m) :
    dirichletPolynomial alpha
        (Sparse.typeIIFirstSupport delta M₁ R) (onePlusIT t) =
      structuredShortPrimeProduct Q delta t := by
  calc
    dirichletPolynomial alpha
        (Sparse.typeIIFirstSupport delta M₁ R) (onePlusIT t) =
      dirichletPolynomial
        (matomakiTeravainenStructuredTypeIICoefficient delta R Q)
        (Sparse.typeIIFirstSupport delta M₁ R) (onePlusIT t) := by
          unfold dirichletPolynomial
          apply Finset.sum_congr rfl
          intro m hm
          rw [halpha m]
    _ = structuredShortPrimeProduct Q delta t := by
      simpa [Sparse.typeIIFirstSupport] using
        structuredTypeIICoefficient_polynomial_eq_shortPrimeProduct
          hdelta hR hQ hprodQ

/-- If every short prime factor is at most `B ≤ 1`, then a nonempty
structured product is at most `B`. -/
theorem norm_structuredShortPrimeProduct_le_of_pointwise
    {R : ℕ} (Q : Fin R → ℝ) (delta t B : ℝ)
    (hR : 1 ≤ R) (hB0 : 0 ≤ B) (hB1 : B ≤ 1)
    (hfactor : ∀ j, ‖structuredShortPrimePolynomial (Q j) delta t‖ ≤ B) :
    ‖structuredShortPrimeProduct Q delta t‖ ≤ B := by
  let j₀ : Fin R := ⟨0, by omega⟩
  rw [structuredShortPrimeProduct, norm_prod,
    ← Finset.mul_prod_erase Finset.univ
      (fun j ↦ ‖structuredShortPrimePolynomial (Q j) delta t‖)
      (Finset.mem_univ j₀)]
  have hrest :
      ∏ j ∈ Finset.univ.erase j₀,
          ‖structuredShortPrimePolynomial (Q j) delta t‖ ≤ 1 := by
    calc
      ∏ j ∈ Finset.univ.erase j₀,
          ‖structuredShortPrimePolynomial (Q j) delta t‖ ≤
          ∏ _j ∈ Finset.univ.erase j₀, (1 : ℝ) := by
        exact Finset.prod_le_prod₀
          (fun j _ ↦ norm_nonneg
            (structuredShortPrimePolynomial (Q j) delta t))
          (fun j _ ↦ (hfactor j).trans hB1)
      _ = 1 := by simp
  calc
    ‖structuredShortPrimePolynomial (Q j₀) delta t‖ *
          ∏ j ∈ Finset.univ.erase j₀,
            ‖structuredShortPrimePolynomial (Q j) delta t‖ ≤
        B *
          ∏ j ∈ Finset.univ.erase j₀,
            ‖structuredShortPrimePolynomial (Q j) delta t‖ :=
      mul_le_mul_of_nonneg_right (hfactor j₀)
        (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
    _ ≤ B * 1 := mul_le_mul_of_nonneg_left hrest hB0
    _ = B := mul_one B

/-- Every fixed power of `log X` is absorbed by half of the
Vinogradov--Korobov exponential saving used for the structured Type-II
factor. -/
theorem eventually_logPower_mul_exp_neg_four_le_exp_neg_two (C : ℝ) :
    ∀ᶠ X : ℝ in atTop,
      (Real.log X) ^ C *
          Real.exp (-4 * (Real.log X) ^ (1 / 10 : ℝ)) ≤
        Real.exp (-2 * (Real.log X) ^ (1 / 10 : ℝ)) := by
  have hcpos : 0 < 1 / (|C| + 1) := by positivity
  have hlo := (isLittleO_log_rpow_atTop
    (by norm_num : (0 : ℝ) < 1 / 10)).bound hcpos
  have hbound : ∀ᶠ X : ℝ in atTop,
      ‖Real.log (Real.log X)‖ ≤
        (1 / (|C| + 1)) *
          ‖(Real.log X) ^ (1 / 10 : ℝ)‖ :=
    Real.tendsto_log_atTop.eventually hlo
  filter_upwards [hbound,
    eventually_ge_atTop (Real.exp (Real.exp 1))] with X hsmall hX
  have hXone : 1 < X :=
    (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hX
  have hlogX : 0 < Real.log X := Real.log_pos hXone
  have hloglogX : 0 ≤ Real.log (Real.log X) := by
    have hlogXge : Real.exp 1 ≤ Real.log X := by
      rw [← Real.log_exp (Real.exp 1)]
      exact Real.log_le_log (Real.exp_pos _) hX
    have : 1 ≤ Real.log X := by
      linarith [Real.exp_one_gt_two]
    exact Real.log_nonneg this
  have hrpow : 0 ≤ (Real.log X) ^ (1 / 10 : ℝ) :=
    Real.rpow_nonneg hlogX.le _
  rw [Real.norm_of_nonneg hloglogX,
    Real.norm_of_nonneg hrpow] at hsmall
  have hC : C * Real.log (Real.log X) ≤
      2 * (Real.log X) ^ (1 / 10 : ℝ) := by
    have habsC : C ≤ |C| := le_abs_self C
    have hmul := mul_le_mul_of_nonneg_right habsC hloglogX
    have hfrac : |C| * (1 / (|C| + 1)) ≤ 1 := by
      rw [mul_one_div]
      exact (div_le_one (by positivity)).2
        (by linarith [abs_nonneg C])
    calc
      C * Real.log (Real.log X) ≤
          |C| * Real.log (Real.log X) := hmul
      _ ≤ |C| * ((1 / (|C| + 1)) *
          (Real.log X) ^ (1 / 10 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsmall (abs_nonneg C)
      _ = (|C| * (1 / (|C| + 1))) *
          (Real.log X) ^ (1 / 10 : ℝ) := by ring
      _ ≤ 1 * (Real.log X) ^ (1 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_right hfrac hrpow
      _ ≤ 2 * (Real.log X) ^ (1 / 10 : ℝ) := by nlinarith
  rw [Real.rpow_def_of_pos hlogX, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

/-- Squaring the structured-factor bound doubles its exponential saving. -/
theorem sq_le_exp_neg_four_of_le_exp_neg_two
    {S Y : ℝ} (hS : 0 ≤ S)
    (hbound : S ≤ Real.exp (-2 * Y)) :
    S ^ (2 : ℕ) ≤ Real.exp (-4 * Y) := by
  calc
    S ^ (2 : ℕ) ≤ (Real.exp (-2 * Y)) ^ (2 : ℕ) :=
      pow_le_pow_left₀ hS hbound 2
    _ = Real.exp (-4 * Y) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- The precise surviving term in the upgraded Type-II estimate is therefore
still exponentially small, uniformly for every nonnegative `S` satisfying
the structured-factor estimate. -/
theorem eventually_structuredFactor_term_small (C : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ S : ℝ,
      0 ≤ S →
      S ≤ Real.exp (-2 * (Real.log X) ^ (1 / 10 : ℝ)) →
      (Real.log X) ^ C * S ^ (2 : ℕ) ≤
        Real.exp (-2 * (Real.log X) ^ (1 / 10 : ℝ)) := by
  filter_upwards [eventually_logPower_mul_exp_neg_four_le_exp_neg_two C,
    eventually_gt_atTop (1 : ℝ)] with X hmain hX
  intro S hS hstructured
  have hlognonneg : 0 ≤ Real.log X := Real.log_nonneg hX.le
  calc
    (Real.log X) ^ C * S ^ (2 : ℕ) ≤
        (Real.log X) ^ C *
          Real.exp (-4 * (Real.log X) ^ (1 / 10 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · exact sq_le_exp_neg_four_of_le_exp_neg_two hS hstructured
      · exact Real.rpow_nonneg hlognonneg C
    _ ≤ Real.exp (-2 * (Real.log X) ^ (1 / 10 : ℝ)) := hmain

/-- The fixed implied constant in MT23 equation (5.6) is harmless.  This
version corrects the normalization of the preceding convenience lemma:
the structured-factor bound supplied by the source is
`D * exp (-2 (log X)^(1/10))`, with a fixed `D`, rather than the same bound
with unit constant. -/
theorem eventually_logPower_mul_const_structuredBound_sq_small
    (C D : ℝ) :
    ∀ᶠ X : ℝ in atTop,
      (Real.log X) ^ C *
          (D * Real.exp (-2 * (Real.log X) ^ (1 / 10 : ℝ))) ^
            (2 : ℕ) ≤
        Real.exp (-2 * (Real.log X) ^ (1 / 10 : ℝ)) := by
  have hD : ∀ᶠ X : ℝ in atTop, D ^ (2 : ℕ) ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually_ge_atTop (D ^ (2 : ℕ))
  have hmain :=
    eventually_logPower_mul_exp_neg_four_le_exp_neg_two (C + 1)
  filter_upwards [hD, hmain,
    eventually_ge_atTop (Real.exp 1)] with X hDX hmainX hX
  have hlogpos : 0 < Real.log X := by
    have hXone : 1 < X := (Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hX
    exact Real.log_pos hXone
  have hlogC : 0 ≤ (Real.log X) ^ C :=
    Real.rpow_nonneg hlogpos.le _
  have hlogC1 :
      (Real.log X) ^ C * Real.log X =
        (Real.log X) ^ (C + 1) := by
    calc
      (Real.log X) ^ C * Real.log X =
          (Real.log X) ^ C * (Real.log X) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
      _ = (Real.log X) ^ (C + 1) :=
        (Real.rpow_add hlogpos C 1).symm
  have hcoefficient :
      D ^ (2 : ℕ) * (Real.log X) ^ C ≤
        (Real.log X) ^ (C + 1) := by
    calc
      D ^ (2 : ℕ) * (Real.log X) ^ C ≤
          Real.log X * (Real.log X) ^ C :=
        mul_le_mul_of_nonneg_right hDX hlogC
      _ = (Real.log X) ^ (C + 1) := by
        simpa [mul_comm] using hlogC1
  have hexpNonneg :
      0 ≤ Real.exp (-4 * (Real.log X) ^ (1 / 10 : ℝ)) :=
    (Real.exp_pos _).le
  calc
    (Real.log X) ^ C *
          (D * Real.exp (-2 * (Real.log X) ^ (1 / 10 : ℝ))) ^
            (2 : ℕ) =
        (D ^ (2 : ℕ) * (Real.log X) ^ C) *
          (Real.exp (-2 * (Real.log X) ^ (1 / 10 : ℝ))) ^
            (2 : ℕ) := by
      rw [mul_pow]
      ring
    _ =
        (D ^ (2 : ℕ) * (Real.log X) ^ C) *
          Real.exp (-4 * (Real.log X) ^ (1 / 10 : ℝ)) := by
      congr 1
      rw [← Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    _ ≤ (Real.log X) ^ (C + 1) *
          Real.exp (-4 * (Real.log X) ^ (1 / 10 : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoefficient hexpNonneg
    _ ≤ Real.exp (-2 * (Real.log X) ^ (1 / 10 : ℝ)) := hmainX

/-- Direct source-to-surviving-term bridge.  It specializes the exact
published equation (5.6), retains its fixed implied constant, squares the
bound, and absorbs both that constant and an arbitrary fixed logarithmic
power. -/
theorem eventually_structuredVK_survivingTerm_small
    (inputs : ExternalInputs) {epsilon A Clog : ℝ}
    (hepsilon : 0 < epsilon) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (M₁ t : ℝ) (R : ℕ) (Q : Fin R → ℝ),
        let z₀ : ℝ :=
          Real.exp
            (Real.log X / (Real.log (Real.log X)) ^ (3 : ℕ))
        let z : ℝ := X ^ (2 / 11 : ℝ)
        let delta : ℝ := (Real.log X) ^ (-10 * A)
        let T₀ : ℝ := X ^ (1 / 1000 : ℝ)
        1 ≤ R →
        R ≤ ⌊Real.log z / Real.log z₀⌋₊ →
        (∀ j : Fin R, z₀ ≤ Q j ∧ Q j < z) →
        (∏ j, Q j) = M₁ →
        X ^ (epsilon / 2) ≤ M₁ → M₁ ≤ z →
        T₀ ≤ t → t ≤ X →
        (Real.log X) ^ Clog *
            ‖structuredShortPrimeProduct Q delta t‖ ^ (2 : ℕ) ≤
          Real.exp (-2 * (Real.log X) ^ (1 / 10 : ℝ)) := by
  obtain ⟨X₀, D, hX₀, hD, hdecay⟩ :=
    structuredShortSegmentDecay_of_inputs inputs epsilon hepsilon A hA
  have habsorb :=
    eventually_logPower_mul_const_structuredBound_sq_small Clog D
  filter_upwards [habsorb, eventually_ge_atTop X₀] with X habsorbX hX
  intro M₁ t R Q
  dsimp only
  intro hR hRupper hQ hprod hMlower hMupper htLower htUpper
  have hbound := hdecay X M₁ t R Q hX hR hRupper hQ hprod
    hMlower hMupper htLower htUpper
  have hXthree : 3 ≤ X := hX₀.trans hX
  have hlogNonneg : 0 ≤ (Real.log X) ^ Clog :=
    Real.rpow_nonneg (Real.log_nonneg (by linarith)) _
  have hsquare :
      ‖structuredShortPrimeProduct Q
          ((Real.log X) ^ (-10 * A)) t‖ ^ (2 : ℕ) ≤
        (D * Real.exp
          (-2 * (Real.log X) ^ (1 / 10 : ℝ))) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hbound 2
  exact (mul_le_mul_of_nonneg_left hsquare hlogNonneg).trans habsorbX

def typeIIClosureModule : ProofModule :=
  { name := "Completion.TypeIIClosure"
    paperLocation := "Proof of Proposition 7.1, final Type-II paragraph"
    purpose :=
      "Prove the exact finite-fibre identity and the transport of MT23 equation (5.6) to the structured short-prime product. The parameter instantiation and assembly are carried out in Final/TypeIIComponent.lean."
    dependsOn :=
      [ "TypeII.FullTypeIIEstimate",
        "Sparse.Propagation",
        "Completion.StructuredPrimeFactors",
        "Completion.StructuredVKDecay",
        "Assumptions.matomakiTeravainenPropositionTwoTwo" ]
    status := .superseded }

end

end Completion
end ExactSemiprimes
