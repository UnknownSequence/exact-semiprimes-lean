import ExactSemiprimes.Completion.TypeIIClosure
import ExactSemiprimes.TypeII.RealScaleNaturalization
import ExactSemiprimes.Sparse.PropagationParameters
import ExactSemiprimes.Sparse.GlobalComponentCancellation

/-!
# Deterministic instantiation of a source Type-II component

This file closes the endpoint and scale interfaces between the real scales
in MT23 Proposition 2.2(iii), the natural scales in the upgraded Type-II
estimate, and the dyadic factors used by sparse propagation.  It introduces
no analytic input.

The structured first factor is eventually narrow enough to fit wholly in
the natural dyadic block at `floor M₁`.  The arbitrary second factor needs
the exact two-block naturalization from `TypeII.RealScaleNaturalization`.
Consequently a source Type-II component is exactly a sum of two, rather than
one, natural-scale Type-II products.  The second summand is supported at a
single possible endpoint.
-/

namespace ExactSemiprimes
namespace Completion

open Filter MeasureTheory
open scoped BigOperators

noncomputable section

/-- Restrict an arbitrary sequence to the literal structured first support
from Proposition 2.2(iii). -/
def supportedTypeIIFirstCoefficient
    (delta M₁ : ℝ) (R : ℕ) (alpha : ℕ → ℂ) (m : ℕ) : ℂ :=
  if m ∈ Sparse.typeIIFirstSupport delta M₁ R then alpha m else 0

/-- Restriction to the structured support preserves the exact divisor-bound
witnesses. -/
theorem supportedTypeIIFirstCoefficient_isDivisorBoundedByConstant
    {delta M₁ B A : ℝ} {R : ℕ} {alpha : ℕ → ℂ}
    (halpha : IsDivisorBoundedByConstant B A alpha) :
    IsDivisorBoundedByConstant B A
      (supportedTypeIIFirstCoefficient delta M₁ R alpha) := by
  refine ⟨halpha.1, halpha.2.1, ?_⟩
  intro m hm
  by_cases hs : m ∈ Sparse.typeIIFirstSupport delta M₁ R
  · simpa [supportedTypeIIFirstCoefficient, hs] using halpha.2.2 m hm
  · simp only [supportedTypeIIFirstCoefficient, hs, ite_false, norm_zero]
    exact mul_nonneg halpha.2.1.le
      (Real.rpow_nonneg (Nat.cast_nonneg (divisorCount m)) B)

/-- A quantitative form of the endpoint reserve: a width at most `3/2`
fits below twice the floor as soon as the base scale is at least four. -/
theorem structuredUpper_le_two_floor
    {delta M₁ : ℝ} {R : ℕ}
    (hM₁ : 4 ≤ M₁) (hwidth : (1 + delta) ^ R ≤ 3 / 2) :
    (1 + delta) ^ R * M₁ ≤
      2 * (TypeII.naturalDyadicCoreScale M₁ : ℝ) := by
  have hfloor : M₁ - 1 < (TypeII.naturalDyadicCoreScale M₁ : ℝ) :=
    Nat.sub_one_lt_floor M₁
  have hMnonneg : 0 ≤ M₁ := by positivity
  calc
    (1 + delta) ^ R * M₁ ≤ (3 / 2 : ℝ) * M₁ :=
      mul_le_mul_of_nonneg_right hwidth hMnonneg
    _ ≤ 2 * (M₁ - 1) := by linarith
    _ ≤ 2 * (TypeII.naturalDyadicCoreScale M₁ : ℝ) := by
      linarith

/-- Under the preceding endpoint reserve, the literal narrow first support
is contained in the single natural dyadic block at `floor M₁`. -/
theorem typeIIFirstSupport_subset_naturalCore
    {delta M₁ : ℝ} {R : ℕ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁)
    (hupper : (1 + delta) ^ R * M₁ ≤
      2 * (TypeII.naturalDyadicCoreScale M₁ : ℝ)) :
    Sparse.typeIIFirstSupport delta M₁ R ⊆
      dyadicInterval (TypeII.naturalDyadicCoreScale M₁ : ℝ) := by
  intro m hm
  have hmRange := (Sparse.mem_typeIIFirstSupport_iff hdelta hM₁).mp hm
  apply (mem_dyadicInterval
    (Nat.cast_nonneg (TypeII.naturalDyadicCoreScale M₁))).mpr
  constructor
  · exact (Nat.floor_le hM₁.le).trans_lt hmRange.1
  · exact hmRange.2.trans hupper

/-- The structured first polynomial is exactly one natural-scale dyadic
polynomial; zero padding introduces no additional terms. -/
theorem supportedFirst_naturalPolynomial_eq
    {delta M₁ : ℝ} {R : ℕ} {alpha : ℕ → ℂ} {s : ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁)
    (hupper : (1 + delta) ^ R * M₁ ≤
      2 * (TypeII.naturalDyadicCoreScale M₁ : ℝ)) :
    dyadicDirichletPolynomial
        (supportedTypeIIFirstCoefficient delta M₁ R alpha)
        (TypeII.naturalDyadicCoreScale M₁ : ℝ) s =
      dirichletPolynomial alpha
        (Sparse.typeIIFirstSupport delta M₁ R) s := by
  classical
  have hsubset := typeIIFirstSupport_subset_naturalCore
    hdelta hM₁ hupper
  unfold dyadicDirichletPolynomial dirichletPolynomial
  symm
  apply Finset.sum_subset_zero_on_sdiff hsubset
  · intro m hm
    have hmnot : m ∉ Sparse.typeIIFirstSupport delta M₁ R :=
      (Finset.mem_sdiff.mp hm).2
    simp [supportedTypeIIFirstCoefficient, hmnot]
  · intro m hm
    simp [supportedTypeIIFirstCoefficient, hm]

/-- For the literal structured coefficient, the naturalized first block is
still exactly the short-prime product occurring in MT23 equation (5.6). -/
theorem naturalStructuredFirstFactor_eq_shortPrimeProduct
    {delta M₁ t : ℝ} {R : ℕ} {Q : Fin R → ℝ}
    (hdelta : 0 ≤ delta) (hR : 1 ≤ R)
    (hM₁ : 0 < M₁) (hQ : ∀ j, 0 < Q j)
    (hprodQ : (∏ j, Q j) = M₁)
    (hupper : (1 + delta) ^ R * M₁ ≤
      2 * (TypeII.naturalDyadicCoreScale M₁ : ℝ)) :
    dyadicDirichletPolynomial
        (supportedTypeIIFirstCoefficient delta M₁ R
          (matomakiTeravainenStructuredTypeIICoefficient delta R Q))
        (TypeII.naturalDyadicCoreScale M₁ : ℝ) (onePlusIT t) =
      structuredShortPrimeProduct Q delta t := by
  rw [supportedFirst_naturalPolynomial_eq hdelta hM₁ hupper]
  exact structuredTypeIICoefficient_polynomial_eq_shortPrimeProduct
    hdelta hR hQ hprodQ

/-- The complex zero-padded first coefficient is exactly the cast of the
real structured coefficient used by sparse propagation. -/
theorem supportedStructuredFirstCoefficient_eq_realCast
    {delta M₁ : ℝ} {R : ℕ} {Q : Fin R → ℝ} {m : ℕ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) :
    supportedTypeIIFirstCoefficient delta M₁ R
        (matomakiTeravainenStructuredTypeIICoefficient delta R Q) m =
      (Sparse.structuredTypeIIRealCoefficient delta M₁ R Q m : ℂ) := by
  rw [Sparse.structuredTypeIIRealCoefficient_cast]
  by_cases hm : m ∈ Sparse.typeIIFirstSupport delta M₁ R
  · have hrange := (Sparse.mem_typeIIFirstSupport_iff hdelta hM₁).mp hm
    simp [supportedTypeIIFirstCoefficient, hm, hrange]
  · have hrange : ¬ (M₁ < (m : ℝ) ∧
        (m : ℝ) ≤ (1 + delta) ^ R * M₁) := by
      intro hrange
      exact hm ((Sparse.mem_typeIIFirstSupport_iff hdelta hM₁).mpr hrange)
    simp [supportedTypeIIFirstCoefficient, hm, hrange]

/-- At the literal source scales, the stronger width `3/2` holds eventually
uniformly over every admissible structured multiplicity `R`. -/
theorem eventually_source_width_three_halves
    {A : ℝ} (hA : 0 < A) :
    ∀ᶠ X : ℝ in atTop, ∀ R : ℕ,
      R ≤ ⌊Real.log (X ^ (2 / 11 : ℝ)) /
          Real.log
            (Real.exp
              (Real.log X /
                (Real.log (Real.log X)) ^ (3 : ℕ)))⌋₊ →
      (1 + (Real.log X) ^ (-10 * A)) ^ R ≤ 3 / 2 := by
  -- Re-run the elementary exponential comparison with `log (3/2)` as the
  -- endpoint; the preceding eventual estimates already have that strength.
  have hlog : 0 < Real.log (3 / 2 : ℝ) := Real.log_pos (by norm_num)
  filter_upwards
      [eventually_gt_atTop (Real.exp 1),
        Sparse.eventually_loglog_cube_mul_log_rpow_neg_le hA hlog]
      with X hX hsmall
  intro R hR
  have hXpos : 0 < X := (Real.exp_pos 1).trans hX
  have hlogX : 1 < Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log (Real.exp_pos 1) hXpos hX
  have hloglog : 0 < Real.log (Real.log X) := Real.log_pos hlogX
  have hdelta : 0 ≤ (Real.log X) ^ (-10 * A) :=
    Real.rpow_nonneg (by linarith) _
  let K : ℝ := Real.log (X ^ (2 / 11 : ℝ)) /
    Real.log
      (Real.exp
        (Real.log X / (Real.log (Real.log X)) ^ (3 : ℕ)))
  have hK : K = (2 / 11 : ℝ) *
      (Real.log (Real.log X)) ^ (3 : ℕ) :=
    Sparse.source_structured_log_ratio_eq hX
  have hKnonneg : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (by norm_num) (pow_nonneg hloglog.le 3)
  have hRreal : (R : ℝ) ≤ K := by
    calc
      (R : ℝ) ≤ (⌊K⌋₊ : ℝ) := by exact_mod_cast hR
      _ ≤ K := Nat.floor_le hKnonneg
  have hsmallR :
      (R : ℝ) * (Real.log X) ^ (-10 * A) ≤
        Real.log (3 / 2 : ℝ) := by
    calc
      (R : ℝ) * (Real.log X) ^ (-10 * A) ≤
          K * (Real.log X) ^ (-10 * A) :=
        mul_le_mul_of_nonneg_right hRreal hdelta
      _ = (2 / 11 : ℝ) *
          ((Real.log (Real.log X)) ^ (3 : ℕ) *
            (Real.log X) ^ (-10 * A)) := by rw [hK]; ring
      _ ≤ (Real.log (Real.log X)) ^ (3 : ℕ) *
            (Real.log X) ^ (-10 * A) := by
        have hp : 0 ≤ (Real.log (Real.log X)) ^ (3 : ℕ) *
            (Real.log X) ^ (-10 * A) :=
          mul_nonneg (pow_nonneg hloglog.le 3) hdelta
        nlinarith
      _ ≤ Real.log (3 / 2 : ℝ) := hsmall
  have hbase : 1 + (Real.log X) ^ (-10 * A) ≤
      Real.exp ((Real.log X) ^ (-10 * A)) := by
    linarith [Real.add_one_le_exp ((Real.log X) ^ (-10 * A))]
  calc
    (1 + (Real.log X) ^ (-10 * A)) ^ R ≤
        (Real.exp ((Real.log X) ^ (-10 * A))) ^ R :=
      pow_le_pow_left₀ (by linarith) hbase R
    _ = Real.exp ((R : ℝ) * (Real.log X) ^ (-10 * A)) := by
      rw [← Real.exp_nat_mul]
    _ ≤ Real.exp (Real.log (3 / 2 : ℝ)) :=
      Real.exp_le_exp.mpr hsmallR
    _ = 3 / 2 := Real.exp_log (by norm_num)

/-- Exact two-product naturalization of a represented source Type-II
component. -/
theorem representedTypeII_eq_two_naturalProducts
    {delta M₁ M₂ : ℝ} {R : ℕ} {alpha beta f : ℕ → ℂ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 1 ≤ M₂)
    (hupper : (1 + delta) ^ R * M₁ ≤
      2 * (TypeII.naturalDyadicCoreScale M₁ : ℝ))
    (hf : ∀ n, f n =
      matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta n)
    (s : ℂ) :
    dirichletPolynomial f (Sparse.typeIIProductSupport delta M₁ M₂ R) s =
      dyadicDirichletPolynomial
          (supportedTypeIIFirstCoefficient delta M₁ R alpha)
          (TypeII.naturalDyadicCoreScale M₁ : ℝ) s *
        dyadicDirichletPolynomial beta
          (TypeII.naturalDyadicCoreScale M₂ : ℝ) s +
      dyadicDirichletPolynomial
          (supportedTypeIIFirstCoefficient delta M₁ R alpha)
          (TypeII.naturalDyadicCoreScale M₁ : ℝ) s *
        dyadicDirichletPolynomial
          (TypeII.dyadicBoundaryCoefficient beta M₂)
          (TypeII.naturalDyadicBoundaryScale M₂ : ℝ) s := by
  rw [Sparse.representedTypeII_polynomial_factorization hdelta hM₁
    (by linarith : 0 < M₂) hf]
  rw [← supportedFirst_naturalPolynomial_eq hdelta hM₁ hupper]
  rw [TypeII.dyadicDirichletPolynomial_realScale_eq_two_naturalScales
    hM₂]
  ring

/-- The complete coefficient package for the two natural products. -/
theorem representedTypeII_naturalCoefficients_divisorBounded
    {delta M₁ M₂ B A : ℝ} {R : ℕ} {alpha beta : ℕ → ℂ}
    (halpha : IsDivisorBoundedByConstant B A alpha)
    (hbeta : IsDivisorBoundedByConstant B A beta) :
    IsDivisorBoundedByConstant B A
        (supportedTypeIIFirstCoefficient delta M₁ R alpha) ∧
      IsDivisorBoundedByConstant B A beta ∧
      IsDivisorBoundedByConstant B A
        (TypeII.dyadicBoundaryCoefficient beta M₂) := by
  exact ⟨supportedTypeIIFirstCoefficient_isDivisorBoundedByConstant halpha,
    hbeta, TypeII.dyadicBoundaryCoefficient_isDivisorBoundedByConstant hbeta⟩

/-- Literal source product geometry after choosing either natural block for
the second factor. -/
theorem representedTypeII_naturalScale_product_window
    {X P M₁ M₂ : ℝ} (hP : 0 < P)
    (hM₁ : 2 ≤ M₁) (hM₂ : 2 ≤ M₂)
    (hlower : X / (2 * P) < M₁ * M₂)
    (hupper : M₁ * M₂ ≤ 4 * X / P)
    {N₂ : ℕ}
    (hN₂ : N₂ = TypeII.naturalDyadicCoreScale M₂ ∨
      N₂ = TypeII.naturalDyadicBoundaryScale M₂) :
    X / (8 * P) <
        (TypeII.naturalDyadicCoreScale M₁ : ℝ) * (N₂ : ℝ) ∧
      (TypeII.naturalDyadicCoreScale M₁ : ℝ) * (N₂ : ℝ) ≤
        16 * X / P := by
  have hcompare := TypeII.naturalDyadicScale_product_comparable
    hM₁ hM₂ (Or.inl rfl) hN₂
  constructor
  · have hdiv : X / (8 * P) < M₁ * M₂ / 4 := by
      convert (div_lt_div_of_pos_right hlower (by norm_num : (0 : ℝ) < 4)) using 1
      field_simp [ne_of_gt hP]
      ring
    exact hdiv.trans_le hcompare.1
  · calc
      (TypeII.naturalDyadicCoreScale M₁ : ℝ) * (N₂ : ℝ) ≤
          4 * (M₁ * M₂) := hcompare.2
      _ ≤ 4 * (4 * X / P) :=
        mul_le_mul_of_nonneg_left hupper (by norm_num)
      _ = 16 * X / P := by ring

/-- The source product lower bound forces the complementary scale above two
once the fixed logarithmic factor has been absorbed into the ambient
power. -/
theorem representedTypeII_secondScale_ge_two_of_reserve
    {X P M₁ M₂ : ℝ} (hP : 0 < P) (hM₁ : 0 < M₁)
    (hlower : X / (2 * P) < M₁ * M₂)
    (hreserve : 4 * P * M₁ ≤ X) :
    2 < M₂ := by
  have hden : 0 < 2 * P := by positivity
  have htwoM₁ : 2 * M₁ ≤ X / (2 * P) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have hprod : 2 * M₁ < M₁ * M₂ := htwoM₁.trans_lt hlower
  nlinarith

/-- All elementary floor and complementary-length reserves used below hold
eventually, uniformly in the moving source scales. -/
theorem eventually_sourceTypeII_naturalization_reserves
    (a : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ X : ℝ in atTop,
      4 ≤ X ^ (epsilon / 2) ∧
      2 * X ^ (epsilon / 5) ≤ X ^ (epsilon / 2) ∧
      4 * (Real.log X) ^ a * X ^ (2 / 11 : ℝ) ≤ X ∧
      4 ≤ Real.log X := by
  have hepsHalf : 0 < epsilon / 2 := by positivity
  have hepsGap : 0 < 3 * epsilon / 10 := by positivity
  have hnine : 0 < (9 / 22 : ℝ) := by norm_num
  have hhalfFour : ∀ᶠ X : ℝ in atTop, 4 ≤ X ^ (epsilon / 2) :=
    (tendsto_rpow_atTop hepsHalf).eventually_ge_atTop 4
  have hgapTwo : ∀ᶠ X : ℝ in atTop, 2 ≤ X ^ (3 * epsilon / 10) :=
    (tendsto_rpow_atTop hepsGap).eventually_ge_atTop 2
  have hlogPower := TypeII.eventually_log_rpow_le_rpow a hnine
  have hnineFour : ∀ᶠ X : ℝ in atTop, 4 ≤ X ^ (9 / 22 : ℝ) :=
    (tendsto_rpow_atTop hnine).eventually_ge_atTop 4
  have hlogFour : ∀ᶠ X : ℝ in atTop, 4 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually_ge_atTop 4
  filter_upwards [hhalfFour, hgapTwo, hlogPower, hnineFour,
      hlogFour, eventually_gt_atTop (1 : ℝ)] with
      X hhalf hgap hlogPow hnine4 hlog4 hX
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hfloorReserve :
      2 * X ^ (epsilon / 5) ≤ X ^ (epsilon / 2) := by
    calc
      2 * X ^ (epsilon / 5) ≤
          X ^ (3 * epsilon / 10) * X ^ (epsilon / 5) :=
        mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hXpos.le _)
      _ = X ^ (epsilon / 2) := by
        rw [← Real.rpow_add hXpos]
        congr 1
        ring
  have hfourLog :
      4 * (Real.log X) ^ a ≤ X ^ (9 / 11 : ℝ) := by
    calc
      4 * (Real.log X) ^ a ≤
          X ^ (9 / 22 : ℝ) * X ^ (9 / 22 : ℝ) :=
        mul_le_mul hnine4 hlogPow
          (Real.rpow_nonneg (Real.log_nonneg hX.le) _)
          (Real.rpow_nonneg hXpos.le _)
      _ = X ^ (9 / 11 : ℝ) := by
        rw [← Real.rpow_add hXpos]
        congr 1
        ring
  have hcomplementReserve :
      4 * (Real.log X) ^ a * X ^ (2 / 11 : ℝ) ≤ X := by
    calc
      4 * (Real.log X) ^ a * X ^ (2 / 11 : ℝ) ≤
          X ^ (9 / 11 : ℝ) * X ^ (2 / 11 : ℝ) :=
        mul_le_mul_of_nonneg_right hfourLog (Real.rpow_nonneg hXpos.le _)
      _ = X := by
        rw [← Real.rpow_add hXpos]
        norm_num
  exact ⟨hhalf, hfloorReserve, hcomplementReserve, hlog4⟩

/-- The first natural length inherits the lower and upper power ranges needed
by `TypeIIEstimateStatement`, after only the explicit factor-two reserve
caused by the floor. -/
theorem representedTypeII_firstNaturalScale_powerRange
    {X M₁ epsilon : ℝ}
    (hX : 1 ≤ X) (hepsilon : 0 ≤ epsilon) (hM₁ : 2 ≤ M₁)
    (hMlower : X ^ (epsilon / 2) ≤ M₁)
    (hMupper : M₁ ≤ X ^ (2 / 11 : ℝ))
    (hfloorReserve : 2 * X ^ (epsilon / 5) ≤ X ^ (epsilon / 2)) :
    X ^ (epsilon / 5) ≤
        (TypeII.naturalDyadicCoreScale M₁ : ℝ) ∧
      (TypeII.naturalDyadicCoreScale M₁ : ℝ) ≤
        X ^ (2 / 11 + epsilon) := by
  have hhalf := TypeII.half_le_naturalDyadicCoreScale hM₁
  have hfloorUpper :
      (TypeII.naturalDyadicCoreScale M₁ : ℝ) ≤ M₁ :=
    Nat.floor_le (by positivity)
  constructor
  · calc
      X ^ (epsilon / 5) ≤ X ^ (epsilon / 2) / 2 := by linarith
      _ ≤ M₁ / 2 := div_le_div_of_nonneg_right hMlower (by norm_num)
      _ ≤ (TypeII.naturalDyadicCoreScale M₁ : ℝ) := hhalf
  · calc
      (TypeII.naturalDyadicCoreScale M₁ : ℝ) ≤ M₁ := hfloorUpper
      _ ≤ X ^ (2 / 11 : ℝ) := hMupper
      _ ≤ X ^ (2 / 11 + epsilon) :=
        Real.rpow_le_rpow_of_exponent_le hX (by linarith)

/-- For `log X ≥ 4`, the absolute factor eight in the rounded lower
product window is absorbed by two extra logarithmic powers. -/
theorem logWindow_lower_roundingReserve
    {X a : ℝ} (hlog : 4 ≤ Real.log X) (_ha : 0 ≤ a) :
    (Real.log X) ^ (-(a + 2)) ≤
      1 / (8 * (Real.log X) ^ a) := by
  have hlogpos : 0 < Real.log X := by linarith
  have hloga : 0 < (Real.log X) ^ a :=
    Real.rpow_pos_of_pos hlogpos _
  have hlogSq : 8 ≤ (Real.log X) ^ (2 : ℕ) := by nlinarith
  have hden :
      8 * (Real.log X) ^ a ≤ (Real.log X) ^ (a + 2) := by
    rw [Real.rpow_add hlogpos, Real.rpow_two]
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left hlogSq hloga.le)
  rw [Real.rpow_neg hlogpos.le]
  simpa only [one_div] using
    (one_div_le_one_div_of_le (by positivity) hden)

/-- The corresponding rounded upper product window is also contained in
the same two-sided logarithmic window. -/
theorem logWindow_upper_roundingReserve
    {X a : ℝ} (hlog : 4 ≤ Real.log X) (ha : 0 ≤ a) :
    16 / (Real.log X) ^ a ≤ (Real.log X) ^ (a + 2) := by
  have hlogpos : 0 < Real.log X := by linarith
  have hlogaPos : 0 < (Real.log X) ^ a :=
    Real.rpow_pos_of_pos hlogpos _
  have hlogaOne : 1 ≤ (Real.log X) ^ a :=
    Real.one_le_rpow (by linarith) ha
  have hlogSq : 16 ≤ (Real.log X) ^ (2 : ℕ) := by nlinarith
  rw [Real.rpow_add hlogpos, Real.rpow_two]
  calc
    16 / (Real.log X) ^ a ≤ 16 :=
      (div_le_iff₀ hlogaPos).2 (by nlinarith)
    _ ≤ (Real.log X) ^ a * (Real.log X * Real.log X) := by
      nlinarith
    _ = (Real.log X) ^ a * (Real.log X) ^ (2 : ℕ) := by
      rw [pow_two]

/-- All length hypotheses of `TypeIIEstimateStatement` for either
naturalized second block, with every rounding reserve exposed.  In the final
eventual application `hM₂`, `hfloorReserve`, and `hlog` follow from the
source product window and fixed positive powers of `X`. -/
theorem representedTypeII_fullEstimate_lengthGeometry
    {X P M₁ M₂ epsilon a : ℝ} {N₂ : ℕ}
    (hX : 1 < X) (hlog : 4 ≤ Real.log X) (ha : 0 ≤ a)
    (hP : P = (Real.log X) ^ a)
    (hM₁ : 2 ≤ M₁) (hM₂ : 2 ≤ M₂)
    (hM₁lower : X ^ (epsilon / 2) ≤ M₁)
    (hM₁upper : M₁ ≤ X ^ (2 / 11 : ℝ))
    (hepsilon : 0 ≤ epsilon)
    (hfloorReserve : 2 * X ^ (epsilon / 5) ≤ X ^ (epsilon / 2))
    (hprodLower : X / (2 * P) < M₁ * M₂)
    (hprodUpper : M₁ * M₂ ≤ 4 * X / P)
    (hN₂ : N₂ = TypeII.naturalDyadicCoreScale M₂ ∨
      N₂ = TypeII.naturalDyadicBoundaryScale M₂) :
    1 ≤ TypeII.naturalDyadicCoreScale M₁ ∧ 1 ≤ N₂ ∧
      (Real.log X) ^ (-(a + 2)) ≤
        ((TypeII.naturalDyadicCoreScale M₁ : ℝ) * (N₂ : ℝ)) / X ∧
      ((TypeII.naturalDyadicCoreScale M₁ : ℝ) * (N₂ : ℝ)) / X ≤
        (Real.log X) ^ (a + 2) ∧
      X ^ (epsilon / 5) ≤
        (TypeII.naturalDyadicCoreScale M₁ : ℝ) ∧
      (TypeII.naturalDyadicCoreScale M₁ : ℝ) ≤
        X ^ (2 / 11 + epsilon) := by
  have hPpos : 0 < P := by
    rw [hP]
    exact Real.rpow_pos_of_pos (by linarith) _
  have hwindow := representedTypeII_naturalScale_product_window
    hPpos hM₁ hM₂ hprodLower hprodUpper hN₂
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hratioLower :
      1 / (8 * P) <
        ((TypeII.naturalDyadicCoreScale M₁ : ℝ) * (N₂ : ℝ)) / X := by
    apply (lt_div_iff₀ hXpos).2
    calc
      1 / (8 * P) * X = X / (8 * P) := by ring
      _ < (TypeII.naturalDyadicCoreScale M₁ : ℝ) * (N₂ : ℝ) :=
        hwindow.1
  have hratioUpper :
      ((TypeII.naturalDyadicCoreScale M₁ : ℝ) * (N₂ : ℝ)) / X ≤
        16 / P := by
    apply (div_le_iff₀ hXpos).2
    calc
      (TypeII.naturalDyadicCoreScale M₁ : ℝ) * (N₂ : ℝ) ≤
          16 * X / P := hwindow.2
      _ = 16 / P * X := by ring
  have hpower := representedTypeII_firstNaturalScale_powerRange
    hX.le hepsilon hM₁ hM₁lower hM₁upper hfloorReserve
  have hN₁one : 1 ≤ TypeII.naturalDyadicCoreScale M₁ := by
    apply (Nat.le_floor_iff (by positivity : 0 ≤ M₁)).2
    exact_mod_cast (show (1 : ℝ) ≤ M₁ by linarith)
  have hN₂one : 1 ≤ N₂ := by
    rcases hN₂ with rfl | rfl
    · apply (Nat.le_floor_iff (by positivity : 0 ≤ M₂)).2
      exact_mod_cast (show (1 : ℝ) ≤ M₂ by linarith)
    · simp only [TypeII.naturalDyadicBoundaryScale]
      have hcore : 1 ≤ TypeII.naturalDyadicCoreScale M₂ := by
        apply (Nat.le_floor_iff (by positivity : 0 ≤ M₂)).2
        exact_mod_cast (show (1 : ℝ) ≤ M₂ by linarith)
      omega
  refine ⟨hN₁one, hN₂one, ?_, ?_, hpower.1, hpower.2⟩
  · rw [hP] at hratioLower
    exact (logWindow_lower_roundingReserve hlog ha).trans hratioLower.le
  · rw [hP] at hratioUpper
    exact hratioUpper.trans (logWindow_upper_roundingReserve hlog ha)

/-- End-to-end eventual source-scale package for the upgraded Type-II
estimate.  It derives the stronger structured endpoint inclusion, the lower
bound for the complementary scale, and every natural length hypothesis from
the literal inequalities in Proposition 2.2(iii). -/
theorem eventually_sourceTypeII_fullEstimate_lengthGeometry
    {A epsilon a : ℝ} (hA : 0 < A) (hepsilon : 0 < epsilon)
    (ha : 0 ≤ a) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (R : ℕ) (M₁ M₂ : ℝ) (N₂ : ℕ),
        R ≤ ⌊Real.log (X ^ (2 / 11 : ℝ)) /
            Real.log
              (Real.exp
                (Real.log X /
                  (Real.log (Real.log X)) ^ (3 : ℕ)))⌋₊ →
        X ^ (epsilon / 2) ≤ M₁ →
        M₁ ≤ X ^ (2 / 11 : ℝ) →
        X / (2 * (Real.log X) ^ a) < M₁ * M₂ →
        M₁ * M₂ ≤ 4 * X / (Real.log X) ^ a →
        (N₂ = TypeII.naturalDyadicCoreScale M₂ ∨
          N₂ = TypeII.naturalDyadicBoundaryScale M₂) →
        (1 + (Real.log X) ^ (-10 * A)) ^ R * M₁ ≤
            2 * (TypeII.naturalDyadicCoreScale M₁ : ℝ) ∧
          1 ≤ TypeII.naturalDyadicCoreScale M₁ ∧ 1 ≤ N₂ ∧
          (Real.log X) ^ (-(a + 2)) ≤
            ((TypeII.naturalDyadicCoreScale M₁ : ℝ) * (N₂ : ℝ)) / X ∧
          ((TypeII.naturalDyadicCoreScale M₁ : ℝ) * (N₂ : ℝ)) / X ≤
            (Real.log X) ^ (a + 2) ∧
          X ^ (epsilon / 5) ≤
            (TypeII.naturalDyadicCoreScale M₁ : ℝ) ∧
          (TypeII.naturalDyadicCoreScale M₁ : ℝ) ≤
            X ^ (2 / 11 + epsilon) := by
  have hwidth := eventually_source_width_three_halves hA
  have hreserves := eventually_sourceTypeII_naturalization_reserves
    a hepsilon
  filter_upwards [hwidth, hreserves, eventually_gt_atTop (1 : ℝ)] with
      X hwidthX hreservesX hX
  intro R M₁ M₂ N₂ hR hM₁lower hM₁upper hprodLower
    hprodUpper hN₂
  rcases hreservesX with
    ⟨hXhalf, hfloorReserve, hcomplementReserve, hlog⟩
  have hM₁four : 4 ≤ M₁ := hXhalf.trans hM₁lower
  have hPpos : 0 < (Real.log X) ^ a :=
    Real.rpow_pos_of_pos (Real.log_pos hX) _
  have hM₁reserve :
      4 * (Real.log X) ^ a * M₁ ≤ X := by
    exact (mul_le_mul_of_nonneg_left hM₁upper
      (mul_nonneg (by norm_num) hPpos.le)).trans hcomplementReserve
  have hM₂two : 2 ≤ M₂ := by
    exact (representedTypeII_secondScale_ge_two_of_reserve
      hPpos (by linarith) hprodLower hM₁reserve).le
  have hstructuredUpper :
      (1 + (Real.log X) ^ (-10 * A)) ^ R * M₁ ≤
        2 * (TypeII.naturalDyadicCoreScale M₁ : ℝ) :=
    structuredUpper_le_two_floor hM₁four (hwidthX R hR)
  have hgeometry := representedTypeII_fullEstimate_lengthGeometry
    hX hlog ha rfl (by linarith : 2 ≤ M₁) hM₂two hM₁lower
    hM₁upper hepsilon.le hfloorReserve hprodLower hprodUpper hN₂
  exact ⟨hstructuredUpper, hgeometry⟩

/-- A large value of a two-block naturalized polynomial selects at least one
block with half the original threshold. -/
theorem half_threshold_le_one_naturalBlock_of_le_realScale
    {M V t : ℝ} (hM : 1 ≤ M) (a : ℕ → ℂ)
    (hlarge : V ≤ ‖dyadicDirichletPolynomial a M (onePlusIT t)‖) :
    V / 2 ≤
        ‖dyadicDirichletPolynomial a
          (TypeII.naturalDyadicCoreScale M : ℝ) (onePlusIT t)‖ ∨
      V / 2 ≤
        ‖dyadicDirichletPolynomial (TypeII.dyadicBoundaryCoefficient a M)
          (TypeII.naturalDyadicBoundaryScale M : ℝ) (onePlusIT t)‖ := by
  rw [TypeII.dyadicDirichletPolynomial_realScale_eq_two_naturalScales
    hM] at hlarge
  by_contra h
  rw [not_or, not_le, not_le] at h
  have htriangle := norm_add_le
    (dyadicDirichletPolynomial a
      (TypeII.naturalDyadicCoreScale M : ℝ) (onePlusIT t))
    (dyadicDirichletPolynomial (TypeII.dyadicBoundaryCoefficient a M)
      (TypeII.naturalDyadicBoundaryScale M : ℝ) (onePlusIT t))
  linarith

/-- Squaring the triangle inequality for two summands costs exactly the
harmless factor two used when recombining the natural endpoint blocks. -/
theorem norm_add_sq_le_two_mul_sum_sq (z w : ℂ) :
    ‖z + w‖ ^ (2 : ℕ) ≤
      2 * (‖z‖ ^ (2 : ℕ) + ‖w‖ ^ (2 : ℕ)) := by
  have hnorm := norm_add_le z w
  have hsquare : ‖z + w‖ ^ (2 : ℕ) ≤ (‖z‖ + ‖w‖) ^ (2 : ℕ) :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

/-- Integrated exact two-block assembly.  Every regularity hypothesis is
discharged from finite Dirichlet-polynomial continuity and boundedness of
the ambient height interval. -/
theorem integral_representedTypeII_le_two_naturalProducts
    {delta M₁ M₂ X : ℝ} {R : ℕ} {alpha beta f : ℕ → ℂ}
    {E : Set ℝ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 1 ≤ M₂)
    (_hX : 0 ≤ X) (hE : MeasurableSet E)
    (hEsub : E ⊆ Set.Icc (-X) X)
    (hupper : (1 + delta) ^ R * M₁ ≤
      2 * (TypeII.naturalDyadicCoreScale M₁ : ℝ))
    (hf : ∀ n, f n =
      matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta n) :
    (∫ t in E,
        ‖dirichletPolynomial f
          (Sparse.typeIIProductSupport delta M₁ M₂ R)
          (onePlusIT t)‖ ^ (2 : ℕ)) ≤
      2 * (∫ t in E,
        ‖dyadicDirichletPolynomial
            (supportedTypeIIFirstCoefficient delta M₁ R alpha)
            (TypeII.naturalDyadicCoreScale M₁ : ℝ) (onePlusIT t) *
          dyadicDirichletPolynomial beta
            (TypeII.naturalDyadicCoreScale M₂ : ℝ) (onePlusIT t)‖ ^
              (2 : ℕ)) +
      2 * (∫ t in E,
        ‖dyadicDirichletPolynomial
            (supportedTypeIIFirstCoefficient delta M₁ R alpha)
            (TypeII.naturalDyadicCoreScale M₁ : ℝ) (onePlusIT t) *
          dyadicDirichletPolynomial
            (TypeII.dyadicBoundaryCoefficient beta M₂)
            (TypeII.naturalDyadicBoundaryScale M₂ : ℝ) (onePlusIT t)‖ ^
              (2 : ℕ)) := by
  let A : ℝ → ℂ := fun t ↦
    dyadicDirichletPolynomial
      (supportedTypeIIFirstCoefficient delta M₁ R alpha)
      (TypeII.naturalDyadicCoreScale M₁ : ℝ) (onePlusIT t)
  let B₀ : ℝ → ℂ := fun t ↦
    dyadicDirichletPolynomial beta
      (TypeII.naturalDyadicCoreScale M₂ : ℝ) (onePlusIT t)
  let B₁ : ℝ → ℂ := fun t ↦
    dyadicDirichletPolynomial (TypeII.dyadicBoundaryCoefficient beta M₂)
      (TypeII.naturalDyadicBoundaryScale M₂ : ℝ) (onePlusIT t)
  let F : ℝ → ℂ := fun t ↦
    dirichletPolynomial f
      (Sparse.typeIIProductSupport delta M₁ M₂ R) (onePlusIT t)
  have hAcont : Continuous A := by
    exact Sparse.continuous_dirichletPolynomial_onePlusIT_sparse _ _
  have hB₀cont : Continuous B₀ := by
    exact Sparse.continuous_dirichletPolynomial_onePlusIT_sparse _ _
  have hB₁cont : Continuous B₁ := by
    exact Sparse.continuous_dirichletPolynomial_onePlusIT_sparse _ _
  have hFcont : Continuous F := by
    exact Sparse.continuous_dirichletPolynomial_onePlusIT_sparse _ _
  have hleft : IntegrableOn (fun t ↦ ‖F t‖ ^ (2 : ℕ)) E :=
    (hFcont.norm.pow 2).integrableOn_Icc.mono_set hEsub
  have hterm₀ : IntegrableOn (fun t ↦ ‖A t * B₀ t‖ ^ (2 : ℕ)) E :=
    ((hAcont.mul hB₀cont).norm.pow 2).integrableOn_Icc.mono_set hEsub
  have hterm₁ : IntegrableOn (fun t ↦ ‖A t * B₁ t‖ ^ (2 : ℕ)) E :=
    ((hAcont.mul hB₁cont).norm.pow 2).integrableOn_Icc.mono_set hEsub
  have hright : IntegrableOn
      (fun t ↦ 2 * (‖A t * B₀ t‖ ^ (2 : ℕ) +
        ‖A t * B₁ t‖ ^ (2 : ℕ))) E :=
    (hterm₀.add hterm₁).const_mul 2
  have hpointwise : ∀ t, ‖F t‖ ^ (2 : ℕ) ≤
      2 * (‖A t * B₀ t‖ ^ (2 : ℕ) +
        ‖A t * B₁ t‖ ^ (2 : ℕ)) := by
    intro t
    have hfactor := representedTypeII_eq_two_naturalProducts
      hdelta hM₁ hM₂ hupper hf (onePlusIT t)
    change ‖F t‖ ^ (2 : ℕ) ≤ _
    change F t = A t * B₀ t + A t * B₁ t at hfactor
    rw [hfactor]
    exact norm_add_sq_le_two_mul_sum_sq _ _
  calc
    (∫ t in E, ‖F t‖ ^ (2 : ℕ)) ≤
        ∫ t in E, 2 * (‖A t * B₀ t‖ ^ (2 : ℕ) +
          ‖A t * B₁ t‖ ^ (2 : ℕ)) :=
      setIntegral_mono_on hleft hright hE (fun t _ ↦ hpointwise t)
    _ = 2 * (∫ t in E, ‖A t * B₀ t‖ ^ (2 : ℕ)) +
        2 * (∫ t in E, ‖A t * B₁ t‖ ^ (2 : ℕ)) := by
      rw [integral_const_mul, integral_add hterm₀ hterm₁]
      ring

/-- The narrow residual analytic proposition after deterministic
naturalization: prove the same majorant for the core and singleton-boundary
products.  `integral_representedTypeII_le_two_naturalProducts` then returns
the source component with a factor four. -/
def NaturalizedTypeIIAnalyticResidual
    (delta M₁ M₂ : ℝ) (R : ℕ) (alpha beta : ℕ → ℂ)
    (E : Set ℝ) (V : ℝ) : Prop :=
  (∫ t in E,
      ‖dyadicDirichletPolynomial
          (supportedTypeIIFirstCoefficient delta M₁ R alpha)
          (TypeII.naturalDyadicCoreScale M₁ : ℝ) (onePlusIT t) *
        dyadicDirichletPolynomial beta
          (TypeII.naturalDyadicCoreScale M₂ : ℝ) (onePlusIT t)‖ ^
            (2 : ℕ)) ≤ V ∧
  (∫ t in E,
      ‖dyadicDirichletPolynomial
          (supportedTypeIIFirstCoefficient delta M₁ R alpha)
          (TypeII.naturalDyadicCoreScale M₁ : ℝ) (onePlusIT t) *
        dyadicDirichletPolynomial
          (TypeII.dyadicBoundaryCoefficient beta M₂)
          (TypeII.naturalDyadicBoundaryScale M₂ : ℝ) (onePlusIT t)‖ ^
            (2 : ℕ)) ≤ V

/-- Exact discharge rule for the residual proposition. -/
theorem integral_representedTypeII_le_four_mul_of_naturalizedResidual
    {delta M₁ M₂ X V : ℝ} {R : ℕ} {alpha beta f : ℕ → ℂ}
    {E : Set ℝ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 1 ≤ M₂)
    (hX : 0 ≤ X) (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc (-X) X)
    (hupper : (1 + delta) ^ R * M₁ ≤
      2 * (TypeII.naturalDyadicCoreScale M₁ : ℝ))
    (hf : ∀ n, f n =
      matomakiTeravainenTypeIIValue delta M₁ M₂ R alpha beta n)
    (hresidual : NaturalizedTypeIIAnalyticResidual
      delta M₁ M₂ R alpha beta E V) :
    (∫ t in E,
        ‖dirichletPolynomial f
          (Sparse.typeIIProductSupport delta M₁ M₂ R)
          (onePlusIT t)‖ ^ (2 : ℕ)) ≤ 4 * V := by
  have hsplit := integral_representedTypeII_le_two_naturalProducts
    hdelta hM₁ hM₂ hX hE hEsub hupper hf
  dsimp only [NaturalizedTypeIIAnalyticResidual] at hresidual
  linarith

/-! ## Direct feed into the upgraded Type-II estimate -/

/-- Source-scale version of the upgraded Type-II estimate for either of the
two naturalized second blocks.  This differs from
`TypeIIEstimateStatement` only in that its length hypotheses are the literal
ones supplied by Proposition 2.2(iii); the theorem below proves it without
new analytic input. -/
def NaturalizedSourceTypeIIEstimateStatement : Prop :=
  ∃ C₁ epsilon₀ : ℝ, 0 < C₁ ∧ 0 < epsilon₀ ∧
    ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilon₀ →
      ∀ B : ℝ, 0 ≤ B →
        ∃ kappa₁ : ℝ, 0 < kappa₁ ∧
          ∀ A₀ a : ℝ, 1 ≤ A₀ → 0 ≤ a →
            ∃ C₂ C X₀ : ℝ,
              0 < C₂ ∧ 0 < C ∧ 1 ≤ X₀ ∧
                ∀ (X M₁ M₂ delta : ℝ) (R N₂ : ℕ)
                    (alpha gamma : ℕ → ℂ) (U : Set ℝ) (S : ℝ),
                  X₀ ≤ X → 1 < X → 4 ≤ Real.log X →
                  2 ≤ M₁ → 2 ≤ M₂ →
                  X ^ (epsilon / 2) ≤ M₁ →
                  M₁ ≤ X ^ (2 / 11 : ℝ) →
                  2 * X ^ (epsilon / 5) ≤ X ^ (epsilon / 2) →
                  X / (2 * (Real.log X) ^ a) < M₁ * M₂ →
                  M₁ * M₂ ≤ 4 * X / (Real.log X) ^ a →
                  (N₂ = TypeII.naturalDyadicCoreScale M₂ ∨
                    N₂ = TypeII.naturalDyadicBoundaryScale M₂) →
                  IsDivisorBoundedByConstant B A₀ alpha →
                  IsDivisorBoundedByConstant B A₀ gamma →
                  MeasurableSet U → U ⊆ Set.Icc (0 : ℝ) X →
                  (∀ t ∈ U,
                    (TypeII.naturalDyadicCoreScale M₁ : ℝ) ^
                        (-(17 / 70 - C₁ * epsilon)) ≤
                      ‖dyadicDirichletPolynomial
                        (supportedTypeIIFirstCoefficient delta M₁ R alpha)
                        (TypeII.naturalDyadicCoreScale M₁ : ℝ)
                        (onePlusIT t)‖ ∨
                    (N₂ : ℝ) ^ (-(17 / 70 - C₁ * epsilon)) ≤
                      ‖dyadicDirichletPolynomial gamma (N₂ : ℝ)
                        (onePlusIT t)‖) →
                  0 ≤ S →
                  (∀ t ∈ U,
                    ‖dyadicDirichletPolynomial
                      (supportedTypeIIFirstCoefficient delta M₁ R alpha)
                      (TypeII.naturalDyadicCoreScale M₁ : ℝ)
                      (onePlusIT t)‖ ^ (2 : ℕ) ≤ S) →
                  (∫ t in U,
                    ‖dyadicDirichletPolynomial
                      (supportedTypeIIFirstCoefficient delta M₁ R alpha)
                      (TypeII.naturalDyadicCoreScale M₁ : ℝ)
                      (onePlusIT t)‖ ^ (2 : ℕ) *
                    ‖dyadicDirichletPolynomial gamma (N₂ : ℝ)
                      (onePlusIT t)‖ ^ (2 : ℕ)) ≤
                    C * (X ^ (-kappa₁) + (Real.log X) ^ C₂ * S)

/-- The completed Proposition 5.1 estimate implies its literal source-scale
natural-block specialization. -/
theorem naturalizedSourceTypeIIEstimate_of_typeIIEstimate
    (htypeII : TypeII.TypeIIEstimateStatement) :
    NaturalizedSourceTypeIIEstimateStatement := by
  rcases htypeII with
    ⟨C₁, epsilon₀, hC₁, hepsilon₀, htypeII⟩
  refine ⟨C₁, epsilon₀, hC₁, hepsilon₀, ?_⟩
  intro epsilon hepsilon hepsilonUpper B hB
  obtain ⟨kappa₁, hkappa₁, htypeII⟩ :=
    htypeII epsilon hepsilon hepsilonUpper B hB
  refine ⟨kappa₁, hkappa₁, ?_⟩
  intro A₀ a hA₀ ha
  obtain ⟨C₂, C, X₀, hC₂, hC, hX₀, hbound⟩ :=
    htypeII A₀ (a + 2) hA₀ (by linarith)
  refine ⟨C₂, C, X₀, hC₂, hC, hX₀, ?_⟩
  intro X M₁ M₂ delta R N₂ alpha gamma U S hX₀X hX hlog
    hM₁ hM₂ hM₁lower hM₁upper hfloorReserve hprodLower
    hprodUpper hN₂ halpha hgamma hUmeas hU hlarge hS hSbound
  have hgeometry := representedTypeII_fullEstimate_lengthGeometry
    hX hlog ha rfl hM₁ hM₂ hM₁lower hM₁upper hepsilon.le
    hfloorReserve hprodLower hprodUpper hN₂
  rcases hgeometry with
    ⟨hN₁, hN₂one, hprodLower', hprodUpper', hN₁lower, hN₁upper⟩
  exact hbound X (TypeII.naturalDyadicCoreScale M₁) N₂
    (supportedTypeIIFirstCoefficient delta M₁ R alpha) gamma U S
    hX₀X hN₁ hN₂one hprodLower' hprodUpper' hN₁lower
    hN₁upper
    (supportedTypeIIFirstCoefficient_isDivisorBoundedByConstant halpha)
    hgamma hUmeas hU hlarge hS hSbound

/-- Fully cited instance of the preceding source-scale statement. -/
theorem naturalizedSourceTypeIIEstimate_of_externalInputs
    (inputs : ExternalInputs) : NaturalizedSourceTypeIIEstimateStatement :=
  naturalizedSourceTypeIIEstimate_of_typeIIEstimate
    (TypeII.typeIIEstimateStatement_of_externalInputs inputs)

/-- Registry entry.  The analytic partition and the medium-bin estimates for
the two natural products are applied in `Final/TypeIIComponent.lean`. -/
def typeIIInstantiationModule : ProofModule :=
  { name := "Completion.TypeIIInstantiation"
    paperLocation := "Proof of Proposition 7.1, Type-II case"
    purpose :=
      "Naturalize the real source scales without endpoint loss, preserve divisor bounds, prove the exact two-product factorization, and expose the product and first-length geometry required by the analytic packages."
    dependsOn := ["Completion.TypeIIClosure",
      "TypeII.RealScaleNaturalization", "Sparse.PropagationParameters",
      "Sparse.GlobalComponentCancellation"]
    status := .proved }

end
end Completion
end ExactSemiprimes
