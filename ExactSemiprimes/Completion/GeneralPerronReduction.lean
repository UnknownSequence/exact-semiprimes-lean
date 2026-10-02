import ExactSemiprimes.Completion.PerronCumulativeBounds
import ExactSemiprimes.Sparse.Propagation

/-!
# General Perron reduction: exact finite interfaces

Teräväinen's 2016 Lemma 1 is a Parseval/Perron lemma for a general
coefficient sequence.  Before it can be applied to the product polynomial
in the present paper, one must identify its coefficient sequence, its full
support, and the two different integral normalizations.  The algebraic and
normalization parts are proved here.  The analytic Parseval inequality is
left as an explicit proposition rather than being silently inferred from a
source statement whose printed normalization and support do not match this
application.
-/

namespace ExactSemiprimes
namespace Completion

open MeasureTheory

noncomputable section

/-- The literal finite support obtained by multiplying the prime support by
the minorant support. -/
def perronProductSupport (X P : ℝ) : Finset ℕ :=
  ((dyadicPrimes P).product
    (natOpenClosedInterval (X / (2 * P)) (4 * X / P))).image
      fun pn ↦ pn.1 * pn.2

/-- The coefficient of the literal product polynomial, with multiplicities
retained. -/
def perronProductCoefficient
    (weight : ℕ → ℝ) (X P : ℝ) (m : ℕ) : ℂ :=
  Sparse.binaryConvolutionCoefficient
    (fun _ ↦ 1) (fun n ↦ (weight n : ℂ))
    (dyadicPrimes P)
    (natOpenClosedInterval (X / (2 * P)) (4 * X / P)) m

/-- Exact finite convolution identity for the polynomial appearing in the
Perron target.  In particular, the actual product support is exposed rather
than being replaced by the narrower `n ∼ X` support printed in Teräväinen's
Lemma 1. -/
theorem perronProduct_eq_convolutionPolynomial
    (weight : ℕ → ℝ) (X P t : ℝ) :
    perronProduct weight X P t =
      dirichletPolynomial (perronProductCoefficient weight X P)
        (perronProductSupport X P) (onePlusIT t) := by
  unfold perronProduct primeDirichletPolynomial perronMinorantPolynomial
    perronProductCoefficient perronProductSupport
  exact Sparse.dirichletPolynomial_mul_eq_binaryConvolution
    (fun _ : ℕ ↦ (1 : ℂ)) (fun n ↦ (weight n : ℂ))
    (dyadicPrimes P)
    (natOpenClosedInterval (X / (2 * P)) (4 * X / P))
    (onePlusIT t)

/-- If the minorant coefficients have norm at most `K`, then a coefficient
of the product has norm at most `K` times the number of available primes.
For a fixed product, projection to the prime coordinate is injective; this
avoids the much larger and incorrect loss by the cardinality of the whole
Cartesian-product support. -/
theorem norm_perronProductCoefficient_le_primeCard_mul
    (weight : ℕ → ℝ) (X P K : ℝ) (m : ℕ) (hK : 0 ≤ K)
    (hweight : ∀ n ∈
      natOpenClosedInterval (X / (2 * P)) (4 * X / P),
        ‖(weight n : ℂ)‖ ≤ K) :
    ‖perronProductCoefficient weight X P m‖ ≤
      ((dyadicPrimes P).card : ℝ) * K := by
  classical
  let S₁ : Finset ℕ := dyadicPrimes P
  let S₂ : Finset ℕ :=
    natOpenClosedInterval (X / (2 * P)) (4 * X / P)
  let fiber : Finset (ℕ × ℕ) :=
    (S₁.product S₂).filter (fun pn ↦ pn.1 * pn.2 = m)
  have hcard : fiber.card ≤ S₁.card := by
    refine Finset.card_le_card_of_injOn Prod.fst ?_ ?_
    · intro pn hpn
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hpn).1).1
    · intro pn hpn qr hqr heq
      have hpnProduct := (Finset.mem_filter.mp hpn).2
      have hqrProduct := (Finset.mem_filter.mp hqr).2
      have hprime : pn.1.Prime := by
        exact (Finset.mem_filter.mp
          (Finset.mem_product.mp (Finset.mem_filter.mp hpn).1).1).2
      apply Prod.ext heq
      apply Nat.mul_left_cancel hprime.pos
      calc
        pn.1 * pn.2 = m := hpnProduct
        _ = qr.1 * qr.2 := hqrProduct.symm
        _ = pn.1 * qr.2 := by rw [heq]
  have hterm : ∀ pn ∈ fiber,
      ‖(1 : ℂ) * (weight pn.2 : ℂ)‖ ≤ K := by
    intro pn hpn
    have hnmem : pn.2 ∈ S₂ :=
      (Finset.mem_product.mp (Finset.mem_filter.mp hpn).1).2
    simpa [S₂] using hweight pn.2 hnmem
  unfold perronProductCoefficient Sparse.binaryConvolutionCoefficient
  change ‖∑ pn ∈ fiber, (1 : ℂ) * (weight pn.2 : ℂ)‖ ≤ _
  calc
    ‖∑ pn ∈ fiber, (1 : ℂ) * (weight pn.2 : ℂ)‖ ≤
        ∑ pn ∈ fiber, ‖(1 : ℂ) * (weight pn.2 : ℂ)‖ :=
      norm_sum_le fiber _
    _ ≤ ∑ _pn ∈ fiber, K := Finset.sum_le_sum hterm
    _ = (fiber.card : ℝ) * K := by simp
    _ ≤ (S₁.card : ℝ) * K := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hK
    _ = ((dyadicPrimes P).card : ℝ) * K := rfl

/-- The number of primes in the dyadic block is at most its elementary
ambient length.  No prime number theorem is used. -/
theorem dyadicPrimes_card_cast_le_two_mul
    {P : ℝ} (hP : 0 ≤ P) :
    ((dyadicPrimes P).card : ℝ) ≤ 2 * P := by
  have hfilter : (dyadicPrimes P).card ≤ (dyadicInterval P).card := by
    exact Finset.card_filter_le _ _
  have hinterval : (dyadicInterval P).card ≤ ⌊2 * P⌋₊ := by
    simp only [dyadicInterval, Nat.card_Ioc]
    omega
  have hnat : (dyadicPrimes P).card ≤ ⌊2 * P⌋₊ := hfilter.trans hinterval
  calc
    ((dyadicPrimes P).card : ℝ) ≤ (⌊2 * P⌋₊ : ℝ) := by exact_mod_cast hnat
    _ ≤ 2 * P := Nat.floor_le (by positivity)

/-- A coefficient bound `K` for the minorant therefore gives the completely
explicit product-coefficient bound `2PK`. -/
theorem norm_perronProductCoefficient_le_two_mul
    (weight : ℕ → ℝ) (X P K : ℝ) (m : ℕ)
    (hP : 0 ≤ P) (hK : 0 ≤ K)
    (hweight : ∀ n ∈
      natOpenClosedInterval (X / (2 * P)) (4 * X / P),
        ‖(weight n : ℂ)‖ ≤ K) :
    ‖perronProductCoefficient weight X P m‖ ≤ 2 * P * K := by
  calc
    ‖perronProductCoefficient weight X P m‖ ≤
        ((dyadicPrimes P).card : ℝ) * K :=
      norm_perronProductCoefficient_le_primeCard_mul
        weight X P K m hK hweight
    _ ≤ (2 * P) * K :=
      mul_le_mul_of_nonneg_right (dyadicPrimes_card_cast_le_two_mul hP) hK

/-- Any fixed polylogarithmic coefficient bound is annihilated by the
paper's power-sized lower cutoff `T₀=X^(1/1000)`.  This is the quantitative
absorption needed for the low-frequency term in the Parseval lemma. -/
theorem eventually_polylogCoefficient_lowFrequency_le
    (K₀ a ε : ℝ) :
    ∀ᶠ X : ℝ in Filter.atTop,
      (K₀ * (Real.log X) ^ a) ^ (2 : ℕ) /
          X ^ (1 / 1000 : ℝ) ≤
        1 / (Real.log X) ^ (2 + ε) := by
  let δ : ℝ := 1 / 2000
  let L : ℝ := 2 * a + (2 + ε)
  have hδ : 0 < δ := by norm_num [δ]
  have hlogBound := TypeII.eventually_log_rpow_le_rpow L hδ
  have hconstBound :=
    (_root_.tendsto_rpow_atTop hδ).eventually_ge_atTop (K₀ ^ (2 : ℕ))
  filter_upwards [hlogBound, hconstBound,
    Filter.eventually_gt_atTop (1 : ℝ)] with X hlog hconst hX
  have hXpos : 0 < X := zero_lt_one.trans hX
  have hlogXpos : 0 < Real.log X := Real.log_pos hX
  have hpowNonneg : 0 ≤ X ^ δ := Real.rpow_nonneg hXpos.le _
  have hlogNonneg : 0 ≤ (Real.log X) ^ L :=
    Real.rpow_nonneg hlogXpos.le _
  have hproduct :
      K₀ ^ (2 : ℕ) * (Real.log X) ^ L ≤
        X ^ (1 / 1000 : ℝ) := by
    calc
      K₀ ^ (2 : ℕ) * (Real.log X) ^ L ≤ X ^ δ * X ^ δ :=
        mul_le_mul hconst hlog hlogNonneg hpowNonneg
      _ = X ^ (δ + δ) := (Real.rpow_add hXpos δ δ).symm
      _ = X ^ (1 / 1000 : ℝ) := by norm_num [δ]
  have hleftIdentity :
      (K₀ * (Real.log X) ^ a) ^ (2 : ℕ) *
          (Real.log X) ^ (2 + ε) =
        K₀ ^ (2 : ℕ) * (Real.log X) ^ L := by
    rw [mul_pow]
    have haTwo :
        ((Real.log X) ^ a) ^ (2 : ℕ) =
          (Real.log X) ^ (2 * a) := by
      calc
        ((Real.log X) ^ a) ^ (2 : ℕ) =
            Real.rpow ((Real.log X) ^ a) (2 : ℝ) :=
          (Real.rpow_natCast ((Real.log X) ^ a) 2).symm
        _ = (Real.log X) ^ (a * 2) :=
          (Real.rpow_mul hlogXpos.le a 2).symm
        _ = (Real.log X) ^ (2 * a) := by ring_nf
    rw [haTwo]
    calc
      K₀ ^ (2 : ℕ) * (Real.log X) ^ (2 * a) *
          (Real.log X) ^ (2 + ε) =
          K₀ ^ (2 : ℕ) *
            ((Real.log X) ^ (2 * a) *
              (Real.log X) ^ (2 + ε)) := by ring
      _ = K₀ ^ (2 : ℕ) *
          (Real.log X) ^ (2 * a + (2 + ε)) := by
        rw [← Real.rpow_add hlogXpos]
      _ = K₀ ^ (2 : ℕ) * (Real.log X) ^ L := by rfl
  have hT₀pos : 0 < X ^ (1 / 1000 : ℝ) :=
    Real.rpow_pos_of_pos hXpos _
  have hlogPowerPos : 0 < (Real.log X) ^ (2 + ε) :=
    Real.rpow_pos_of_pos hlogXpos _
  apply (div_le_div_iff₀ hT₀pos hlogPowerPos).2
  rw [one_mul, hleftIdentity]
  exact hproduct

/-! ## The actual minorant coefficient budget -/

/-- The roughness indicator occurring in equation (2.4) is at most one. -/
theorem matomakiTeravainenRoughIndicator_le_one
    (n : ℕ) (z : ℝ) :
    matomakiTeravainenRoughIndicator n z ≤ 1 := by
  unfold matomakiTeravainenRoughIndicator
  split_ifs <;> norm_num

/-- Equation (2.4) and the numerical bound for its prefactor give a uniform
raw coefficient bound on the Perron support.  The support geometry is kept
explicit, because it is the only place the logarithmic prime scale enters. -/
theorem minorant_norm_le_5324_on_perronSupport
    {X P ε εₘₐₓ : ℝ}
    (hX : 3 ≤ X) (hP : 0 < P)
    (hε : 0 < ε) (hεmax : ε ≤ εₘₐₓ)
    (heq24 : ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∀ X : ℝ, 3 ≤ X → ∀ n : ℕ,
        2 * X ^ (1 / 2 : ℝ) ≤ (n : ℝ) → (n : ℝ) ≤ 3 * X →
          |matomakiTeravainenMinorant X ε n| ≤
            sectionFiveMinorantMajorant X *
              matomakiTeravainenRoughIndicator n
                (X ^ (2 / 11 : ℝ)))
    (hlower : 2 * X ^ (1 / 2 : ℝ) ≤ X / (2 * P))
    (hupper : 4 * X / P ≤ 3 * X) :
    ∀ n ∈ natOpenClosedInterval (X / (2 * P)) (4 * X / P),
      ‖(matomakiTeravainenMinorant X ε n : ℂ)‖ ≤ 5324 := by
  intro n hn
  have hXpos : 0 < X := by linarith
  have hlowerNonneg : 0 ≤ X / (2 * P) := by positivity
  have hupperNonneg : 0 ≤ 4 * X / P := by positivity
  have hnrange := (mem_natOpenClosedInterval hlowerNonneg hupperNonneg).mp hn
  have hnLower : 2 * X ^ (1 / 2 : ℝ) ≤ (n : ℝ) :=
    hlower.trans hnrange.1.le
  have hnUpper : (n : ℝ) ≤ 3 * X := hnrange.2.trans hupper
  have hpoint := heq24 ε hε hεmax X hX n hnLower hnUpper
  have hmajorantNonneg : 0 ≤ sectionFiveMinorantMajorant X :=
    sectionFiveMinorantMajorant_nonneg hX
  have hrough := matomakiTeravainenRoughIndicator_le_one n
    (X ^ (2 / 11 : ℝ))
  calc
    ‖(matomakiTeravainenMinorant X ε n : ℂ)‖ =
        |matomakiTeravainenMinorant X ε n| := by simp
    _ ≤ sectionFiveMinorantMajorant X *
          matomakiTeravainenRoughIndicator n
            (X ^ (2 / 11 : ℝ)) := hpoint
    _ ≤ sectionFiveMinorantMajorant X * 1 :=
      mul_le_mul_of_nonneg_left hrough hmajorantNonneg
    _ ≤ 5324 := by simpa using sectionFiveMinorantMajorant_le hX

/-- The complete elementary coefficient budget for the product polynomial:
equation (2.4) costs `5324`, and summing over the dyadic prime coordinate
costs at most `2P`. -/
theorem productMinorantCoefficient_norm_le
    {X P ε εₘₐₓ : ℝ}
    (hX : 3 ≤ X) (hP : 0 < P)
    (hε : 0 < ε) (hεmax : ε ≤ εₘₐₓ)
    (heq24 : ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∀ X : ℝ, 3 ≤ X → ∀ n : ℕ,
        2 * X ^ (1 / 2 : ℝ) ≤ (n : ℝ) → (n : ℝ) ≤ 3 * X →
          |matomakiTeravainenMinorant X ε n| ≤
            sectionFiveMinorantMajorant X *
              matomakiTeravainenRoughIndicator n
                (X ^ (2 / 11 : ℝ)))
    (hlower : 2 * X ^ (1 / 2 : ℝ) ≤ X / (2 * P))
    (hupper : 4 * X / P ≤ 3 * X) (m : ℕ) :
    ‖perronProductCoefficient
        (matomakiTeravainenMinorant X ε) X P m‖ ≤ 10648 * P := by
  have hweight := minorant_norm_le_5324_on_perronSupport
    hX hP hε hεmax heq24 hlower hupper
  calc
    ‖perronProductCoefficient
        (matomakiTeravainenMinorant X ε) X P m‖ ≤
        2 * P * 5324 :=
      norm_perronProductCoefficient_le_two_mul
        (matomakiTeravainenMinorant X ε) X P 5324 m hP.le
        (by norm_num) hweight
    _ = 10648 * P := by ring

/-- The support inclusion used above is uniform on the entire exponent
window `1 ≤ a ≤ 11/10`, not only on MT23's very narrow printed window. -/
theorem eventually_perronSupport_inside_equationTwoFour_range_wide :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ a : ℝ, 1 ≤ a → a ≤ 11 / 10 →
        let P : ℝ := (Real.log X) ^ a
        0 < P ∧
          2 * X ^ (1 / 2 : ℝ) ≤ X / (2 * P) ∧
          4 * X / P ≤ 3 * X := by
  have hsmall : ∀ᶠ X : ℝ in Filter.atTop,
      (Real.log X) ^ (11 / 10 : ℝ) ≤
        (1 / 4 : ℝ) * X ^ (1 / 2 : ℝ) := by
    have hlittle := Asymptotics.isLittleO_iff.1
      (isLittleO_log_rpow_rpow_atTop (11 / 10 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 2))
      (by norm_num : (0 : ℝ) < 1 / 4)
    filter_upwards [hlittle, Filter.eventually_gt_atTop (1 : ℝ)] with X hX hXone
    have hlogNonneg : 0 ≤ Real.log X := Real.log_nonneg hXone.le
    have hXnonneg : 0 ≤ X := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlogNonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg hXnonneg _)] at hX
    exact hX
  filter_upwards [hsmall,
    Filter.eventually_ge_atTop (Real.exp 2)] with X hsmallX hX
  intro a haLower haUpper
  have hXpos : 0 < X := (Real.exp_pos 2).trans_le hX
  have hlogXtwo : 2 ≤ Real.log X := by
    rw [← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos 2) hX
  have hlogXone : 1 ≤ Real.log X := by linarith
  have hPpos : 0 < Real.log X ^ a :=
    Real.rpow_pos_of_pos (by linarith) a
  have hPlower : 4 / 3 ≤ Real.log X ^ a := by
    calc
      (4 / 3 : ℝ) ≤ Real.log X := by linarith
      _ = Real.log X ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Real.log X ^ a :=
        Real.rpow_le_rpow_of_exponent_le hlogXone haLower
  have hPupper : Real.log X ^ a ≤
      Real.log X ^ (11 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlogXone haUpper
  have hfourP : 4 * Real.log X ^ a ≤ X ^ (1 / 2 : ℝ) := by
    calc
      4 * Real.log X ^ a ≤ 4 * Real.log X ^ (11 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hPupper (by norm_num)
      _ ≤ 4 * ((1 / 4 : ℝ) * X ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsmallX (by norm_num)
      _ = X ^ (1 / 2 : ℝ) := by ring
  refine ⟨hPpos, ?_, ?_⟩
  · apply (le_div_iff₀ (mul_pos (by norm_num) hPpos)).2
    calc
      2 * X ^ (1 / 2 : ℝ) * (2 * Real.log X ^ a) =
          (4 * Real.log X ^ a) * X ^ (1 / 2 : ℝ) := by ring
      _ ≤ X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hfourP
          (Real.rpow_nonneg hXpos.le _)
      _ = X := by
        rw [← Real.rpow_add hXpos]
        norm_num
  · apply (div_le_iff₀ hPpos).2
    have hmul := mul_le_mul_of_nonneg_left hPlower
      (show 0 ≤ 3 * X by positivity)
    nlinarith

/-- Fully quantified product-coefficient budget obtained from the cited
equation (2.4).  It is uniform throughout the enlarged prime-scale window. -/
theorem eventually_productMinorantCoefficient_bound_of_inputs
    (inputs : ExternalInputs) :
    ∃ εₘₐₓ : ℝ, 0 < εₘₐₓ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
        ∀ᶠ X : ℝ in Filter.atTop,
          ∀ a : ℝ, 1 ≤ a → a ≤ 11 / 10 → ∀ m : ℕ,
            ‖perronProductCoefficient
                (matomakiTeravainenMinorant X ε) X
                ((Real.log X) ^ a) m‖ ≤
              10648 * (Real.log X) ^ a := by
  obtain ⟨εₘₐₓ, hεₘₐₓ, heq24⟩ :=
    inputs.matomakiTeravainenEquationTwoFour
  refine ⟨εₘₐₓ, hεₘₐₓ, ?_⟩
  intro ε hε hεUpper
  filter_upwards [eventually_perronSupport_inside_equationTwoFour_range_wide,
    Filter.eventually_ge_atTop (3 : ℝ)] with X hgeometry hX
  intro a haLower haUpper m
  obtain ⟨hP, hlower, hupper⟩ := hgeometry a haLower haUpper
  exact productMinorantCoefficient_norm_le
    hX hP hε hεUpper heq24 hlower hupper m

/-- A fully explicit fixed-scale interface for the one analytic step still
needed from the general Parseval/Perron argument.  `K` is a uniform bound
for the convolution coefficients.  The low-frequency loss therefore has
the homogeneous size `K²/T₀`; `Bmiddle` and `Btail` are exactly the other
two terms in Teräväinen's reduction.

This proposition is deliberately *not* an `ExternalInputs` field.  The
literal printed statement of Teräväinen 2016, Lemma 1 has incompatible
normalizations and a narrower support; a cited field may be added only after
those source issues have been resolved from a corrected version or by
formalizing the Parseval proof itself. -/
def PerronParsevalAtScaleStatement
    (weight : ℕ → ℝ) (X P h hlong T₀ K : ℝ) : Prop :=
  ∃ Cparseval : ℝ, 0 < Cparseval ∧
    T₀ = X ^ (1 / 1000 : ℝ) ∧
    0 < X ∧ 0 < h ∧ h ≤ hlong ∧ hlong ≤ X / T₀ ^ (3 : ℕ) ∧
    (∀ m ∈ perronProductSupport X P,
      ‖perronProductCoefficient weight X P m‖ ≤ K) ∧
    ∀ Bmiddle Btail : ℝ,
      perronProductIntegral weight X P (X / h) ≤ Bmiddle →
      (∀ T : ℝ, X / h ≤ T →
        X / (T * h) *
          (∫ t in Set.Ioc T (2 * T),
            ‖perronProduct weight X P t‖ ^ (2 : ℕ)) ≤ Btail) →
      matomakiTeravainenShortLongVariance weight X P h hlong ≤
        Cparseval * (K ^ (2 : ℕ) / T₀ + Bmiddle + Btail)

/-- Once the fixed-scale Parseval interface is supplied, a cumulative
Dirichlet-polynomial bound gives the variance bound with exact constants.
The only surviving extra term is the homogeneous low-frequency loss
`K²/T₀`; this is where a coefficient bound must be absorbed. -/
theorem variance_le_of_parsevalAtScale_and_cumulative
    {weight : ℕ → ℝ} {X P h hlong T₀ K C L : ℝ}
    (hparseval : PerronParsevalAtScaleStatement
      weight X P h hlong T₀ K)
    (hcutoff : T₀ ≤ X / h) (hL : 0 < L)
    (hcumulative : ∀ U : ℝ, X / h ≤ U →
      perronProductIntegral weight X P U ≤
        C * (U / (X / h)) / L) :
    ∃ Cparseval : ℝ, 0 < Cparseval ∧
      matomakiTeravainenShortLongVariance weight X P h hlong ≤
        Cparseval * (K ^ (2 : ℕ) / T₀ + C / L + 2 * C / L) := by
  obtain ⟨Cparseval, hCparseval, hT₀, hX, hh, _hhLong, _hLongUpper,
      _hcoeff, hparsevalBound⟩ := hparseval
  subst T₀
  refine ⟨Cparseval, hCparseval, ?_⟩
  apply hparsevalBound (C / L) (2 * C / L)
  · exact perron_middleIntegral_le_of_cumulative weight hX hh hcumulative
  · intro T hT
    exact perron_normalizedDyadicTail_le_of_cumulative weight hX hh hT
      hcutoff hL hcumulative

def generalPerronReductionModule : ProofModule :=
  { name := "Completion.GeneralPerronReduction"
    paperLocation :=
      "Teräväinen 2016, Lemma 1 (citing Matomäki--Radziwiłł, Lemma 14), and MT23 Lemma 3.1"
    purpose :=
      "Expose the exact product coefficient and support and prove the cumulative-to-Parseval normalization. The Parseval specialization is the labelled extension E1."
    dependsOn :=
      ["Completion.PerronTarget", "Completion.PerronCumulativeBounds"]
    status := .superseded }

end

end Completion
end ExactSemiprimes
