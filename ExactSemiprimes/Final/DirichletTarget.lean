import ExactSemiprimes.Final.TypeIIComponent
import ExactSemiprimes.Final.ComplementU
import ExactSemiprimes.Final.PerronTail
import ExactSemiprimes.Completion.ComponentIntegralAssembly

/-!
# The Dirichlet-polynomial target of Proposition 7.1

For a prime block `P` with `(log X)^(1925/1763+η) ≤ P ≤ (log X)^(c-1)` and every
height `T ≥ X/(log X)^c`,

`∫_{X^(1/1000)}^T |P₁(1+it) P(1+it)|² dt ≪ (T/(X/h)) / (log X)^(2+ε₀)`.

* On `𝒰` the minorant is decomposed by [MT23, Proposition 2.2]; Type I and
  Type I/II components are bounded by the labelled extensions (E4), (E5),
  Type II components by `Final.TypeIIComponent`.
* Off `𝒰` the bound comes from `Final.ComplementU`.
* For `T ≥ X` the mean value theorem and the unique small prime factor
  (`Final.PerronTail`) suffice.
-/

namespace ExactSemiprimes
namespace Final

open Filter Real MeasureTheory
open scoped BigOperators

noncomputable section

/-- The squared-norm integrand of a continuous function is integrable on any
measurable subset of a compact interval. -/
theorem integrableOn_norm_sq_of_continuous {F : ℝ → ℂ} (hF : Continuous F)
    {E : Set ℝ} {a b : ℝ} (hE : E ⊆ Set.Icc a b) :
    IntegrableOn (fun t ↦ ‖F t‖ ^ (2 : ℕ)) E :=
  (hF.norm.pow 2).integrableOn_Icc.mono_set hE

theorem continuous_perronProduct (w : ℕ → ℝ) (X P : ℝ) :
    Continuous (fun t : ℝ ↦ Completion.perronProduct w X P t) := by
  unfold Completion.perronProduct
  exact (continuous_primeDirichletPolynomial_onePlusIT P).mul
    (Sparse.continuous_dirichletPolynomial_onePlusIT_sparse _ _)

/-- The family-size loss is absorbed: `2 (C e^{y^5})² D e^{-y^6} ≤ e^{-3y}`. -/
theorem eventually_family_absorbed {Cf D : ℝ} :
    ∀ᶠ X : ℕ in atTop,
      2 * (Cf * Real.exp ((Real.log (Real.log (X : ℝ))) ^ (5 : ℕ))) ^ (2 : ℕ) *
          (D * loglogSixSaving (X : ℝ)) ≤
        (Real.log (X : ℝ)) ^ (-3 : ℝ) := by
  have hlogNat : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hy : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hlogNat
  set L := Real.log (2 * Cf ^ 2 * |D| + 1) with hLdef
  have hKpos : 0 < 2 * Cf ^ 2 * |D| + 1 := by positivity
  have hL : 0 ≤ L := Real.log_nonneg (by nlinarith [abs_nonneg D, sq_nonneg Cf])
  have hpoly : ∀ᶠ y : ℝ in atTop, 2 * y ^ 5 + 3 * y + L ≤ y ^ 6 := by
    filter_upwards [eventually_ge_atTop (6 + L), eventually_ge_atTop (1 : ℝ)] with y hy hy1
    have h5 : 1 ≤ y ^ 5 := one_le_pow₀ hy1
    have h6 : y ^ 6 = y * y ^ 5 := by ring
    have hA : (6 + L) * y ^ 5 ≤ y * y ^ 5 := mul_le_mul_of_nonneg_right hy (by positivity)
    have hB : L ≤ L * y ^ 5 := le_mul_of_one_le_right hL h5
    have hC : y ≤ y ^ 5 := by
      calc y = y ^ 1 := (pow_one y).symm
        _ ≤ y ^ 5 := pow_le_pow_right₀ hy1 (by norm_num)
    nlinarith
  filter_upwards [hy.eventually hpoly, hlogNat.eventually (eventually_gt_atTop 1)]
    with X hX hlog1
  set y := Real.log (Real.log (X : ℝ)) with hydef
  have hlogpos : 0 < Real.log (X : ℝ) := by linarith
  have hrhs : (Real.log (X : ℝ)) ^ (-3 : ℝ) = Real.exp (-3 * y) := by
    rw [Real.rpow_def_of_pos hlogpos, hydef]; ring_nf
  rw [hrhs]
  unfold loglogSixSaving
  have hexp2 : Real.exp (y ^ 5) ^ 2 = Real.exp (2 * y ^ 5) := by
    rw [show (2 : ℝ) * y ^ 5 = ((2 : ℕ) : ℝ) * y ^ 5 by norm_num, Real.exp_nat_mul]
  have heq : Real.exp (L + 2 * y ^ 5 - y ^ 6) =
      (2 * Cf ^ 2 * |D| + 1) * (Real.exp (y ^ 5) ^ 2 * Real.exp (-(y ^ 6))) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, hLdef, Real.exp_log hKpos, hexp2]
    ring
  calc 2 * (Cf * Real.exp (y ^ 5)) ^ 2 * (D * Real.exp (-(y ^ 6)))
      ≤ (2 * Cf ^ 2 * |D| + 1) * (Real.exp (y ^ 5) ^ 2 * Real.exp (-(y ^ 6))) := by
        have he : 0 ≤ Real.exp (y ^ 5) ^ 2 * Real.exp (-(y ^ 6)) := by positivity
        have : 2 * (Cf * Real.exp (y ^ 5)) ^ 2 * (D * Real.exp (-(y ^ 6))) =
            2 * Cf ^ 2 * D * (Real.exp (y ^ 5) ^ 2 * Real.exp (-(y ^ 6))) := by ring
        rw [this]
        have h2 : 2 * Cf ^ 2 * D ≤ 2 * Cf ^ 2 * |D| + 1 := by
          nlinarith [sq_nonneg Cf, le_abs_self D]
        exact mul_le_mul_of_nonneg_right h2 he
    _ = Real.exp (L + 2 * y ^ 5 - y ^ 6) := heq.symm
    _ ≤ Real.exp (-3 * y) := by
        apply Real.exp_le_exp.mpr
        linarith

/-- Restricting a `𝒰_ε` integral to the smaller `𝒰_{ε/2}`. -/
theorem integral_largePrime_half_le {X P ε : ℝ} (hP : 1 ≤ P) (hε : 0 ≤ ε)
    {F : ℝ → ℂ} (hF : Continuous F) :
    (∫ t in largePrimeValueSet X P (ε / 2),
        ‖primeDirichletPolynomial P (onePlusIT t)‖ ^ (2 : ℕ) * ‖F t‖ ^ (2 : ℕ)) ≤
      ∫ t in largePrimeValueSet X P ε,
        ‖primeDirichletPolynomial P (onePlusIT t)‖ ^ (2 : ℕ) * ‖F t‖ ^ (2 : ℕ) := by
  have hcont : Continuous (fun t ↦
      ‖primeDirichletPolynomial P (onePlusIT t)‖ ^ (2 : ℕ) * ‖F t‖ ^ (2 : ℕ)) :=
    ((continuous_primeDirichletPolynomial_onePlusIT P).norm.pow 2).mul (hF.norm.pow 2)
  apply setIntegral_mono_set
  · exact hcont.integrableOn_Icc.mono_set (largePrimeValueSet_subset_Icc X P ε)
  · exact Filter.Eventually.of_forall (fun t ↦ by positivity)
  · exact Filter.Eventually.of_forall (largePrimeValueSet_mono hP (by linarith))

/-- **The `𝒰` part.**  Uniformly over the block window, the Perron product
has mean square `≪ (log X)^(-3)` on `𝒰_{ε/2}`. -/
theorem Upart_uniform (inputs : ExternalInputs) (ext : ParameterExtensionInputs) :
    ∀ η : ℝ, 0 < η → ∃ εₘₐₓ : ℝ, 0 < εₘₐₓ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop, ∀ P : ℝ,
        (Real.log (X : ℝ)) ^ (1925 / 1763 + η) ≤ P →
        P ≤ (Real.log (X : ℝ)) ^ (11 / 10 : ℝ) →
        (∫ t in largePrimeValueSet (X : ℝ) P (ε / 2),
            ‖Completion.perronProduct (matomakiTeravainenMinorant (X : ℝ) ε)
              (X : ℝ) P t‖ ^ (2 : ℕ)) ≤
          C * (Real.log (X : ℝ)) ^ (-3 : ℝ) := by
  intro η hη
  obtain ⟨εII, hεII, hII⟩ := typeIIComponentStatement_of_inputs inputs η hη
  obtain ⟨ε22, hε22, h22⟩ := inputs.matomakiTeravainenPropositionTwoTwo
  obtain ⟨εI, hεI, hI⟩ := ext.uniformTypeIComponent
  obtain ⟨εI2, hεI2, hI2⟩ := ext.uniformTypeIOneHalfComponent
  refine ⟨min (min (min εII ε22) (min εI εI2)) 1, by positivity, ?_⟩
  intro ε hε hεle0
  have hε1 : ε ≤ 1 := hεle0.trans (min_le_right _ _)
  have hεle := hεle0.trans (min_le_left _ _)
  have hεII' : ε ≤ εII := hεle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hε22' : ε ≤ ε22 := hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεI' : ε ≤ εI := hεle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεI2' : ε ≤ εI2 := hεle.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Cfam, Crem, Bc, Ac, hCfam, hCrem, hBc, hAc, hdec⟩ :=
    h22 ε hε hε22' 5 (le_refl _)
  obtain ⟨CI, XI, hCI, hXI, hIb⟩ := hI ε hε hεI' 5 (by norm_num) Bc Ac hBc hAc
  obtain ⟨CI2, XI2, hCI2, hXI2, hI2b⟩ := hI2 ε hε hεI2' 5 (by norm_num) Bc Ac hBc hAc
  obtain ⟨CII, hCII, NII, hIIb⟩ := hII ε hε hεII' 5 (by norm_num) Bc Ac hBc hAc
  obtain ⟨CMV, hCMV, hMV⟩ := inputs.iwaniecKowalskiTheoremNineOne
  set Cc := max CI (max CI2 CII) with hCc
  have hCc0 : 0 < Cc := lt_of_lt_of_le hCI (le_max_left _ _)
  set CR := 64 * Crem * (2 + 8 * CMV) with hCR
  refine ⟨1 + 2 * CR, by positivity, ?_⟩
  have hlogNat : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hfam := eventually_family_absorbed (Cf := Cfam) (D := Cc)
  have hsmallP := eventually_const_mul_log_rpow_le_rpow 2 (11 / 10)
    (c := ε / 100) (by positivity)
  filter_upwards [hfam, hsmallP, hlogNat.eventually_ge_atTop 2,
    eventually_ge_atTop ⌈XI⌉₊, eventually_ge_atTop ⌈XI2⌉₊, eventually_ge_atTop NII,
    eventually_ge_atTop 3] with X hfamX hsmallX hlog2 hXI' hXI2' hNII' hX3
  intro P hPlo hPhi
  have hX3' : (3 : ℝ) ≤ X := by exact_mod_cast hX3
  have hXpos : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) < X := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.log (X : ℝ) := by linarith
  have hlogpos : 0 < Real.log (X : ℝ) := by linarith
  have hP2 : 2 ≤ P := by
    have : Real.log (X : ℝ) ≤ (Real.log (X : ℝ)) ^ (1925 / 1763 + η) := by
      calc Real.log (X : ℝ) = (Real.log (X : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
    linarith
  have hP1 : 1 ≤ P := by linarith
  have hPpos : 0 < P := by linarith
  set Y : ℝ := (X : ℝ) / P with hYdef
  have hY1 : 1 ≤ Y := by
    rw [hYdef, le_div_iff₀ hPpos, one_mul]
    have : (2 : ℝ) * (Real.log (X : ℝ)) ^ (11 / 10 : ℝ) ≤ (X : ℝ) ^ (ε / 100) := hsmallX
    have hXε : (X : ℝ) ^ (ε / 100) ≤ X := by
      calc (X : ℝ) ^ (ε / 100) ≤ (X : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hX1.le (by linarith)
        _ = X := Real.rpow_one _
    have hPle : P ≤ (Real.log (X : ℝ)) ^ (11 / 10 : ℝ) := hPhi
    nlinarith [Real.rpow_nonneg hlogpos.le (11 / 10 : ℝ)]
  have hYlo : (X : ℝ) ^ (1 - ε / 100) < Y := by
    rw [hYdef, lt_div_iff₀ hPpos]
    have hsplit : (X : ℝ) = (X : ℝ) ^ (1 - ε / 100) * (X : ℝ) ^ (ε / 100) := by
      rw [← Real.rpow_add hXpos]; norm_num
    have hPlt : P < (X : ℝ) ^ (ε / 100) := by
      have hpos : 0 < (Real.log (X : ℝ)) ^ (11 / 10 : ℝ) := Real.rpow_pos_of_pos hlogpos _
      linarith
    calc (X : ℝ) ^ (1 - ε / 100) * P < (X : ℝ) ^ (1 - ε / 100) * (X : ℝ) ^ (ε / 100) :=
          mul_lt_mul_of_pos_left hPlt (Real.rpow_pos_of_pos hXpos _)
      _ = X := hsplit.symm
  have hYhi : Y ≤ (X : ℝ) / 2 := by
    rw [hYdef]; exact div_le_div_of_nonneg_left hXpos.le (by norm_num) hP2
  -- the decomposition of the minorant
  have hdecX := hdec (X : ℝ) hX3'
  dsimp only at hdecX
  obtain ⟨F, c, hFcard, hident, hcsupp, hcL2, hcases⟩ := hdecX Y hYlo hYhi
  set δ : ℝ := (Real.log (X : ℝ)) ^ (-10 * (5 : ℝ)) with hδ
  have hδ0 : 0 ≤ δ := Real.rpow_nonneg hlogpos.le _
  obtain ⟨cs, hcs⟩ :=
    Sparse.exists_componentSupportFunction_of_matomakiTeravainenCases F hδ0 hcases
  -- the Perron product as a sum of component products
  have hsupp_eq : natOpenClosedInterval ((X : ℝ) / (2 * P)) (4 * (X : ℝ) / P) =
      natOpenClosedInterval (Y / 2) (4 * Y) := by
    rw [hYdef]; congr 1 <;> ring
  have hprodEq : ∀ t : ℝ,
      Completion.perronProduct (matomakiTeravainenMinorant (X : ℝ) ε) (X : ℝ) P t =
        (∑ f ∈ F, primeDirichletPolynomial P (onePlusIT t) *
            dirichletPolynomial f (cs f) (onePlusIT t)) +
          primeDirichletPolynomial P (onePlusIT t) *
            dirichletPolynomial c (natOpenClosedInterval (Y / 4) (8 * Y))
              (onePlusIT t) := by
    intro t
    unfold Completion.perronProduct Completion.perronMinorantPolynomial
    rw [hsupp_eq, Sparse.matomakiTeravainenDecomposition_fullComponentSupports cs
      (onePlusIT t) (by linarith) hident hcsupp hcs, mul_add, Finset.mul_sum]
  set U := largePrimeValueSet (X : ℝ) P (ε / 2) with hU
  have hUmeas : MeasurableSet U := measurableSet_largePrimeValueSet _ _ _
  have hUsub : U ⊆ Set.Icc ((X : ℝ) ^ (1 / 1000 : ℝ)) X :=
    largePrimeValueSet_subset_Icc _ _ _
  have hP₁cont := continuous_primeDirichletPolynomial_onePlusIT P
  have hlo' : (Real.log (X : ℝ)) ^ (1925 / 1763 : ℝ) ≤ P :=
    (Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)).trans hPlo
  have hXI'' : XI ≤ (X : ℝ) := (Nat.le_ceil XI).trans (by exact_mod_cast hXI')
  have hXI2'' : XI2 ≤ (X : ℝ) := (Nat.le_ceil XI2).trans (by exact_mod_cast hXI2')
  have hL6 : 0 ≤ loglogSixSaving (X : ℝ) := (Real.exp_pos _).le
  -- each component
  have hcomp : ∀ f ∈ F,
      (∫ t in U, ‖primeDirichletPolynomial P (onePlusIT t) *
          dirichletPolynomial f (cs f) (onePlusIT t)‖ ^ (2 : ℕ)) ≤
        Cc * loglogSixSaving (X : ℝ) := by
    intro f hf
    have hsplit : ∀ (g : ℕ → ℂ) (S : Finset ℕ),
        (∀ t, dirichletPolynomial f (cs f) (onePlusIT t) =
          dirichletPolynomial g S (onePlusIT t)) →
        (∫ t in U, ‖primeDirichletPolynomial P (onePlusIT t) *
            dirichletPolynomial f (cs f) (onePlusIT t)‖ ^ (2 : ℕ)) =
          ∫ t in U, ‖primeDirichletPolynomial P (onePlusIT t)‖ ^ (2 : ℕ) *
            ‖dirichletPolynomial g S (onePlusIT t)‖ ^ (2 : ℕ) := by
      intro g S hgS
      congr 1; funext t
      rw [hgS t, norm_mul, mul_pow]
    rcases hcases f hf with hcase | hcase | hcase
    · obtain ⟨M₁, M₂, α, hM₁, hM₂, hα, hM₁le, hlo, hhi, hfeq⟩ := hcase
      have hpoly : ∀ t, dirichletPolynomial f (cs f) (onePlusIT t) =
          dirichletPolynomial (matomakiTeravainenTypeIValue δ M₁ M₂ α)
            (Sparse.typeIProductSupport δ M₁ M₂) (onePlusIT t) := by
        intro t
        have hfun : f = matomakiTeravainenTypeIValue δ M₁ M₂ α := funext hfeq
        rw [Sparse.dirichletPolynomial_eq_of_two_finiteSupports (hcs f hf)
          (fun n hn ↦ by
            rw [hfeq n]
            exact Sparse.matomakiTeravainenTypeIValue_eq_zero_of_not_mem_productSupport
              hδ0 hM₁ hM₂ hn), hfun]
      rw [hsplit _ _ hpoly]
      refine (integral_largePrime_half_le hP1 hε.le
        (Sparse.continuous_dirichletPolynomial_onePlusIT_sparse _ _)).trans ?_
      refine (hIb (X : ℝ) P hXI'' hlo' hPhi M₁ M₂ α hM₁ hM₂ hα hM₁le hlo hhi).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hL6
    · obtain ⟨M₁, M₂, M₃, α, β, hM₁, hM₂, hM₃, hα, hβ, hM₁le, hM₂le, hlo, hhi, hfeq⟩ :=
        hcase
      have hpoly : ∀ t, dirichletPolynomial f (cs f) (onePlusIT t) =
          dirichletPolynomial (matomakiTeravainenTypeIOneHalfValue δ M₁ M₂ M₃ α β)
            (Sparse.typeIOneHalfProductSupport δ M₁ M₂ M₃) (onePlusIT t) := by
        intro t
        have hfun : f = matomakiTeravainenTypeIOneHalfValue δ M₁ M₂ M₃ α β := funext hfeq
        rw [Sparse.dirichletPolynomial_eq_of_two_finiteSupports (hcs f hf)
          (fun n hn ↦ by
            rw [hfeq n]
            exact Sparse.matomakiTeravainenTypeIOneHalfValue_eq_zero_of_not_mem_productSupport
              hδ0 hM₁ hM₂ hM₃ hn), hfun]
      rw [hsplit _ _ hpoly]
      refine (integral_largePrime_half_le hP1 hε.le
        (Sparse.continuous_dirichletPolynomial_onePlusIT_sparse _ _)).trans ?_
      refine (hI2b (X : ℝ) P hXI2'' hlo' hPhi M₁ M₂ M₃ α β hM₁ hM₂ hM₃ hα hβ
        hM₁le hM₂le hlo hhi).trans ?_
      exact mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _)) hL6
    · obtain ⟨R, M₁, M₂, α, β, Q, hR1, hRup, hM₁, hM₂, hα, hβ, hM₁lo, hM₁hi, hlo, hhi,
        hQ, hprodQ, hαdef, hfeq⟩ := hcase
      have hpoly : ∀ t, dirichletPolynomial f (cs f) (onePlusIT t) =
          dirichletPolynomial (matomakiTeravainenTypeIIValue δ M₁ M₂ R α β)
            (Sparse.typeIIProductSupport δ M₁ M₂ R) (onePlusIT t) := by
        intro t
        have hfun : f = matomakiTeravainenTypeIIValue δ M₁ M₂ R α β := funext hfeq
        rw [Sparse.dirichletPolynomial_eq_of_two_finiteSupports (hcs f hf)
          (fun n hn ↦ by
            rw [hfeq n]
            exact Sparse.matomakiTeravainenTypeIIValue_eq_zero_of_not_mem_productSupport
              hδ0 hM₁ hM₂ hn), hfun]
      rw [hsplit _ _ hpoly]
      refine (hIIb X hNII' P hPlo hPhi R M₁ M₂ α β Q hR1 hRup hM₁ hM₂ hα hβ hM₁lo
        hM₁hi hlo hhi hQ hprodQ hαdef).trans ?_
      exact mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_max_right _ _)) hL6
  -- assembling the components and the remainder
  have hcompCont : ∀ f ∈ F, Continuous (fun t : ℝ ↦ primeDirichletPolynomial P (onePlusIT t) *
      dirichletPolynomial f (cs f) (onePlusIT t)) :=
    fun f _ ↦ hP₁cont.mul (Sparse.continuous_dirichletPolynomial_onePlusIT_sparse _ _)
  have hRcont : Continuous (fun t : ℝ ↦
      dirichletPolynomial c (natOpenClosedInterval (Y / 4) (8 * Y)) (onePlusIT t)) :=
    Sparse.continuous_dirichletPolynomial_onePlusIT_sparse _ _
  have hremCont : Continuous (fun t : ℝ ↦ primeDirichletPolynomial P (onePlusIT t) *
      dirichletPolynomial c (natOpenClosedInterval (Y / 4) (8 * Y)) (onePlusIT t)) :=
    hP₁cont.mul hRcont
  have hstep := Completion.integral_norm_componentSum_add_remainder_sq_le U F
    (fun f t ↦ primeDirichletPolynomial P (onePlusIT t) *
      dirichletPolynomial f (cs f) (onePlusIT t))
    (fun t ↦ primeDirichletPolynomial P (onePlusIT t) *
      dirichletPolynomial c (natOpenClosedInterval (Y / 4) (8 * Y)) (onePlusIT t))
    hUmeas
    (integrableOn_norm_sq_of_continuous
      ((continuous_finsetSum F (fun f hf ↦ hcompCont f hf)).add hremCont) hUsub)
    (fun f hf ↦ integrableOn_norm_sq_of_continuous (hcompCont f hf) hUsub)
    (integrableOn_norm_sq_of_continuous hremCont hUsub)
  have hrw : (∫ t in U, ‖Completion.perronProduct (matomakiTeravainenMinorant (X : ℝ) ε)
        (X : ℝ) P t‖ ^ (2 : ℕ)) =
      ∫ t in U, ‖(∑ f ∈ F, primeDirichletPolynomial P (onePlusIT t) *
          dirichletPolynomial f (cs f) (onePlusIT t)) +
        primeDirichletPolynomial P (onePlusIT t) *
          dirichletPolynomial c (natOpenClosedInterval (Y / 4) (8 * Y))
            (onePlusIT t)‖ ^ (2 : ℕ) := by
    congr 1; funext t; rw [hprodEq t]
  -- the family term
  have hsum : (∑ f ∈ F, ∫ t in U, ‖primeDirichletPolynomial P (onePlusIT t) *
      dirichletPolynomial f (cs f) (onePlusIT t)‖ ^ (2 : ℕ)) ≤
        (F.card : ℝ) * (Cc * loglogSixSaving (X : ℝ)) := by
    calc _ ≤ ∑ f ∈ F, Cc * loglogSixSaving (X : ℝ) := Finset.sum_le_sum hcomp
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard0 : (0 : ℝ) ≤ (F.card : ℝ) := Nat.cast_nonneg _
  have hfamterm : 2 * (F.card : ℝ) * (∑ f ∈ F, ∫ t in U,
      ‖primeDirichletPolynomial P (onePlusIT t) *
        dirichletPolynomial f (cs f) (onePlusIT t)‖ ^ (2 : ℕ)) ≤
        (Real.log (X : ℝ)) ^ (-3 : ℝ) := by
    calc _ ≤ 2 * (F.card : ℝ) * ((F.card : ℝ) * (Cc * loglogSixSaving (X : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 2 * (F.card : ℝ) ^ (2 : ℕ) * (Cc * loglogSixSaving (X : ℝ)) := by ring
      _ ≤ 2 * (Cfam * Real.exp ((Real.log (Real.log (X : ℝ))) ^ (5 : ℕ))) ^ (2 : ℕ) *
            (Cc * loglogSixSaving (X : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hcard0 hFcard 2) (by norm_num))
            (mul_nonneg hCc0.le hL6)
      _ ≤ _ := hfamX
  -- the remainder term
  have hUsub' : U ⊆ Set.Icc (-(X : ℝ)) X := by
    intro t ht
    have h := hUsub ht
    have h0 : (0 : ℝ) ≤ (X : ℝ) ^ (1 / 1000 : ℝ) := Real.rpow_nonneg hXpos.le _
    exact ⟨by linarith [h.1], h.2⟩
  have hrem1 : (∫ t in U, ‖primeDirichletPolynomial P (onePlusIT t) *
      dirichletPolynomial c (natOpenClosedInterval (Y / 4) (8 * Y))
        (onePlusIT t)‖ ^ (2 : ℕ)) ≤
      4 * ∫ t in U, ‖dirichletPolynomial c (natOpenClosedInterval (Y / 4) (8 * Y))
        (onePlusIT t)‖ ^ (2 : ℕ) := by
    calc _ = ∫ t in U, ‖primeDirichletPolynomial P (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖dirichletPolynomial c (natOpenClosedInterval (Y / 4) (8 * Y))
            (onePlusIT t)‖ ^ (2 : ℕ) := by
          congr 1; funext t; rw [norm_mul, mul_pow]
      _ ≤ _ := integral_primeFactor_mul_le_four_mul hP1 hUmeas hUsub hRcont
  have hrem2 : (∫ t in U, ‖dirichletPolynomial c (natOpenClosedInterval (Y / 4) (8 * Y))
        (onePlusIT t)‖ ^ (2 : ℕ)) ≤
      ∫ t in Set.Icc (-(X : ℝ)) X,
        ‖dirichletPolynomial c (natOpenClosedInterval (Y / 4) (8 * Y))
          (onePlusIT t)‖ ^ (2 : ℕ) := by
    apply setIntegral_mono_set
    · exact (hRcont.norm.pow 2).integrableOn_Icc
    · exact Filter.Eventually.of_forall (fun t ↦ by positivity)
    · exact Filter.Eventually.of_forall hUsub'
  have hrem3 := remainder_meanSquare_le hCMV (fun N T a hN hT ↦ hMV N T a hN hT) c
    (T := (X : ℝ)) hY1 hX1.le hcL2
  have hL5pos : 0 < (Real.log (X : ℝ)) ^ (5 : ℝ) := Real.rpow_pos_of_pos hlogpos _
  have hYpos : 0 < Y := by linarith
  have hXY : (X : ℝ) = P * Y := by
    rw [hYdef]; field_simp
  have hrem4 : 4 * ((2 * (X : ℝ) + CMV * (8 * Y)) *
        (16 * (Crem * Y / (Real.log (X : ℝ)) ^ (5 : ℝ)) / Y ^ 2)) =
      64 * Crem * (2 * P + 8 * CMV) / (Real.log (X : ℝ)) ^ (5 : ℝ) := by
    rw [hXY]; field_simp; ring
  have hPL : P / (Real.log (X : ℝ)) ^ (5 : ℝ) ≤ (Real.log (X : ℝ)) ^ (-3 : ℝ) := by
    calc P / (Real.log (X : ℝ)) ^ (5 : ℝ) ≤
          (Real.log (X : ℝ)) ^ (11 / 10 : ℝ) / (Real.log (X : ℝ)) ^ (5 : ℝ) :=
          div_le_div_of_nonneg_right hPhi hL5pos.le
      _ = (Real.log (X : ℝ)) ^ (11 / 10 - 5 : ℝ) := (Real.rpow_sub hlogpos _ _).symm
      _ ≤ (Real.log (X : ℝ)) ^ (-3 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlog1 (by norm_num)
  have hrem5 : 64 * Crem * (2 * P + 8 * CMV) / (Real.log (X : ℝ)) ^ (5 : ℝ) ≤
      CR * (Real.log (X : ℝ)) ^ (-3 : ℝ) := by
    have h1 : 2 * P + 8 * CMV ≤ (2 + 8 * CMV) * P := by
      have h0 : CMV * 1 ≤ CMV * P := mul_le_mul_of_nonneg_left hP1 hCMV.le
      linarith only [h0]
    calc 64 * Crem * (2 * P + 8 * CMV) / (Real.log (X : ℝ)) ^ (5 : ℝ) ≤
          64 * Crem * ((2 + 8 * CMV) * P) / (Real.log (X : ℝ)) ^ (5 : ℝ) := by
          apply div_le_div_of_nonneg_right _ hL5pos.le
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = CR * (P / (Real.log (X : ℝ)) ^ (5 : ℝ)) := by rw [hCR]; ring
      _ ≤ CR * (Real.log (X : ℝ)) ^ (-3 : ℝ) :=
          mul_le_mul_of_nonneg_left hPL (by rw [hCR]; positivity)
  have hremU : (∫ t in U, ‖primeDirichletPolynomial P (onePlusIT t) *
      dirichletPolynomial c (natOpenClosedInterval (Y / 4) (8 * Y))
        (onePlusIT t)‖ ^ (2 : ℕ)) ≤ CR * (Real.log (X : ℝ)) ^ (-3 : ℝ) := by
    calc _ ≤ _ := hrem1
      _ ≤ 4 * ∫ t in Set.Icc (-(X : ℝ)) X,
          ‖dirichletPolynomial c (natOpenClosedInterval (Y / 4) (8 * Y))
            (onePlusIT t)‖ ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hrem2 (by norm_num)
      _ ≤ 4 * ((2 * (X : ℝ) + CMV * (8 * Y)) *
          (16 * (Crem * Y / (Real.log (X : ℝ)) ^ (5 : ℝ)) / Y ^ 2)) :=
          mul_le_mul_of_nonneg_left hrem3 (by norm_num)
      _ = _ := hrem4
      _ ≤ _ := hrem5
  rw [hrw]
  refine hstep.trans ?_
  linarith only [hfamterm, hremU]

/-! ## The block target on all heights -/

/-- Splitting a set integral of a nonnegative continuous function along a
cover by two measurable subsets of a compact interval. -/
theorem integral_le_of_subset_union {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) {S A B : Set ℝ} {a b : ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAsub : A ⊆ Set.Icc a b) (hBsub : B ⊆ Set.Icc a b) (hS : S ⊆ A ∪ B) :
    (∫ t in S, f t) ≤ (∫ t in A, f t) + ∫ t in B, f t := by
  have hint : IntegrableOn f (Set.Icc a b) := hf.integrableOn_Icc
  calc (∫ t in S, f t) ≤ ∫ t in A ∪ B, f t := by
        apply setIntegral_mono_set (hint.mono_set (Set.union_subset hAsub hBsub))
        · exact Filter.Eventually.of_forall (fun t ↦ hf0 t)
        · exact Filter.Eventually.of_forall hS
    _ = (∫ t in A, f t) + ∫ t in B \ A, f t := by
        rw [← Set.union_sdiff_self]
        exact setIntegral_union Set.disjoint_sdiff_right (hB.diff hA)
          (hint.mono_set hAsub) (hint.mono_set (Set.sdiff_subset.trans hBsub))
    _ ≤ (∫ t in A, f t) + ∫ t in B, f t := by
        have : (∫ t in B \ A, f t) ≤ ∫ t in B, f t := by
          apply setIntegral_mono_set (hint.mono_set hBsub)
          · exact Filter.Eventually.of_forall (fun t ↦ hf0 t)
          · exact Filter.Eventually.of_forall Set.sdiff_subset
        linarith

theorem measurableSet_sectionFiveSmallPrimeSet (X P ε T : ℝ) :
    MeasurableSet (Completion.sectionFiveSmallPrimeSet X P ε T) :=
  measurableSet_Icc.inter (measurableSet_le
    (continuous_primeDirichletPolynomial_onePlusIT P).norm.measurable measurable_const)

theorem sectionFiveSmallPrimeSet_subset_Icc (X P ε T : ℝ) :
    Completion.sectionFiveSmallPrimeSet X P ε T ⊆ Set.Icc (X ^ (1 / 1000 : ℝ)) T :=
  Set.inter_subset_left

/-- Every height in `(T₁,T₂] ⊆ [X^(1/1000),X]` is either in `𝒰` or in the
small-value set. -/
theorem Ioc_subset_largePrime_union_small {X P ε T₁ T₂ : ℝ}
    (h1 : X ^ (1 / 1000 : ℝ) ≤ T₁) (h2 : T₂ ≤ X) :
    Set.Ioc T₁ T₂ ⊆ largePrimeValueSet X P ε ∪
      Completion.sectionFiveSmallPrimeSet X P ε T₂ := by
  intro t ht
  rcases le_total (P ^ (-ε / 10)) ‖primeDirichletPolynomial P (onePlusIT t)‖ with h | h
  · exact Or.inl ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, h⟩
  · exact Or.inr ⟨⟨by linarith [ht.1], ht.2⟩, h⟩

theorem mul_log_le_of_le_rpow_sub_one {L c P : ℝ} (hL : 0 < L)
    (hPhi : P ≤ L ^ (c - 1)) : P * L ≤ L ^ c := by
  calc P * L ≤ L ^ (c - 1) * L := mul_le_mul_of_nonneg_right hPhi hL.le
    _ = L ^ c := by rw [← Real.rpow_add_one hL.ne']; ring_nf

theorem div_mul_le_one_of_div_le {X T h : ℝ} (hh : 0 < h) (hT0 : 0 < T)
    (hT : X / h ≤ T) : X / (T * h) ≤ 1 := by
  rw [div_le_one (mul_pos hT0 hh)]
  have := (div_le_iff₀ hh).mp hT
  linarith only [this]

theorem middle_ratio_le {X L c P : ℝ} (hX : 0 < X) (hL : 0 < L) (_hLc : 0 < L ^ c)
    (hPL : P * L ≤ L ^ c) :
    X / (L ^ c / 2) * P / (X * L) ≤ 2 / L ^ (2 : ℕ) := by
  have heq : X / (L ^ c / 2) * P / (X * L) = 2 * P / (L ^ c * L) := by
    field_simp
  rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 2 * P * L ^ (2 : ℕ) = 2 * L * (P * L) := by ring
  have h2 : 2 * (L ^ c * L) = 2 * L * L ^ c := by ring
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left hPL (by positivity)

theorem tail_ratio_le {X L c P T : ℝ} (hX : 0 < X) (hL : 0 < L) (_hLc : 0 < L ^ c)
    (hT : 0 < T) (hPL : P * L ≤ L ^ c) :
    X / (T * (L ^ c / 2)) * (2 * T * P / (X * L)) ≤ 4 / L ^ (2 : ℕ) := by
  have heq : X / (T * (L ^ c / 2)) * (2 * T * P / (X * L)) = 4 * P / (L ^ c * L) := by
    field_simp; ring
  rw [heq, div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 4 * P * L ^ (2 : ℕ) = 4 * L * (P * L) := by ring
  have h2 : 4 * (L ^ c * L) = 4 * L * L ^ c := by ring
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left hPL (by positivity)

theorem mv_tail_le {X T L c CMV K : ℝ} (hX : 0 < X) (hT : 0 < T) (hLc : 0 < L ^ c)
    (hCMV : 0 ≤ CMV) (hXT : X < 2 * T) :
    X / (T * (L ^ c / 2)) * ((2 * (2 * T) + CMV * (8 * X)) * (32 * K ^ (2 : ℕ) / X)) ≤
      64 * K ^ (2 : ℕ) * (4 + 16 * CMV) * (1 / L ^ c) := by
  have heq : X / (T * (L ^ c / 2)) * ((2 * (2 * T) + CMV * (8 * X)) *
      (32 * K ^ (2 : ℕ) / X)) =
      64 * K ^ (2 : ℕ) * (4 + 8 * CMV * (X / T)) * (1 / L ^ c) := by
    field_simp; ring
  rw [heq]
  have hXT' : X / T ≤ 2 := by
    rw [div_le_iff₀ hT]; linarith only [hXT]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have : CMV * (X / T) ≤ CMV * 2 := mul_le_mul_of_nonneg_left hXT' hCMV
  linarith only [this]

theorem rpow_neg_mul_inv_sq {L e : ℝ} (hL : 0 < L) :
    L ^ (-e) * (1 / L ^ (2 : ℕ)) = L ^ (-(2 + e)) := by
  rw [show -(2 + e) = -e + -2 by ring, Real.rpow_add hL, Real.rpow_neg hL.le (2 : ℝ),
    Real.rpow_two]
  ring

/-- **The Dirichlet-polynomial target of Proposition 7.1.**  With
`h = (log X)^c / 2` and `T₀ = X^(1/1000)`, uniformly over the block window,
both the middle range `(T₀, X/h]` and every tail `(T, 2T]`, `T ≥ X/h`, save
`(log X)^(2+ε/10)`. -/
theorem blockTarget_uniform (inputs : ExternalInputs) (ext : ParameterExtensionInputs)
    {c : ℝ} (hc2 : 2 < c) (hc : c ≤ 21 / 10) :
    ∀ η : ℝ, 0 < η → ∃ εₘₐₓ : ℝ, 0 < εₘₐₓ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop, ∀ P : ℝ,
        (Real.log (X : ℝ)) ^ (1925 / 1763 + η) ≤ P → P ≤ (Real.log (X : ℝ)) ^ (c - 1) →
        (∫ t in Set.Ioc ((X : ℝ) ^ (1 / 1000 : ℝ))
            ((X : ℝ) / ((Real.log (X : ℝ)) ^ c / 2)),
            ‖Completion.perronProduct (matomakiTeravainenMinorant (X : ℝ) ε)
              (X : ℝ) P t‖ ^ (2 : ℕ)) ≤
          C * (Real.log (X : ℝ)) ^ (-(2 + ε / 10)) ∧
        ∀ T : ℝ, (X : ℝ) / ((Real.log (X : ℝ)) ^ c / 2) ≤ T →
          (X : ℝ) / (T * ((Real.log (X : ℝ)) ^ c / 2)) *
            (∫ t in Set.Ioc T (2 * T),
              ‖Completion.perronProduct (matomakiTeravainenMinorant (X : ℝ) ε)
                (X : ℝ) P t‖ ^ (2 : ℕ)) ≤
          C * (Real.log (X : ℝ)) ^ (-(2 + ε / 10)) := by
  intro η hη
  obtain ⟨εU, hεU, hU⟩ := Upart_uniform inputs ext η hη
  obtain ⟨εC, CC, hεC, hCC, hcomp⟩ := complementU_uniform inputs ext.uniformRoughPairSieve
  obtain ⟨ε24, hε24, heq24⟩ := inputs.matomakiTeravainenEquationTwoFour
  obtain ⟨CMV, hCMV, hMV⟩ := inputs.iwaniecKowalskiTheoremNineOne
  have hc2' : 0 < 10 * (c - 2) := by linarith
  refine ⟨min (min εU εC) (min ε24 (min (10 * (c - 2)) 1)), by positivity, ?_⟩
  intro ε hε hεle
  have hεU' : ε ≤ εU := hεle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεC' : ε ≤ εC := hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε24' : ε ≤ ε24 := hεle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεc : ε ≤ 10 * (c - 2) := hεle.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hε1 : ε ≤ 1 := hεle.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨CU, hCU, hUev⟩ := hU ε hε hεU'
  set K : ℝ := 5324 with hK
  set Ctail : ℝ := 64 * K ^ (2 : ℕ) * (4 + 16 * CMV) with hCtail
  have hCtail0 : 0 < Ctail := by rw [hCtail, hK]; positivity
  refine ⟨CU + 5 * CC + Ctail, by positivity, ?_⟩
  have hlogNat : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgeo := tendsto_natCast_atTop_atTop.eventually
    Completion.eventually_perronSupport_inside_equationTwoFour_range_wide
  have hXe : ∀ᶠ X : ℕ in atTop, Real.exp 1 < (X : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  have hPz := eventually_const_mul_log_rpow_le_rpow 2 (11 / 10) (c := 1 / 10) (by norm_num)
  have hLc := eventually_const_mul_log_rpow_le_rpow 1 (21 / 10) (c := 1 / 2) (by norm_num)
  filter_upwards [hUev, hcomp, hgeo, hXe, hPz, hLc, hlogNat.eventually_ge_atTop 2,
    eventually_ge_atTop 3] with X hUX hcompX hgeoX hXeX hPzX hLcX hlog2 hX3
  intro P hPlo hPhi
  have hX3' : (3 : ℝ) ≤ X := by exact_mod_cast hX3
  have hXpos : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) < X := by linarith
  set L := Real.log (X : ℝ) with hL
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hLP : L ≤ P := by
    calc L = L ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ L ^ (1925 / 1763 + η) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ ≤ P := hPlo
  have hPpos : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hP11 : P ≤ L ^ (11 / 10 : ℝ) :=
    hPhi.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  -- sizes
  have hLc1 : L ≤ L ^ c := by
    calc L = L ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ L ^ c := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hLc2 : 2 ≤ L ^ c := by linarith
  have hLcpos : 0 < L ^ c := by linarith
  have hPL : P * L ≤ L ^ c := mul_log_le_of_le_rpow_sub_one hLpos hPhi
  set h := L ^ c / 2 with hh
  have hhpos : 0 < h := by rw [hh]; positivity
  have hh1 : 1 ≤ h := by rw [hh]; linarith
  set H := (X : ℝ) / h with hH
  have hHle : H ≤ X := by rw [hH]; exact div_le_self hXpos.le hh1
  have hHlo : (X : ℝ) / L ^ c ≤ H := by
    rw [hH, hh]; apply div_le_div_of_nonneg_left hXpos.le (by positivity); linarith
  have hT0H : (X : ℝ) ^ (1 / 1000 : ℝ) ≤ H := by
    have hsq : (X : ℝ) = (X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hXpos]; norm_num
    have hLcX : L ^ c ≤ (X : ℝ) ^ (1 / 2 : ℝ) := by
      have : L ^ c ≤ L ^ (21 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 hc
      linarith
    have hsqpos : 0 < (X : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hXpos _
    have h1 : (X : ℝ) ^ (1 / 2 : ℝ) ≤ (X : ℝ) / L ^ c := by
      rw [le_div_iff₀ hLcpos]
      calc (X : ℝ) ^ (1 / 2 : ℝ) * L ^ c ≤ (X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left hLcX hsqpos.le
        _ = X := hsq.symm
    have h2 : (X : ℝ) ^ (1 / 1000 : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num)
    linarith
  have hT0pos : 0 < (X : ℝ) ^ (1 / 1000 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hT01 : 1 ≤ (X : ℝ) ^ (1 / 1000 : ℝ) := Real.one_le_rpow hX1.le (by norm_num)
  -- the saving factor
  have hPε : P ^ (-ε / 10) ≤ L ^ (-ε / 10) :=
    Real.rpow_le_rpow_of_nonpos hLpos hLP (by linarith)
  have hL3 : L ^ (-3 : ℝ) ≤ L ^ (-(2 + ε / 10)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hLsave : L ^ (-ε / 10) * (1 / L ^ (2 : ℕ)) = L ^ (-(2 + ε / 10)) := by
    rw [show -ε / 10 = -(ε / 10) by ring]; exact rpow_neg_mul_inv_sq hLpos
  have hsave0 : 0 ≤ L ^ (-(2 + ε / 10)) := Real.rpow_nonneg hLpos.le _
  -- the integrand
  set f : ℝ → ℝ := fun t ↦ ‖Completion.perronProduct (matomakiTeravainenMinorant (X : ℝ) ε)
    (X : ℝ) P t‖ ^ (2 : ℕ) with hf
  have hfcont : Continuous f := (continuous_perronProduct _ _ _).norm.pow 2
  have hf0 : ∀ t, 0 ≤ f t := fun t ↦ by rw [hf]; positivity
  have hUmeas := measurableSet_largePrimeValueSet (X : ℝ) P (ε / 2)
  have hUsub := largePrimeValueSet_subset_Icc (X : ℝ) P (ε / 2)
  have hUbound : (∫ t in largePrimeValueSet (X : ℝ) P (ε / 2), f t) ≤ CU * L ^ (-3 : ℝ) :=
    hUX P hPlo hP11
  -- the split bound on `(T₁, T₂]` with `T₂ ≤ X`
  have hsplit : ∀ T₁ T₂ : ℝ, (X : ℝ) ^ (1 / 1000 : ℝ) ≤ T₁ → H ≤ T₂ → T₂ ≤ X →
      (∫ t in Set.Ioc T₁ T₂, f t) ≤
        CU * L ^ (-3 : ℝ) + CC * P ^ (-ε / 10) *
          (T₂ * P / ((X : ℝ) * L) + 1 / L ^ (2 : ℕ)) := by
    intro T₁ T₂ hT₁ hT₂ hT₂X
    have hsmall := hcompX P c ε T₂ hLP hPhi hc hε hεC' (hHlo.trans hT₂) hT₂X
    have hcov := integral_le_of_subset_union hfcont hf0 hUmeas
      (measurableSet_sectionFiveSmallPrimeSet (X : ℝ) P (ε / 2) T₂)
      hUsub ((sectionFiveSmallPrimeSet_subset_Icc _ _ _ _).trans
        (Set.Icc_subset_Icc le_rfl hT₂X))
      (Ioc_subset_largePrime_union_small (P := P) (ε := ε / 2) hT₁ hT₂X)
    have hexp : -(ε / 2) / 10 = -ε / 20 := by ring
    exact hcov.trans (add_le_add hUbound hsmall)
  constructor
  · -- the middle range
    have hm := hsplit ((X : ℝ) ^ (1 / 1000 : ℝ)) H le_rfl le_rfl hHle
    have hHP : H * P / ((X : ℝ) * L) ≤ 2 / L ^ (2 : ℕ) :=
      middle_ratio_le hXpos hLpos hLcpos hPL
    calc (∫ t in Set.Ioc ((X : ℝ) ^ (1 / 1000 : ℝ)) H, f t)
        ≤ CU * L ^ (-3 : ℝ) + CC * P ^ (-ε / 10) *
          (H * P / ((X : ℝ) * L) + 1 / L ^ (2 : ℕ)) := hm
      _ ≤ CU * L ^ (-(2 + ε / 10)) + CC * L ^ (-ε / 10) * (3 * (1 / L ^ (2 : ℕ))) := by
          gcongr
          have : 2 / L ^ (2 : ℕ) = 2 * (1 / L ^ (2 : ℕ)) := by ring
          linarith only [hHP, this]
      _ = (CU + 3 * CC) * L ^ (-(2 + ε / 10)) := by rw [← hLsave]; ring
      _ ≤ (CU + 5 * CC + Ctail) * L ^ (-(2 + ε / 10)) := by
          apply mul_le_mul_of_nonneg_right _ hsave0; linarith only [hCC, hCtail0]
  · intro T hT
    have hTpos : 0 < T := by linarith only [hT, hT0H, hT0pos]
    have hfac0 : 0 ≤ (X : ℝ) / (T * h) := by positivity
    have hfac1 : (X : ℝ) / (T * h) ≤ 1 := div_mul_le_one_of_div_le hhpos hTpos hT
    rcases le_or_gt (2 * T) X with h2T | h2T
    · have hm := hsplit T (2 * T) (hT0H.trans hT) (by linarith) h2T
      have hA : (X : ℝ) / (T * h) * (2 * T * P / ((X : ℝ) * L)) ≤ 4 / L ^ (2 : ℕ) :=
        tail_ratio_le hXpos hLpos hLcpos hTpos hPL
      calc (X : ℝ) / (T * h) * (∫ t in Set.Ioc T (2 * T), f t)
          ≤ (X : ℝ) / (T * h) * (CU * L ^ (-3 : ℝ) + CC * P ^ (-ε / 10) *
              (2 * T * P / ((X : ℝ) * L) + 1 / L ^ (2 : ℕ))) :=
            mul_le_mul_of_nonneg_left hm hfac0
        _ = (X : ℝ) / (T * h) * (CU * L ^ (-3 : ℝ)) + CC * P ^ (-ε / 10) *
              ((X : ℝ) / (T * h) * (2 * T * P / ((X : ℝ) * L)) +
                (X : ℝ) / (T * h) * (1 / L ^ (2 : ℕ))) := by ring
        _ ≤ 1 * (CU * L ^ (-3 : ℝ)) + CC * L ^ (-ε / 10) *
              (4 / L ^ (2 : ℕ) + 1 * (1 / L ^ (2 : ℕ))) := by
            gcongr
        _ ≤ CU * L ^ (-(2 + ε / 10)) + 5 * CC * (L ^ (-ε / 10) * (1 / L ^ (2 : ℕ))) := by
            have : CU * L ^ (-3 : ℝ) ≤ CU * L ^ (-(2 + ε / 10)) :=
              mul_le_mul_of_nonneg_left hL3 hCU.le
            have e : CC * L ^ (-ε / 10) * (4 / L ^ (2 : ℕ) + 1 * (1 / L ^ (2 : ℕ))) =
                5 * CC * (L ^ (-ε / 10) * (1 / L ^ (2 : ℕ))) := by ring
            linarith only [this, e]
        _ = (CU + 5 * CC) * L ^ (-(2 + ε / 10)) := by rw [hLsave]; ring
        _ ≤ (CU + 5 * CC + Ctail) * L ^ (-(2 + ε / 10)) := by
            apply mul_le_mul_of_nonneg_right _ hsave0; linarith only [hCtail0]
    · -- `T > X/2`: the mean value theorem
      have hT1 : 1 ≤ 2 * T := by linarith only [hT, hT0H, hT01]
      obtain ⟨_, hsupLo, hsupHi⟩ := hgeoX (scaleExponent (X : ℝ) P)
        (le_scaleExponent_of_rpow_le hXeX hPpos (by rw [Real.rpow_one]; exact hLP))
        (scaleExponent_le_of_le_rpow hXeX hPpos hP11)
      rw [rpow_scaleExponent hXeX hPpos] at hsupLo hsupHi
      have hPzX0 : 2 * L ^ (11 / 10 : ℝ) ≤ (X : ℝ) ^ (1 / 10 : ℝ) := hPzX
      have hPzX : 2 * P < (X : ℝ) ^ (2 / 11 : ℝ) := by
        have h1 : (X : ℝ) ^ (1 / 10 : ℝ) < (X : ℝ) ^ (2 / 11 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt hX1 (by norm_num)
        have h2 : 2 * P ≤ 2 * L ^ (11 / 10 : ℝ) := by linarith only [hP11]
        linarith only [h1, h2, hPzX0]
      have hcoeff : ∀ m ∈ Completion.perronProductSupport (X : ℝ) P,
          ‖Completion.perronProductCoefficient (matomakiTeravainenMinorant (X : ℝ) ε)
            (X : ℝ) P m‖ ≤ K := fun m _ ↦
        minorant_productCoefficient_le_5324 hX3' hPpos hε hε24' heq24 hsupLo hsupHi hPzX m
      have hmv := perronProduct_meanSquare_le hCMV (fun N T a hN hT ↦ hMV N T a hN hT)
        (matomakiTeravainenMinorant (X : ℝ) ε) (X := (X : ℝ)) (P := P) (K := K)
        (T := 2 * T) hX1.le hPpos (by rw [hK]; norm_num) hT1 hcoeff
      have hsub : (∫ t in Set.Ioc T (2 * T), f t) ≤ ∫ t in Set.Icc (-(2 * T)) (2 * T), f t := by
        apply setIntegral_mono_set hfcont.integrableOn_Icc
        · exact Filter.Eventually.of_forall (fun t ↦ hf0 t)
        · exact Filter.Eventually.of_forall (fun t ht ↦ ⟨by linarith [ht.1], ht.2⟩)
      have hLcsave : 1 / L ^ c ≤ L ^ (-(2 + ε / 10)) := by
        rw [one_div, ← Real.rpow_neg hLpos.le]
        exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      have hbound : (X : ℝ) / (T * h) * ((2 * (2 * T) + CMV * (8 * (X : ℝ))) *
          (32 * K ^ (2 : ℕ) / X)) ≤ Ctail * (1 / L ^ c) :=
        mv_tail_le hXpos hTpos hLcpos hCMV.le h2T
      calc (X : ℝ) / (T * h) * (∫ t in Set.Ioc T (2 * T), f t)
          ≤ (X : ℝ) / (T * h) * ((2 * (2 * T) + CMV * (8 * (X : ℝ))) *
              (32 * K ^ (2 : ℕ) / X)) :=
            mul_le_mul_of_nonneg_left (hsub.trans hmv) hfac0
        _ ≤ Ctail * (1 / L ^ c) := hbound
        _ ≤ Ctail * L ^ (-(2 + ε / 10)) := mul_le_mul_of_nonneg_left hLcsave hCtail0.le
        _ ≤ (CU + 5 * CC + Ctail) * L ^ (-(2 + ε / 10)) := by
            apply mul_le_mul_of_nonneg_right _ hsave0; linarith

end

end Final
end ExactSemiprimes
