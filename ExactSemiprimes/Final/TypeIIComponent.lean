import ExactSemiprimes.Extensions
import ExactSemiprimes.Final.SparseUniform
import ExactSemiprimes.Completion.TypeIIAnalyticPartition
import ExactSemiprimes.Completion.TypeIIClosure
import ExactSemiprimes.Final.TypeIIDensityBins

/-!
# The Type II component bound

This is the new part of the argument (paper, Proposition 5.1 and Section 6),
assembled into the form in which it enters Proposition 7.1: for
every Type II convolution `F` of [MT23, Proposition 2.2(iii)] at
`Y = X/P₁`, and uniformly for `P₁ ∈ [(log X)^(1925/1763+η), (log X)^(11/10)]`,

`∫_𝒰 |P₁(1+it)|² |F(1+it)|² dt ≪ exp(-(log log X)^6)`.

The set `𝒰` uses the threshold `P₁^(-ε/20)` (i.e. `ε/2` in place of `ε`);
since `𝒰_{ε/2} ⊆ 𝒰_ε`, this is the version needed when the remaining
components are estimated on `𝒰_ε`.

The large-value part uses Proposition 5.1 (threshold `17/70`).  Each
medium bin is treated by one of the three arguments of
`Final/TypeIIDensityBins.lean`: the length-dependent density bound for the
powered first factor, the density bound for the second factor, or the two
sparse Heath-Brown branches.  This is where the window starts at
`a = 1925/1763`.

All analytic input comes from `ExternalInputs` (Guth--Maynard through the
proved Lemma 4.3 and Proposition 5.1, Heath-Brown's sparse mean value
theorem through the proved Section 6, Hildebrand--Tenenbaum, and MT23
equation (5.6)).
-/

namespace ExactSemiprimes
namespace Final

open Filter Real MeasureTheory
open scoped BigOperators

noncomputable section

/-- The Type II component bound, uniformly over the block window. -/
def TypeIIComponentStatement : Prop :=
  ∀ η : ℝ, 0 < η → ∃ εₘₐₓ : ℝ, 0 < εₘₐₓ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∀ A : ℝ, 5 ≤ A →
        ∀ Bcoeff Acoeff : ℝ, 0 ≤ Bcoeff → 1 ≤ Acoeff →
          ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ,
            ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ,
              (Real.log (X : ℝ)) ^ (1925 / 1763 + η) ≤ P →
              P ≤ (Real.log (X : ℝ)) ^ (11 / 10 : ℝ) →
              ∀ (R : ℕ) (M₁ M₂ : ℝ) (α β : ℕ → ℂ) (Q : Fin R → ℝ),
                1 ≤ R →
                R ≤ ⌊Real.log ((X : ℝ) ^ (2 / 11 : ℝ)) /
                  Real.log (Real.exp (Real.log (X : ℝ) /
                    (Real.log (Real.log (X : ℝ))) ^ (3 : ℕ)))⌋₊ →
                0 < M₁ → 0 < M₂ →
                IsDivisorBoundedByConstant Bcoeff Acoeff α →
                IsDivisorBoundedByConstant Bcoeff Acoeff β →
                (X : ℝ) ^ (ε / 2) ≤ M₁ → M₁ ≤ (X : ℝ) ^ (2 / 11 : ℝ) →
                (X : ℝ) / P / 2 < M₁ * M₂ → M₁ * M₂ ≤ 4 * ((X : ℝ) / P) →
                (∀ j : Fin R,
                  Real.exp (Real.log (X : ℝ) /
                      (Real.log (Real.log (X : ℝ))) ^ (3 : ℕ)) ≤ Q j ∧
                    Q j < (X : ℝ) ^ (2 / 11 : ℝ)) →
                (∏ j, Q j) = M₁ →
                (∀ m, α m = matomakiTeravainenStructuredTypeIICoefficient
                  ((Real.log (X : ℝ)) ^ (-10 * A)) R Q m) →
                (∫ t in largePrimeValueSet (X : ℝ) P (ε / 2),
                    ‖primeDirichletPolynomial P (onePlusIT t)‖ ^ (2 : ℕ) *
                      ‖dirichletPolynomial
                          (matomakiTeravainenTypeIIValue
                            ((Real.log (X : ℝ)) ^ (-10 * A)) M₁ M₂ R α β)
                          (Sparse.typeIIProductSupport
                            ((Real.log (X : ℝ)) ^ (-10 * A)) M₁ M₂ R)
                          (onePlusIT t)‖ ^ (2 : ℕ)) ≤
                  C * loglogSixSaving (X : ℝ)

/-! ## Elementary facts about `P₁` and `𝒰` -/

theorem primeDirichletPolynomial_eq_primeBase (P : ℝ) (s : ℂ) :
    primeDirichletPolynomial P s =
      Sparse.primeBasePolynomial (dyadicPrimes P) s := by
  simp [primeDirichletPolynomial, dirichletPolynomial,
    Sparse.primeBasePolynomial]

/-- On the line `Re(s)=1`, `|P₁(1+it)| ≤ ∑_{P<p≤2P} 1/p ≤ 2`. -/
theorem norm_primeDirichletPolynomial_onePlusIT_le_two
    {P : ℝ} (hP : 1 ≤ P) (t : ℝ) :
    ‖primeDirichletPolynomial P (onePlusIT t)‖ ≤ 2 := by
  have hPpos : 0 < P := by linarith
  unfold primeDirichletPolynomial dirichletPolynomial
  calc ‖∑ p ∈ dyadicPrimes P, (fun _ ↦ (1 : ℂ)) p * (p : ℂ) ^ (-onePlusIT t)‖
      ≤ ∑ p ∈ dyadicPrimes P, ‖(fun _ ↦ (1 : ℂ)) p * (p : ℂ) ^ (-onePlusIT t)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _p ∈ dyadicPrimes P, P⁻¹ := by
        apply Finset.sum_le_sum
        intro p hp
        have hpmem := Finset.mem_filter.mp hp
        have hpr := (mem_dyadicInterval hPpos.le).mp hpmem.1
        have hppos : (0 : ℝ) < p := hPpos.trans hpr.1
        rw [one_mul, Complex.norm_natCast_cpow_of_pos (by exact_mod_cast hppos)]
        have hre : (-onePlusIT t).re = -1 := by
          simp [onePlusIT]
        rw [hre, Real.rpow_neg_one]
        exact inv_anti₀ hPpos hpr.1.le
    _ = ((dyadicPrimes P).card : ℝ) * P⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * P) * P⁻¹ :=
        mul_le_mul_of_nonneg_right
          (Completion.dyadicPrimes_card_cast_le_two_mul hPpos.le)
          (inv_nonneg.mpr hPpos.le)
    _ = 2 := by field_simp

theorem continuous_primeDirichletPolynomial_onePlusIT (P : ℝ) :
    Continuous (fun t : ℝ ↦ primeDirichletPolynomial P (onePlusIT t)) := by
  unfold primeDirichletPolynomial
  exact Sparse.continuous_dirichletPolynomial_onePlusIT_sparse _ _

theorem measurableSet_largePrimeValueSet (X P ε : ℝ) :
    MeasurableSet (largePrimeValueSet X P ε) := by
  unfold largePrimeValueSet
  exact measurableSet_Icc.inter
    (measurableSet_le measurable_const
      (continuous_primeDirichletPolynomial_onePlusIT P).norm.measurable)

theorem largePrimeValueSet_subset_Icc (X P ε : ℝ) :
    largePrimeValueSet X P ε ⊆ Set.Icc (X ^ (1 / 1000 : ℝ)) X :=
  Set.inter_subset_left

/-- The large-prime sets are nested in the threshold parameter. -/
theorem largePrimeValueSet_mono {X P ε ε' : ℝ} (hP : 1 ≤ P)
    (hεε' : ε ≤ ε') :
    largePrimeValueSet X P ε ⊆ largePrimeValueSet X P ε' := by
  intro t ht
  refine ⟨ht.1, ?_⟩
  have hle : P ^ (-ε' / 10) ≤ P ^ (-ε / 10) :=
    Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  exact hle.trans ht.2

/-- Removing the factor `|P₁|² ≤ 4` from a `𝒰`-integral. -/
theorem integral_primeFactor_mul_le_four_mul
    {P : ℝ} (hP : 1 ≤ P) {E : Set ℝ} {F : ℝ → ℂ}
    (hE : MeasurableSet E) {a b : ℝ} (hEsub : E ⊆ Set.Icc a b)
    (hF : Continuous F) :
    (∫ t in E, ‖primeDirichletPolynomial P (onePlusIT t)‖ ^ (2 : ℕ) *
        ‖F t‖ ^ (2 : ℕ)) ≤ 4 * ∫ t in E, ‖F t‖ ^ (2 : ℕ) := by
  have hcont1 : Continuous (fun t ↦
      ‖primeDirichletPolynomial P (onePlusIT t)‖ ^ (2 : ℕ) *
        ‖F t‖ ^ (2 : ℕ)) :=
    ((continuous_primeDirichletPolynomial_onePlusIT P).norm.pow 2).mul
      (hF.norm.pow 2)
  have hcont2 : Continuous (fun t ↦ 4 * ‖F t‖ ^ (2 : ℕ)) :=
    continuous_const.mul (hF.norm.pow 2)
  rw [← integral_const_mul]
  apply setIntegral_mono_on (hcont1.integrableOn_Icc.mono_set hEsub)
    (hcont2.integrableOn_Icc.mono_set hEsub) hE
  intro t _
  have h2 := norm_primeDirichletPolynomial_onePlusIT_le_two hP t
  have hsq : ‖primeDirichletPolynomial P (onePlusIT t)‖ ^ (2 : ℕ) ≤ 4 := by
    have := pow_le_pow_left₀ (norm_nonneg _) h2 2
    norm_num at this ⊢; linarith
  exact mul_le_mul_of_nonneg_right hsq (by positivity)

/-! ## The outer-large piece: Proposition 5.1, uniformly in `P` -/

/-- Uniform version of `outerR1NaturalizedTypeIIEstimate_of_source`: the
product window is `X/(2P) < M₁M₂ ≤ 4X/P` with `P` anywhere in
`[1, (log X)^(11/10)]`; the constants do not depend on `P`. -/
theorem typeII_R1_uniform (inputs : ExternalInputs) :
    ∃ C₁ ε₅ : ℝ, 0 < C₁ ∧ 0 < ε₅ ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₅ → ∀ B : ℝ, 0 ≤ B →
        ∃ κ₁ : ℝ, 0 < κ₁ ∧ ∀ A₀ : ℝ, 1 ≤ A₀ →
          ∃ C₂ C : ℝ, 0 < C₂ ∧ 0 < C ∧ ∀ᶠ X : ℝ in atTop,
            ∀ (P M₁ M₂ δ : ℝ) (R N₂ : ℕ) (α γ : ℕ → ℂ) (E : Set ℝ) (S : ℝ),
              1 ≤ P → P ≤ (Real.log X) ^ (11 / 10 : ℝ) →
              X ^ (ε / 2) ≤ M₁ → M₁ ≤ X ^ (2 / 11 : ℝ) →
              X / (2 * P) < M₁ * M₂ → M₁ * M₂ ≤ 4 * X / P →
              (N₂ = TypeII.naturalDyadicCoreScale M₂ ∨
                N₂ = TypeII.naturalDyadicBoundaryScale M₂) →
              IsDivisorBoundedByConstant B A₀ α →
              IsDivisorBoundedByConstant B A₀ γ →
              MeasurableSet E → E ⊆ Set.Icc (0 : ℝ) X → 0 ≤ S →
              (∀ t ∈ E,
                ‖dyadicDirichletPolynomial
                  (Completion.supportedTypeIIFirstCoefficient δ M₁ R α)
                  (TypeII.naturalDyadicCoreScale M₁ : ℝ)
                  (onePlusIT t)‖ ^ (2 : ℕ) ≤ S) →
              (∫ t in TypeII.largeValueR1 E
                  (dyadicDirichletPolynomial
                    (Completion.supportedTypeIIFirstCoefficient δ M₁ R α)
                    (TypeII.naturalDyadicCoreScale M₁ : ℝ))
                  (dyadicDirichletPolynomial γ (N₂ : ℝ))
                  (TypeII.naturalDyadicCoreScale M₁ : ℝ) (N₂ : ℝ)
                  (Completion.outerPartitionEpsilon (17 / 70 - C₁ * ε)),
                TypeII.typeIIMagnitude
                    (dyadicDirichletPolynomial
                      (Completion.supportedTypeIIFirstCoefficient δ M₁ R α)
                      (TypeII.naturalDyadicCoreScale M₁ : ℝ)) t ^ (2 : ℕ) *
                  TypeII.typeIIMagnitude
                    (dyadicDirichletPolynomial γ (N₂ : ℝ)) t ^ (2 : ℕ)) ≤
                C * (X ^ (-κ₁) + (Real.log X) ^ C₂ * S) := by
  obtain ⟨C₁, ε₀, hC₁, hε₀, htypeII⟩ :=
    TypeII.typeIIEstimateStatement_of_externalInputs inputs
  refine ⟨C₁, ε₀, hC₁, hε₀, ?_⟩
  intro ε hε hεle B hB
  obtain ⟨κ₁, hκ₁, htypeII⟩ := htypeII ε hε hεle B hB
  refine ⟨κ₁, hκ₁, ?_⟩
  intro A₀ hA₀
  obtain ⟨C₂, C, T₀, hC₂, hC, hT₀, hbound⟩ := htypeII A₀ 4 hA₀ (by norm_num)
  refine ⟨C₂, C, hC₂, hC, ?_⟩
  filter_upwards [eventually_ge_atTop T₀,
    Completion.eventually_sourceTypeII_naturalization_reserves (11 / 10) hε,
    eventually_gt_atTop (Real.exp 1)] with X hXT₀ hres hXe
  intro P M₁ M₂ δ R N₂ α γ E S hP1 hPhi hM₁lo hM₁hi hprodLo hprodHi hN₂
    hα hγ hE hEsub hS hSbound
  obtain ⟨hfour, hfloorReserve, hcomplement, hlog4⟩ := hres
  have hX1 : 1 < X := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlogX : 1 < Real.log X := by
    rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) hXe
  have hPpos : 0 < P := by linarith
  set a := scaleExponent X P with ha
  have hPa : P = (Real.log X) ^ a := (rpow_scaleExponent hXe hPpos).symm
  have ha0 : 0 ≤ a := by
    have := le_scaleExponent_of_rpow_le (b := 0) hXe hPpos
      (by rw [Real.rpow_zero]; exact hP1)
    linarith
  have ha2 : a ≤ 2 := by
    have := scaleExponent_le_of_le_rpow hXe hPpos hPhi
    linarith
  have hM₁four : 4 ≤ M₁ := hfour.trans hM₁lo
  have hreserve : 4 * P * M₁ ≤ X := by
    have h1 : 4 * P * M₁ ≤ 4 * (Real.log X) ^ (11 / 10 : ℝ) * X ^ (2 / 11 : ℝ) := by
      have : 0 ≤ M₁ := by linarith
      calc 4 * P * M₁ ≤ 4 * (Real.log X) ^ (11 / 10 : ℝ) * M₁ := by gcongr
        _ ≤ 4 * (Real.log X) ^ (11 / 10 : ℝ) * X ^ (2 / 11 : ℝ) := by
          gcongr
    exact h1.trans hcomplement
  have hM₂two : 2 ≤ M₂ :=
    (Completion.representedTypeII_secondScale_ge_two_of_reserve hPpos
      (by linarith) hprodLo hreserve).le
  have hgeo := Completion.representedTypeII_fullEstimate_lengthGeometry
    hX1 hlog4 ha0 hPa (by linarith : 2 ≤ M₁) hM₂two hM₁lo hM₁hi hε.le
    hfloorReserve hprodLo hprodHi hN₂
  obtain ⟨hN₁one, hN₂one, hratioLo, hratioHi, hN₁lo, hN₁hi⟩ := hgeo
  have hlogX1 : 1 ≤ Real.log X := hlogX.le
  have hL1 : (Real.log X) ^ (-(4 : ℝ)) ≤ (Real.log X) ^ (-(a + 2)) :=
    Real.rpow_le_rpow_of_exponent_le hlogX1 (by linarith)
  have hL2 : (Real.log X) ^ (a + 2) ≤ (Real.log X) ^ (4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlogX1 (by linarith)
  let F₁ : ℂ → ℂ := dyadicDirichletPolynomial
    (Completion.supportedTypeIIFirstCoefficient δ M₁ R α)
    (TypeII.naturalDyadicCoreScale M₁ : ℝ)
  let F₂ : ℂ → ℂ := dyadicDirichletPolynomial γ (N₂ : ℝ)
  have hF₁cont : Continuous (fun t : ℝ ↦ F₁ (onePlusIT t)) :=
    Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse _ _
  have hF₂cont : Continuous (fun t : ℝ ↦ F₂ (onePlusIT t)) :=
    Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse _ _
  let U := TypeII.largeValueR1 E F₁ F₂
    (TypeII.naturalDyadicCoreScale M₁ : ℝ) (N₂ : ℝ)
    (Completion.outerPartitionEpsilon (17 / 70 - C₁ * ε))
  have hUmeas : MeasurableSet U :=
    TypeII.measurableSet_largeValueR1 hE hF₁cont.norm.measurable
      hF₂cont.norm.measurable
  have hUsub : U ⊆ Set.Icc (0 : ℝ) X := fun t ht ↦ hEsub ht.1
  have hlarge : ∀ t ∈ U,
      (TypeII.naturalDyadicCoreScale M₁ : ℝ) ^
          (-(17 / 70 - C₁ * ε)) ≤ ‖F₁ (onePlusIT t)‖ ∨
        (N₂ : ℝ) ^ (-(17 / 70 - C₁ * ε)) ≤ ‖F₂ (onePlusIT t)‖ := by
    intro t ht
    have ht' := (TypeII.mem_largeValueR1_iff.mp ht).2
    simpa only [Completion.outerPartition_threshold,
      TypeII.typeIIMagnitude] using ht'
  have hSU : ∀ t ∈ U, ‖F₁ (onePlusIT t)‖ ^ 2 ≤ S := fun t ht ↦ hSbound t ht.1
  have hdiv : IsDivisorBoundedByConstant B A₀
      (Completion.supportedTypeIIFirstCoefficient δ M₁ R α) :=
    Completion.supportedTypeIIFirstCoefficient_isDivisorBoundedByConstant hα
  have hmain := hbound X (TypeII.naturalDyadicCoreScale M₁) N₂
    (Completion.supportedTypeIIFirstCoefficient δ M₁ R α) γ U S hXT₀
    hN₁one hN₂one (hL1.trans hratioLo) (hratioHi.trans hL2) hN₁lo hN₁hi
    hdiv hγ hUmeas hUsub hlarge hS hSU
  simpa [TypeII.typeIIMagnitude, F₁, F₂, U, norm_mul, mul_pow] using hmain

/-! ## Occupied medium bins -/

theorem rpow_logRatio {X N : ℝ} (hX : 1 < X) (hN : 0 < N) :
    N = X ^ (Real.log N / Real.log X) := by
  have hlog : 0 < Real.log X := Real.log_pos hX
  rw [Real.rpow_def_of_pos (by linarith),
    show Real.log X * (Real.log N / Real.log X) = Real.log N by field_simp,
    Real.exp_log hN]

/-- Exponent information carried by any point of an `R₂` logarithmic bin. -/
theorem binExponent_facts {E : Set ℝ} {F₁ F₂ : ℂ → ℂ}
    {N₁ N₂ X eps : ℝ} {k : ℤ × ℤ} {t : ℝ}
    (hN₁ : 1 < N₁) (hN₂ : 1 < N₂) (hX : 1 < X)
    (ht : t ∈ TypeII.mediumLogMagnitudeBinSet E F₁ F₂ N₁ N₂ X eps k) :
    10 * eps < TypeII.upperBinExponent N₁ k.1 ∧
      10 * eps < TypeII.upperBinExponent N₂ k.2 ∧
      TypeII.upperBinExponent N₂ k.2 ≤
        (Real.log X + 1) / Real.log N₂ := by
  have hR2 := TypeII.mem_largeValueR2_iff.mp ht.1
  have hpos := TypeII.typeIIMagnitudes_pos_of_mem_largeValueR2
    (by linarith : (0 : ℝ) < X) ht.1
  refine ⟨?_, ?_, ?_⟩
  · exact TypeII.lt_upperBinExponent_of_magnitude_lt_rpow hN₁ ht.2.1 hpos.1
      (by simpa only [neg_mul] using hR2.2.1)
  · exact TypeII.lt_upperBinExponent_of_magnitude_lt_rpow hN₂ ht.2.2 hpos.2
      (by simpa only [neg_mul] using hR2.2.2.1)
  · have hbin := ht.2.2
    rw [TypeII.mem_logMagnitudeBin_iff] at hbin
    have hlogN₂ : 0 < Real.log N₂ := Real.log_pos hN₂
    have hk : (k.2 : ℝ) ≤ Real.log X := by
      have h1 : (k.2 : ℝ) ≤ -Real.log (TypeII.typeIIMagnitude F₂ t) := hbin.1
      have h2 : Real.log X⁻¹ ≤ Real.log (TypeII.typeIIMagnitude F₂ t) :=
        Real.log_le_log (by positivity) hR2.2.2.2.2
      rw [Real.log_inv] at h2
      linarith
    unfold TypeII.upperBinExponent
    exact div_le_div_of_nonneg_right (by linarith) hlogN₂.le

/-- `K (log X)^b ≤ X^c` eventually along the naturals. -/
theorem eventually_const_mul_log_rpow_le_rpow (K b : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, K * (Real.log (X : ℝ)) ^ b ≤ (X : ℝ) ^ c := by
  have hc2 : 0 < c / 2 := by positivity
  have h1 := tendsto_natCast_atTop_atTop.eventually
    (TypeII.eventually_log_rpow_le_rpow b hc2)
  have h2 := tendsto_natCast_atTop_atTop.eventually
    ((tendsto_rpow_atTop hc2).eventually_ge_atTop (max K 0))
  filter_upwards [h1, h2, eventually_ge_atTop 1] with X h1 h2 hX
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hlog0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hX1
  have hpos : 0 ≤ (Real.log (X : ℝ)) ^ b := Real.rpow_nonneg hlog0 _
  calc K * (Real.log (X : ℝ)) ^ b ≤ max K 0 * (Real.log (X : ℝ)) ^ b :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
    _ ≤ (X : ℝ) ^ (c / 2) * (X : ℝ) ^ (c / 2) :=
        mul_le_mul h2 h1 hpos (Real.rpow_nonneg (by linarith) _)
    _ = (X : ℝ) ^ c := by
        rw [← Real.rpow_add (by linarith)]; ring_nf

/-- `X^(e/2) + 1 ≤ X^e` eventually. -/
theorem eventually_rpow_half_add_one_le {e : ℝ} (he : 0 < e) :
    ∀ᶠ X : ℕ in atTop, (X : ℝ) ^ (e / 2) + 1 ≤ (X : ℝ) ^ e := by
  have he2 : 0 < e / 2 := by positivity
  have h := tendsto_natCast_atTop_atTop.eventually
    ((tendsto_rpow_atTop he2).eventually_ge_atTop 2)
  filter_upwards [h, eventually_ge_atTop 1] with X hX hX1
  have hX1' : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hsq : (X : ℝ) ^ e = (X : ℝ) ^ (e / 2) * (X : ℝ) ^ (e / 2) := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  rw [hsq]
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **Occupied medium bins (paper Section 6, refined).**  Uniformly over the
block window `[(log X)^(1925/1763+η), (log X)^(11/10)]` and over every Type II
component, each `R₂` logarithmic bin of the naturalized product has measure
at most a constant times its sparse target times `X^(-(ε/2)²)`.

Each bin is handled by one of three arguments (see
`Final/TypeIIDensityBins.lean`): the refined density bound for the powered
first factor, the refined density bound for the second factor, or
Heath-Brown's sparse mean value theorem through the two sparse branches. -/
theorem typeII_bins_uniform (inputs : ExternalInputs)
    {η ε C₁ A Bcoeff Acoeff : ℝ} (hη : 0 < η) (hη' : η ≤ 1 / 250)
    (hε : 0 < ε) (hε0 : ε ≤ 1 / 20000) (hεη : 20 * ε ≤ η) (hA : 0 < A)
    (hB : 0 ≤ Bcoeff) (hAc : 1 ≤ Acoeff)
    (hC₁ε : C₁ * ε ≤ 1 / 1000) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (P M₁ M₂ : ℝ) (R : ℕ) (Q : Fin R → ℝ) (α γ : ℕ → ℂ) (N₂ : ℕ),
        (Real.log (X : ℝ)) ^ (1925 / 1763 + η) ≤ P →
        P ≤ (Real.log (X : ℝ)) ^ (11 / 10 : ℝ) →
        R ≤ ⌊Real.log ((X : ℝ) ^ (2 / 11 : ℝ)) /
            Real.log (Real.exp (Real.log (X : ℝ) /
              (Real.log (Real.log (X : ℝ))) ^ (3 : ℕ)))⌋₊ →
        (∀ m, α m = matomakiTeravainenStructuredTypeIICoefficient
          ((Real.log (X : ℝ)) ^ (-10 * A)) R Q m) →
        IsDivisorBoundedByConstant Bcoeff Acoeff α →
        (X : ℝ) ^ (ε / 2) ≤ M₁ → M₁ ≤ (X : ℝ) ^ (2 / 11 : ℝ) →
        (X : ℝ) / (2 * P) < M₁ * M₂ → M₁ * M₂ ≤ 4 * (X : ℝ) / P →
        (N₂ = TypeII.naturalDyadicCoreScale M₂ ∨
          N₂ = TypeII.naturalDyadicBoundaryScale M₂) →
        IsDivisorBoundedByConstant Bcoeff Acoeff γ →
        ∀ bin ∈ TypeII.logMagnitudePairIndexRange (X : ℝ),
          volume.real (TypeII.mediumLogMagnitudeBinSet
            (largePrimeValueSet (X : ℝ) P (ε / 2))
            (dyadicDirichletPolynomial
              (Completion.supportedTypeIIFirstCoefficient
                ((Real.log (X : ℝ)) ^ (-10 * A)) M₁ R α)
              (TypeII.naturalDyadicCoreScale M₁ : ℝ))
            (dyadicDirichletPolynomial γ (N₂ : ℝ))
            (TypeII.naturalDyadicCoreScale M₁ : ℝ) (N₂ : ℝ) (X : ℝ)
            (Completion.outerPartitionEpsilon (17 / 70 - C₁ * ε)) bin) ≤
          K * Sparse.sparsePropagationScaleTarget
              (TypeII.naturalDyadicCoreScale M₁ : ℝ) (N₂ : ℝ)
              (TypeII.upperBinExponent
                (TypeII.naturalDyadicCoreScale M₁ : ℝ) bin.1)
              (TypeII.upperBinExponent (N₂ : ℝ) bin.2) *
            (X : ℝ) ^ (-((ε / 2) ^ 2)) := by
  set e := ε / 2 with he
  have he0 : 0 < e := by positivity
  have he10 : e ≤ 1 / 10 := by linarith
  have he1 : e ≤ 1 := by linarith
  have hesmall : e ≤ 1 / 40000 := by linarith
  have heη : 40 * e ≤ η := by linarith
  obtain ⟨CRe, CIm, Cp, Dp, hCRe, hCIm, hCp, hDp, hloss, hpackage⟩ :=
    Sparse.sparsePropagation_uniformConstants_powerSaving_package inputs he0
      he10 hB (by linarith : (0 : ℝ) < Acoeff)
  have hdens := Hybrid.refinedHybridMeasureDensity_of_inputs inputs
  obtain ⟨Ca, hCa, hDa⟩ := poweredFirstFactor_density hdens hB hAc
    (εh := 3 * e) (by positivity) (by linarith)
  obtain ⟨Cb, hCb, hDb⟩ := directFactor_density hdens hB hAc
    (εh := 3 * e) (by positivity) (by linarith)
  set K := max (max 2 (Sparse.secondBranchPowerConstant Cp Dp Acoeff e))
    (max Ca Cb) with hK
  have h2K : (2 : ℝ) ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hCK : Sparse.secondBranchPowerConstant Cp Dp Acoeff e ≤ K :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hCaK : Ca ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hCbK : Cb ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, lt_of_lt_of_le two_pos h2K, ?_⟩
  have halo : 1 < 1925 / 1763 + η := by linarith
  have hlohi : 1925 / 1763 + η < 11 / 10 := by linarith
  have hlog8 : ∀ᶠ X : ℕ in atTop, 8 ≤ Real.log (X : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 8
  have hgeo := eventually_uniform_sparseGeometry (alo := 1925 / 1763 + η)
    (ahi := 11 / 10) (s := e ^ 2 / 1000) halo (by positivity)
  have hcardE := eventually_uniform_card_sparseSupport
    inputs.hildebrandTenenbaumCorollaryOneThree halo hlohi
    (ω := e ^ 2 / 200) (by positivity)
  have hlossN := tendsto_natCast_atTop_atTop.eventually hloss
  have hres := tendsto_natCast_atTop_atTop.eventually
    (Completion.eventually_sourceTypeII_naturalization_reserves (11 / 10) hε)
  have hwidth := tendsto_natCast_atTop_atTop.eventually
    (Completion.eventually_source_width_three_halves hA)
  have hE4 := eventually_rpow_half_add_one_le he0
  have hE7 := eventually_const_mul_log_rpow_le_rpow 8 (11 / 10)
    (c := e ^ 2 / 100) (by positivity)
  have hE8 := eventually_const_mul_log_rpow_le_rpow 4 (11 / 10)
    (c := 5 / 33) (by norm_num)
  filter_upwards [hgeo, hcardE, hlossN, hres, hwidth, hE4, hE7, hE8,
    eventually_ge_atTop 2, hDa, hDb, hlog8] with X hgeoX hcardX hlossX hresX
      hwidthX hE4X hE7X hE8X hX2 hDaX hDbX hlog8X
  intro P M₁ M₂ R Q α γ N₂ hPlo hPhi hR hαdef hα hM₁lo hM₁hi hprodLo
    hprodHi hN₂ hγ bin hbin
  set δ := (Real.log (X : ℝ)) ^ (-10 * A) with hδ
  set n₁ : ℕ := TypeII.naturalDyadicCoreScale M₁ with hn₁
  set F₁ : ℂ → ℂ := dyadicDirichletPolynomial
    (Completion.supportedTypeIIFirstCoefficient δ M₁ R α) (n₁ : ℝ) with hF₁
  set F₂ : ℂ → ℂ := dyadicDirichletPolynomial γ (N₂ : ℝ) with hF₂
  set σs := 17 / 70 - C₁ * ε with hσs
  set U := largePrimeValueSet (X : ℝ) P e with hU
  set V := TypeII.mediumLogMagnitudeBinSet U F₁ F₂ (n₁ : ℝ) (N₂ : ℝ) (X : ℝ)
    (Completion.outerPartitionEpsilon σs) bin with hV
  have htarget0 : 0 ≤ Sparse.sparsePropagationScaleTarget (n₁ : ℝ) (N₂ : ℝ)
      (TypeII.upperBinExponent (n₁ : ℝ) bin.1)
      (TypeII.upperBinExponent (N₂ : ℝ) bin.2) := by
    unfold Sparse.sparsePropagationScaleTarget; positivity
  have hK0 : 0 ≤ K := le_trans zero_le_two h2K
  by_cases hVne : V.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hVne]
    simp only [measureReal_empty]
    positivity
  obtain ⟨t₀, ht₀⟩ := hVne
  -- geometry of the sparse polynomial
  obtain ⟨hX1, hPpos, hden, hfloor1, hpower, hMone, hMX, hmu⟩ :=
    hgeoX P hPlo hPhi
  obtain ⟨hfour, _hfloorRes, hcompl, hlog4⟩ := hresX
  have hXpos : (0 : ℝ) < X := by linarith
  have hlogpos : 0 < Real.log (X : ℝ) := Real.log_pos hX1
  have hXe : Real.exp 1 < (X : ℝ) := by
    have : Real.exp 1 < Real.exp 4 := Real.exp_lt_exp.mpr (by norm_num)
    have h2 : Real.exp 4 ≤ (X : ℝ) := by
      rw [← Real.exp_log hXpos]; exact Real.exp_le_exp.mpr hlog4
    linarith
  set a := scaleExponent (X : ℝ) P with ha
  have hPa : P = (Real.log (X : ℝ)) ^ a := (rpow_scaleExponent hXe hPpos).symm
  have halo' : 1925 / 1763 + η ≤ a := le_scaleExponent_of_rpow_le hXe hPpos hPlo
  have hahi' : a ≤ 11 / 10 := scaleExponent_le_of_le_rpow hXe hPpos hPhi
  have ha1 : 1 < a := by linarith
  set k := ⌊Real.log (X : ℝ) / Real.log (2 * P)⌋₊ with hk
  set M := P ^ k with hM
  -- scales of the two factors
  have hM₁four : 4 ≤ M₁ := hfour.trans hM₁lo
  have hM₁pos : 0 < M₁ := by linarith
  have hlogX1 : 1 ≤ Real.log (X : ℝ) := by linarith
  have hP8 : 8 ≤ P := by
    have h1 : Real.log (X : ℝ) ≤ (Real.log (X : ℝ)) ^ (1925 / 1763 + η) := by
      calc Real.log (X : ℝ) = (Real.log (X : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hlogX1 (by linarith)
    linarith
  have hP4 : 4 ≤ P := by linarith
  have hreserve : 4 * P * M₁ ≤ (X : ℝ) := by
    calc 4 * P * M₁ ≤ 4 * (Real.log (X : ℝ)) ^ (11 / 10 : ℝ) * M₁ := by gcongr
      _ ≤ 4 * (Real.log (X : ℝ)) ^ (11 / 10 : ℝ) * (X : ℝ) ^ (2 / 11 : ℝ) := by
        gcongr
      _ ≤ (X : ℝ) := hcompl
  have hM₂two : 2 ≤ M₂ :=
    (Completion.representedTypeII_secondScale_ge_two_of_reserve hPpos
      hM₁pos hprodLo hreserve).le
  have hn₁le : (n₁ : ℝ) ≤ M₁ := Nat.floor_le hM₁pos.le
  have hn₁gt : M₁ - 1 < (n₁ : ℝ) := Nat.sub_one_lt_floor M₁
  have hn₁half : M₁ / 2 ≤ (n₁ : ℝ) := TypeII.half_le_naturalDyadicCoreScale (by linarith)
  have hn₁lo : (X : ℝ) ^ (e / 2) ≤ (n₁ : ℝ) := by
    have : (X : ℝ) ^ e ≤ M₁ := by rw [he]; exact hM₁lo
    linarith
  have hn₁one : (1 : ℝ) < n₁ := by
    have : (1 : ℝ) < (X : ℝ) ^ (e / 2) := Real.one_lt_rpow hX1 (by positivity)
    linarith
  -- second factor
  have hcoreM₂le : (TypeII.naturalDyadicCoreScale M₂ : ℝ) ≤ M₂ :=
    Nat.floor_le (by linarith)
  have hcoreM₂half : M₂ / 2 ≤ (TypeII.naturalDyadicCoreScale M₂ : ℝ) :=
    TypeII.half_le_naturalDyadicCoreScale hM₂two
  have hN₂lo : M₂ / 2 ≤ (N₂ : ℝ) := by
    rcases hN₂ with h | h
    · rw [h]; exact hcoreM₂half
    · rw [h, TypeII.naturalDyadicBoundaryScale]; push_cast; linarith
  have hN₂hi : (N₂ : ℝ) ≤ 2 * M₂ := by
    rcases hN₂ with h | h
    · rw [h]; linarith
    · rw [h, TypeII.naturalDyadicBoundaryScale]; push_cast; linarith
  have hM₂lo : (X : ℝ) / (2 * P * M₁) < M₂ := by
    rw [div_lt_iff₀ (by positivity)]
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * P)).1 hprodLo
    linarith [show M₁ * M₂ * (2 * P) = M₂ * (2 * P * M₁) by ring]
  have hN₂big : (X : ℝ) ^ (2 / 3 : ℝ) ≤ (N₂ : ℝ) := by
    have hden0 : 0 < 4 * (Real.log (X : ℝ)) ^ (11 / 10 : ℝ) *
        (X : ℝ) ^ (2 / 11 : ℝ) := by positivity
    have h1 : (X : ℝ) / (4 * (Real.log (X : ℝ)) ^ (11 / 10 : ℝ) *
        (X : ℝ) ^ (2 / 11 : ℝ)) ≤ (X : ℝ) / (4 * P * M₁) := by
      apply div_le_div_of_nonneg_left hXpos.le (by positivity)
      gcongr
    have h2 : (X : ℝ) / (4 * P * M₁) ≤ M₂ / 2 := by
      have : (X : ℝ) / (4 * P * M₁) = (X : ℝ) / (2 * P * M₁) / 2 := by
        field_simp; ring
      rw [this]; linarith
    have h3 : (X : ℝ) ^ (2 / 3 : ℝ) ≤ (X : ℝ) / (4 * (Real.log (X : ℝ)) ^
        (11 / 10 : ℝ) * (X : ℝ) ^ (2 / 11 : ℝ)) := by
      rw [le_div_iff₀ hden0]
      have hsplit : (X : ℝ) = (X : ℝ) ^ (2 / 3 : ℝ) * (X : ℝ) ^ (5 / 33 : ℝ) *
          (X : ℝ) ^ (2 / 11 : ℝ) := by
        rw [← Real.rpow_add hXpos, ← Real.rpow_add hXpos]; norm_num
      calc (X : ℝ) ^ (2 / 3 : ℝ) * (4 * (Real.log (X : ℝ)) ^ (11 / 10 : ℝ) *
            (X : ℝ) ^ (2 / 11 : ℝ)) ≤ (X : ℝ) ^ (2 / 3 : ℝ) *
            ((X : ℝ) ^ (5 / 33 : ℝ) * (X : ℝ) ^ (2 / 11 : ℝ)) := by
            gcongr
        _ = (X : ℝ) ^ (2 / 3 : ℝ) * (X : ℝ) ^ (5 / 33 : ℝ) *
            (X : ℝ) ^ (2 / 11 : ℝ) := by ring
        _ = (X : ℝ) := hsplit.symm
    linarith
  have hN₂one : (1 : ℝ) < N₂ := by
    have : (1 : ℝ) < (X : ℝ) ^ (2 / 3 : ℝ) := Real.one_lt_rpow hX1 (by norm_num)
    linarith
  have hN₂two : (2 : ℝ) ≤ N₂ := by
    have h4 : (4 : ℝ) ≤ (X : ℝ) ^ (2 / 3 : ℝ) := by
      have hX8 : (8 : ℝ) ≤ (X : ℝ) := by
        have : Real.exp 4 ≤ (X : ℝ) := by
          rw [← Real.exp_log hXpos]; exact Real.exp_le_exp.mpr hlog4
        have : (8 : ℝ) ≤ Real.exp 4 := by
          have := Real.add_one_le_exp (4 : ℝ)
          nlinarith [Real.add_one_le_exp (2 : ℝ), Real.exp_pos 2,
            show Real.exp 4 = Real.exp 2 * Real.exp 2 by
              rw [← Real.exp_add]; norm_num]
        linarith
      calc (4 : ℝ) = (8 : ℝ) ^ (2 / 3 : ℝ) := by
            rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
            norm_num
        _ ≤ (X : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) hX8 (by norm_num)
    linarith
  have hN₂X : (N₂ : ℝ) ≤ (X : ℝ) := by
    have hM₂hi : M₂ ≤ 4 * (X : ℝ) / P / M₁ := by
      rw [le_div_iff₀ hM₁pos]; linarith
    have : 4 * (X : ℝ) / P / M₁ ≤ (X : ℝ) / 2 := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      have h16 : 8 ≤ P * M₁ := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h16 hXpos.le]
    linarith
  have hprodN : (X : ℝ) ^ (1 - e ^ 2 / 100) ≤ (n₁ : ℝ) * (N₂ : ℝ) := by
    have h1 : (X : ℝ) / (8 * P) ≤ (n₁ : ℝ) * (N₂ : ℝ) := by
      have : M₁ * M₂ / 4 ≤ (n₁ : ℝ) * (N₂ : ℝ) := by
        have h := mul_le_mul hn₁half hN₂lo (by positivity) (by positivity)
        nlinarith
      have h2 : (X : ℝ) / (8 * P) = (X : ℝ) / (2 * P) / 4 := by field_simp; ring
      rw [h2]; linarith
    have h3 : (X : ℝ) ^ (1 - e ^ 2 / 100) ≤ (X : ℝ) / (8 * P) := by
      rw [le_div_iff₀ (by positivity)]
      have hsplit : (X : ℝ) = (X : ℝ) ^ (1 - e ^ 2 / 100) * (X : ℝ) ^ (e ^ 2 / 100) := by
        rw [← Real.rpow_add hXpos]; norm_num
      calc (X : ℝ) ^ (1 - e ^ 2 / 100) * (8 * P) ≤
            (X : ℝ) ^ (1 - e ^ 2 / 100) * (8 * (Real.log (X : ℝ)) ^ (11 / 10 : ℝ)) := by
            gcongr
        _ ≤ (X : ℝ) ^ (1 - e ^ 2 / 100) * (X : ℝ) ^ (e ^ 2 / 100) := by gcongr
        _ = (X : ℝ) := hsplit.symm
    linarith
  -- exponents of the occupied bin
  obtain ⟨hup1, hup2, hup2le⟩ := binExponent_facts hn₁one hN₂one hX1 ht₀
  have hσthr : 10 * Completion.outerPartitionEpsilon σs = σs := by
    simp [Completion.outerPartitionEpsilon]; ring
  rw [hσthr] at hup1 hup2
  have hσsLo : 17 / 70 - 1 / 1000 ≤ σs := by rw [hσs]; linarith
  have hσstrong : 1 / 5 + 2 * e ≤ σs := by linarith
  have hup2two : TypeII.upperBinExponent (N₂ : ℝ) bin.2 ≤ 2 := by
    refine hup2le.trans ?_
    have hlogN₂ : (2 / 3) * Real.log (X : ℝ) ≤ Real.log (N₂ : ℝ) := by
      have := Real.log_le_log (Real.rpow_pos_of_pos hXpos _) hN₂big
      rwa [Real.log_rpow hXpos] at this
    rw [div_le_iff₀ (by linarith)]
    linarith
  -- the real structured coefficient
  set b : ℕ → ℝ := Sparse.structuredTypeIIRealCoefficient δ M₁ R Q with hbdef
  have hδ0 : 0 ≤ δ := Real.rpow_nonneg hlogpos.le _
  have hαeq : α = matomakiTeravainenStructuredTypeIICoefficient δ R Q :=
    funext hαdef
  have hbfun : (fun n ↦ (b n : ℂ)) =
      Completion.supportedTypeIIFirstCoefficient δ M₁ R α := by
    funext n
    rw [hαeq, Completion.supportedStructuredFirstCoefficient_eq_realCast hδ0 hM₁pos]
  have hbdiv : IsDivisorBoundedByConstant Bcoeff Acoeff (fun n ↦ (b n : ℂ)) := by
    rw [hbfun]
    exact Completion.supportedTypeIIFirstCoefficient_isDivisorBoundedByConstant hα
  -- coordinates
  have hn₁pos : (0 : ℝ) < n₁ := by linarith
  have hN₂pos : (0 : ℝ) < N₂ := by linarith
  have hMpos : 0 < M := by linarith
  set θ := Real.log (n₁ : ℝ) / Real.log (X : ℝ) with hθ
  set φ := Real.log (N₂ : ℝ) / Real.log (X : ℝ) with hφ
  set μ := Real.log M / Real.log (X : ℝ) with hμ
  have hn₁coord : (n₁ : ℝ) = (X : ℝ) ^ θ := rpow_logRatio hX1 hn₁pos
  have hN₂coord : (N₂ : ℝ) = (X : ℝ) ^ φ := rpow_logRatio hX1 hN₂pos
  have hMcoord : M = (X : ℝ) ^ μ := rpow_logRatio hX1 hMpos
  have hθlo : e / 2 ≤ θ := by
    rw [hθ, le_div_iff₀ hlogpos]
    have := Real.log_le_log (Real.rpow_pos_of_pos hXpos _) hn₁lo
    rwa [Real.log_rpow hXpos] at this
  have hθhi : θ ≤ 2 / 11 := by
    rw [hθ, div_le_iff₀ hlogpos]
    have := Real.log_le_log hn₁pos (hn₁le.trans hM₁hi)
    rwa [Real.log_rpow hXpos] at this
  have hφhi : φ ≤ 1 := by
    rw [hφ, div_le_iff₀ hlogpos, one_mul]
    exact Real.log_le_log hN₂pos hN₂X
  have hμhi : μ ≤ 1 := by
    rw [hμ, div_le_iff₀ hlogpos, one_mul]
    exact Real.log_le_log hMpos hMX
  have hproductLoss : 1 - θ - φ ≤ e ^ 2 / 100 := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hXpos _) hprodN
    rw [Real.log_rpow hXpos, Real.log_mul hn₁pos.ne' hN₂pos.ne'] at h
    have : θ + φ = (Real.log (n₁ : ℝ) + Real.log (N₂ : ℝ)) / Real.log (X : ℝ) := by
      rw [hθ, hφ, add_div]
    have h2 : 1 - e ^ 2 / 100 ≤ θ + φ := by
      rw [this, le_div_iff₀ hlogpos]; linarith
    linarith
  -- support bounds
  have hcardBound := hcardX P k hPlo hPhi hfloor1 hpower
  set β := 1 - 1 / a with hβ
  have hβ0 : 0 ≤ β := by
    rw [hβ, sub_nonneg, div_le_one (by linarith)]; linarith
  have hβ1 : β ≤ 1 / 11 := by
    rw [hβ]
    have : (10 : ℝ) / 11 ≤ 1 / a := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    linarith
  have hRfirst : ((Sparse.primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
      M ^ (1 - 1 / a + e ^ 2 / 100) := by
    refine hcardBound.trans ?_
    rw [hMcoord, ← Real.rpow_mul hXpos.le]
    apply Real.rpow_le_rpow_of_exponent_le hX1.le
    have hmu' : 1 - e ^ 2 / 1000 ≤ μ := hmu
    have he2 : e ^ 2 ≤ 1 := pow_le_one₀ he0.le he1
    have hpos' : 0 ≤ β + e ^ 2 / 100 := by positivity
    have hle1 : β + e ^ 2 / 100 ≤ 1 := by linarith
    have h1 : (1 - e ^ 2 / 1000) * (β + e ^ 2 / 100) ≤ μ * (β + e ^ 2 / 100) :=
      mul_le_mul_of_nonneg_right hmu' hpos'
    have h2 : e ^ 2 / 1000 * (β + e ^ 2 / 100) ≤ e ^ 2 / 1000 :=
      mul_le_of_le_one_right (by positivity) hle1
    have he2pos : 0 ≤ e ^ 2 := sq_nonneg e
    have h3 : β + e ^ 2 / 200 ≤ μ * (β + e ^ 2 / 100) :=
      calc β + e ^ 2 / 200 ≤ (β + e ^ 2 / 100) - e ^ 2 / 1000 := by linarith
        _ ≤ (β + e ^ 2 / 100) - e ^ 2 / 1000 * (β + e ^ 2 / 100) := by linarith
        _ = (1 - e ^ 2 / 1000) * (β + e ^ 2 / 100) := by ring
        _ ≤ μ * (β + e ^ 2 / 100) := h1
    simp only [hβ] at h3 ⊢
    exact h3
  have hRsecond : ((Sparse.primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
      M ^ (1 - 1 / a + e / 100) := by
    refine hRfirst.trans (Real.rpow_le_rpow_of_exponent_le hMone ?_)
    have : e ^ 2 ≤ e := by rw [sq]; exact mul_le_of_le_one_left he0.le he1
    linarith
  have hcard13 : ((Sparse.primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
      (X : ℝ) ^ (1 / 3 : ℝ) := by
    refine hcardBound.trans (Real.rpow_le_rpow_of_exponent_le hX1.le ?_)
    have he2 : e ^ 2 ≤ 1 := pow_le_one₀ he0.le he1
    linarith
  have hsupport := Sparse.dyadicPrimePowerSupport_range hPpos.le rfl hpower
  have hUsub : U ⊆ Set.Icc (-(X : ℝ)) X := by
    intro t ht
    have h := largePrimeValueSet_subset_Icc (X : ℝ) P e ht
    exact ⟨by linarith [h.1, Real.rpow_nonneg hXpos.le (1 / 1000 : ℝ)], h.2⟩
  have hprime : ∀ t ∈ U, P ^ (-e / 10) ≤
      ‖Sparse.primeBasePolynomial (dyadicPrimes P) (onePlusIT t)‖ := by
    intro t ht
    rw [← primeDirichletPolynomial_eq_primeBase]
    exact ht.2
  have hblocks : ∀ j ∈ Finset.range 5, 2 ≤ (2 : ℝ) ^ j * (n₁ : ℝ) ^ (5 : ℕ) := by
    intro j _
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have h2 : (2 : ℝ) ≤ (n₁ : ℝ) ^ (5 : ℕ) := by
      have hn₁two : (2 : ℝ) ≤ n₁ := by
        have : (2 : ℝ) ≤ M₁ / 2 := by linarith
        linarith
      calc (2 : ℝ) ≤ (n₁ : ℝ) := hn₁two
        _ ≤ (n₁ : ℝ) ^ (5 : ℕ) := by
          exact le_self_pow₀ (by linarith) (by norm_num)
    calc (2 : ℝ) ≤ (n₁ : ℝ) ^ (5 : ℕ) := h2
      _ = 1 * (n₁ : ℝ) ^ (5 : ℕ) := by ring
      _ ≤ (2 : ℝ) ^ j * (n₁ : ℝ) ^ (5 : ℕ) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
  -- the sparse argument, given the key inequality of the second branch
  have hsparse : (1 - 1 / a - (e / 3 + e ^ 2 / 1000 * (1 - 1 / a)) ≤
        θ * (1 - 2 * TypeII.upperBinExponent (n₁ : ℝ) bin.1) →
      1 / a + (4 * e + e ^ 2 / 25) <
        Sparse.secondBranchKeyExponent θ (TypeII.upperBinExponent (n₁ : ℝ) bin.1)
          (TypeII.upperBinExponent (N₂ : ℝ) bin.2)) →
      volume.real V ≤ K * Sparse.sparsePropagationScaleTarget (n₁ : ℝ) (N₂ : ℝ)
          (TypeII.upperBinExponent (n₁ : ℝ) bin.1)
          (TypeII.upperBinExponent (N₂ : ℝ) bin.2) * (X : ℝ) ^ (-(e ^ 2)) := by
    intro hkey
    let d : Completion.SparsePropagationMediumBinData (X : ℝ) e Bcoeff :=
      { P := P, M := M, M1 := (n₁ : ℝ), M2 := (N₂ : ℝ), A0 := Acoeff, a := a,
        theta := θ, phi := φ, mu := μ,
        scaleError := e ^ 2 / 1000, firstError := e / 3,
        residualError := e / 3 + e ^ 2 / 1000 * (1 - 1 / a),
        keyError := 4 * e + e ^ 2 / 25,
        k := k, beta := γ, b := b, ambient := U,
        partitionEpsilon := Completion.outerPartitionEpsilon σs, bin := bin,
        hpartitionEpsilon := by
          simp only [Completion.outerPartitionEpsilon]; linarith
        hX := hX1
        hPdef := hPa
        ha := ha1
        hk := rfl
        hden := hden
        hMdef := rfl
        hM := hMone
        hMX := hMX
        hM1 := hn₁pos
        hM2 := hN₂two
        hM1lower := hn₁lo
        hsigmaStrong := by linarith
        hsupport := hsupport
        hcard := hcard13
        hb := hbdiv
        hblocks := hblocks
        hambient := measurableSet_largePrimeValueSet _ _ _
        hambientSub := hUsub
        hprime := hprime
        htheta := rfl
        hMExponent := hmu
        htheta0 := by rw [hθ]; exact div_nonneg (Real.log_nonneg hn₁one.le) hlogpos.le
        htheta1 := by linarith
        hresidualError := rfl
        hkey := hkey
        hMcoord := hMcoord
        hM1coord := hn₁coord
        hM2coord := hN₂coord
        hRboundFirst := hRfirst
        hRboundSecond := hRsecond
        haLower := by linarith
        haUpper := hahi'
        hmuLower := by
          have h1 : e ^ 2 ≤ e := by rw [sq]; exact mul_le_of_le_one_left he0.le he1
          linarith
        hmuUpper := hμhi
        hthetaLower := hθlo
        hthetaUpper := hθhi
        hphiUpper := hφhi
        hproductLoss := hproductLoss
        hfirstReserve := le_refl _
        hsecondReserve := by
          have h1 : 2 * TypeII.upperBinExponent (N₂ : ℝ) bin.2 * (e ^ 2 / 100) ≤
              2 * 2 * (e ^ 2 / 100) := by gcongr
          linarith }
    have hcl := hlossX γ (N₂ : ℝ) φ hγ hN₂one.le hN₂coord hφhi
    have hres := Completion.sparsePropagation_uniformPackage_on_mediumLogBin
      hpackage d he0 hcl
    simp only [Completion.sparsePropagationMediumLogBin, d] at hres
    rw [hbfun] at hres
    rw [hV, hF₁, hF₂]
    clear_value d
    clear d
    have he3 : -3 * e ≤ -(e ^ 2) := by
      have : e ^ 2 ≤ e := by rw [sq]; exact mul_le_of_le_one_left he0.le he1
      linarith only [this, he0]
    have hXrpow : (X : ℝ) ^ (-3 * e) ≤ (X : ℝ) ^ (-(e ^ 2)) :=
      Real.rpow_le_rpow_of_exponent_le hX1.le he3
    have hXe2 : 0 ≤ (X : ℝ) ^ (-(e ^ 2)) := Real.rpow_nonneg hXpos.le _
    generalize Sparse.sparsePropagationScaleTarget (n₁ : ℝ) (N₂ : ℝ)
      (TypeII.upperBinExponent (n₁ : ℝ) bin.1)
      (TypeII.upperBinExponent (N₂ : ℝ) bin.2) = T at hres htarget0 ⊢
    generalize (X : ℝ) ^ (-(e ^ 2)) = W at hres hXrpow hXe2 ⊢
    generalize (X : ℝ) ^ (-3 * e) = W' at hres hXrpow
    have hC0 : 0 ≤ Sparse.secondBranchPowerConstant Cp Dp Acoeff e := by
      unfold Sparse.secondBranchPowerConstant; positivity
    generalize Sparse.secondBranchPowerConstant Cp Dp Acoeff e = C' at hres hCK hC0
    have hTW : 0 ≤ T * W := mul_nonneg htarget0 hXe2
    have hC'T : 0 ≤ C' * T := mul_nonneg hC0 htarget0
    rcases hres with h | h
    · nlinarith only [h, h2K, hTW]
    · nlinarith only [h, hCK, hTW, hXrpow, htarget0, hC'T]

  -- the three cases
  obtain ⟨hMA, hMB, hv, hr⟩ := window_margins hη he0 hesmall heη halo' hahi'
  have hθ0 : 0 ≤ θ := by
    rw [hθ]; exact div_nonneg (Real.log_nonneg hn₁one.le) hlogpos.le
  have hφ0 : 0 ≤ φ := by
    rw [hφ]; exact div_nonneg (Real.log_nonneg hN₂one.le) hlogpos.le
  have hprodUp : (n₁ : ℝ) * (N₂ : ℝ) ≤ (X : ℝ) := by
    have h1 : (n₁ : ℝ) * (N₂ : ℝ) ≤ M₁ * (2 * M₂) :=
      mul_le_mul hn₁le hN₂hi (by positivity) (by linarith only [hM₁pos])
    have h3 : 8 * (X : ℝ) / P ≤ (X : ℝ) := by
      rw [div_le_iff₀ hPpos]; nlinarith only [hP8, hXpos]
    have h4 : M₁ * (2 * M₂) = 2 * (M₁ * M₂) := by ring
    have h5 : 2 * (4 * (X : ℝ) / P) = 8 * (X : ℝ) / P := by ring
    linarith only [h1, h3, h4, h5, hprodHi]
  have hθφ : θ + φ ≤ 1 := by
    have h := Real.log_le_log (by positivity) hprodUp
    rw [Real.log_mul hn₁pos.ne' hN₂pos.ne'] at h
    rw [hθ, hφ, ← add_div, div_le_one hlogpos]
    exact h
  have hVsubX : V ⊆ Set.Icc 0 (X : ℝ) := by
    intro t ht
    have h := largePrimeValueSet_subset_Icc (X : ℝ) P e (mediumBin_subset_ambient ht)
    exact ⟨(Real.rpow_nonneg hXpos.le _).trans h.1, h.2⟩
  have hlargeA : ∀ t ∈ V, (n₁ : ℝ) ^ (-TypeII.upperBinExponent (n₁ : ℝ) bin.1) <
      ‖dyadicDirichletPolynomial (Completion.supportedTypeIIFirstCoefficient δ M₁ R α)
        (n₁ : ℝ) (onePlusIT t)‖ :=
    fun t ht ↦ mediumBin_first_large hn₁one hXpos ht
  have hlargeB : ∀ t ∈ V, (N₂ : ℝ) ^ (-TypeII.upperBinExponent (N₂ : ℝ) bin.2) <
      ‖dyadicDirichletPolynomial γ (N₂ : ℝ) (onePlusIT t)‖ :=
    fun t ht ↦ mediumBin_second_large hN₂one hXpos ht
  have hN₂nat : 1 ≤ N₂ := by exact_mod_cast hN₂one.le
  have hcdiv : IsDivisorBoundedByConstant Bcoeff Acoeff
      (Completion.supportedTypeIIFirstCoefficient δ M₁ R α) :=
    Completion.supportedTypeIIFirstCoefficient_isDivisorBoundedByConstant hα
  exact medium_bin_three_cases (r := e / 3 + e ^ 2 / 1000 * (1 - 1 / a))
    (κ := 4 * e + e ^ 2 / 25) hX1 he0 hMA hMB hv hr hesmall hθ0 hθhi hθφ
    hproductLoss hσsLo hup1 hup2 hCa.le hCb.le hCaK hCbK htarget0
    (fun σ h0 h14 h1 h2 ↦ sparseTarget_lower_bound hX1 hn₁coord hN₂coord hθ0 hφ0
      h0 h14 h1 h2 hproductLoss)
    (fun hθ7 h30 hlo ↦ hDaX n₁ _ V _ θ hcdiv hn₁coord hθ7 hθhi h30 hlo hVsubX hlargeA)
    (fun η₀ h1 h2 h3 h4 h5 h6 h7 ↦
      hDbX N₂ γ V _ φ η₀ hγ hN₂nat hN₂coord h1 h2 h3 h4 h5 h6 h7 hVsubX hlargeB)
    hsparse

/-! ## One naturalized product -/

/-- The outer partition with explicit bounds for the three pieces, in the
form used below. -/
theorem naturalProduct_integral_le {E : Set ℝ} {F₁ F₂ : ℂ → ℂ}
    {N₁ N₂ X σ E₁ K saving : ℝ}
    (hX : 1 ≤ X) (hN₁ : 1 < N₁) (hN₂ : 1 < N₂) (hσ : 0 ≤ σ)
    (hK : 0 ≤ K) (hsaving : 0 ≤ saving)
    (hE : MeasurableSet E) (hEsub : E ⊆ Set.Icc 0 X)
    (hF₁ : Continuous (fun t : ℝ ↦ F₁ (onePlusIT t)))
    (hF₂ : Continuous (fun t : ℝ ↦ F₂ (onePlusIT t)))
    (hlarge : (∫ t in TypeII.largeValueR1 E F₁ F₂ N₁ N₂
          (Completion.outerPartitionEpsilon σ),
          TypeII.typeIIMagnitude F₁ t ^ (2 : ℕ) *
            TypeII.typeIIMagnitude F₂ t ^ (2 : ℕ)) ≤ E₁)
    (hbins : ∀ k ∈ TypeII.logMagnitudePairIndexRange X,
      volume.real (TypeII.mediumLogMagnitudeBinSet E F₁ F₂
        N₁ N₂ X (Completion.outerPartitionEpsilon σ) k) ≤
        K * Sparse.sparsePropagationScaleTarget N₁ N₂
          (TypeII.upperBinExponent N₁ k.1)
          (TypeII.upperBinExponent N₂ k.2) * saving) :
    (∫ t in E, ‖F₁ (onePlusIT t) * F₂ (onePlusIT t)‖ ^ (2 : ℕ)) ≤
      E₁ + (Real.log X + 1) ^ 2 * (Real.exp 4 * K * saving) + X⁻¹ := by
  have hXpos : 0 < X := by linarith
  have hEsub' : E ⊆ Set.Icc (-X) X := fun t ht ↦
    ⟨by linarith [(hEsub ht).1], (hEsub ht).2⟩
  have hmain := Completion.integral_typeII_outerPartition_le hXpos hN₁ hN₂ hσ
    hE hEsub' hF₁ hF₂ hlarge hbins
  have hint : (∫ t in E, ‖F₁ (onePlusIT t) * F₂ (onePlusIT t)‖ ^ (2 : ℕ)) =
      ∫ t in E, TypeII.typeIIMagnitude F₁ t ^ (2 : ℕ) *
        TypeII.typeIIMagnitude F₂ t ^ (2 : ℕ) := by
    simp only [norm_mul, mul_pow, TypeII.typeIIMagnitude]
  rw [hint]
  refine hmain.trans ?_
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX
  have hcount : ((((⌊Real.log X⌋ + 1).toNat) ^ 2 : ℕ) : ℝ) ≤
      (Real.log X + 1) ^ 2 := by
    have hfl : (0 : ℤ) ≤ ⌊Real.log X⌋ + 1 := by
      have := Int.floor_nonneg.mpr hlog0; omega
    have hcast : (((⌊Real.log X⌋ + 1).toNat : ℕ) : ℝ) = (⌊Real.log X⌋ : ℝ) + 1 := by
      have h := Int.toNat_of_nonneg hfl
      have h2 : (((⌊Real.log X⌋ + 1).toNat : ℤ) : ℝ) = ((⌊Real.log X⌋ + 1 : ℤ) : ℝ) := by
        rw [h]
      push_cast at h2
      exact_mod_cast h2
    push_cast
    rw [hcast]
    have h1 : (⌊Real.log X⌋ : ℝ) + 1 ≤ Real.log X + 1 := by
      linarith [Int.floor_le (Real.log X)]
    have h0 : (0 : ℝ) ≤ (⌊Real.log X⌋ : ℝ) + 1 := by exact_mod_cast hfl
    nlinarith
  have hR3 : volume.real (TypeII.largeValueR3 E F₁ F₂ N₁ N₂ X
      (Completion.outerPartitionEpsilon σ)) ≤ X := by
    have hsub : TypeII.largeValueR3 E F₁ F₂ N₁ N₂ X
        (Completion.outerPartitionEpsilon σ) ⊆ Set.Icc 0 X :=
      fun t ht ↦ hEsub ht.1.1
    calc volume.real (TypeII.largeValueR3 E F₁ F₂ N₁ N₂ X
          (Completion.outerPartitionEpsilon σ)) ≤ volume.real (Set.Icc 0 X) :=
          measureReal_mono hsub (by simp)
      _ = X := by simp [hXpos.le]
  have hbinsTerm : 0 ≤ Real.exp 4 * K * saving := by positivity
  have hR3term : volume.real (TypeII.largeValueR3 E F₁ F₂ N₁ N₂ X
      (Completion.outerPartitionEpsilon σ)) * (X⁻¹) ^ (2 : ℕ) ≤ X⁻¹ := by
    calc _ ≤ X * (X⁻¹) ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_right hR3 (by positivity)
      _ = X⁻¹ := by field_simp
  have := mul_le_mul_of_nonneg_right hcount hbinsTerm
  linarith

/-! ## Decay comparisons with `exp(-(log log X)^6)` -/

theorem eventually_rpow_neg_le_loglogSix {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℕ in atTop, (X : ℝ) ^ (-κ) ≤ loglogSixSaving (X : ℝ) := by
  have h7 := tendsto_natCast_atTop_atTop.eventually
    (Sparse.eventually_rpow_neg_le_exp_neg_loglog_seven hκ)
  have hll : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log (Real.log (X : ℝ)) :=
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)).eventually_ge_atTop 1
  filter_upwards [h7, hll] with X h7X hllX
  refine h7X.trans ?_
  unfold loglogSixSaving
  apply Real.exp_le_exp.mpr
  have : (Real.log (Real.log (X : ℝ))) ^ (6 : ℕ) ≤
      (Real.log (Real.log (X : ℝ))) ^ (7 : ℕ) :=
    pow_le_pow_right₀ hllX (by norm_num)
  linarith

theorem eventually_exp_neg_two_rpow_le_loglogSix :
    ∀ᶠ X : ℕ in atTop,
      Real.exp (-2 * (Real.log (X : ℝ)) ^ (1 / 10 : ℝ)) ≤
        loglogSixSaving (X : ℝ) := by
  have hlogNat : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := hlogNat.eventually
    (TypeII.eventually_log_rpow_le_rpow 6 (δ := 1 / 10) (by norm_num))
  filter_upwards [h, hlogNat.eventually_ge_atTop 1] with X hX hX1
  unfold loglogSixSaving
  apply Real.exp_le_exp.mpr
  have hll0 : 0 ≤ Real.log (Real.log (X : ℝ)) := Real.log_nonneg hX1
  have h6 : (Real.log (Real.log (X : ℝ))) ^ (6 : ℕ) ≤
      (Real.log (X : ℝ)) ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_natCast]; exact_mod_cast hX
  have hpos : 0 ≤ (Real.log (X : ℝ)) ^ (1 / 10 : ℝ) :=
    Real.rpow_nonneg (by linarith) _
  calc -2 * (Real.log (X : ℝ)) ^ (1 / 10 : ℝ) ≤
        -((Real.log (X : ℝ)) ^ (1 / 10 : ℝ)) := by linarith
    _ ≤ -((Real.log (Real.log (X : ℝ))) ^ (6 : ℕ)) := neg_le_neg h6

theorem eventually_logsq_mul_rpow_neg_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop,
      (Real.log (X : ℝ) + 1) ^ 2 * (X : ℝ) ^ (-c) ≤ (X : ℝ) ^ (-(c / 2)) := by
  have h := eventually_const_mul_log_rpow_le_rpow 4 2 (c := c / 2) (by positivity)
  have hlogNat : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [h, hlogNat.eventually_ge_atTop 1, eventually_ge_atTop 1]
    with X hX hlog hX1
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX1
  have hsq : (Real.log (X : ℝ) + 1) ^ 2 ≤ 4 * (Real.log (X : ℝ)) ^ (2 : ℝ) := by
    rw [Real.rpow_two]; nlinarith
  calc (Real.log (X : ℝ) + 1) ^ 2 * (X : ℝ) ^ (-c)
      ≤ (X : ℝ) ^ (c / 2) * (X : ℝ) ^ (-c) :=
        mul_le_mul_of_nonneg_right (hsq.trans hX) (by positivity)
    _ = (X : ℝ) ^ (-(c / 2)) := by
        rw [← Real.rpow_add hXpos]; ring_nf

/-! ## Main theorem -/

/-- **The Type II component bound** follows from the cited inputs. -/
theorem typeIIComponentStatement_of_inputs (inputs : ExternalInputs) :
    TypeIIComponentStatement := by
  intro η₀ hη₀
  obtain ⟨C₁, ε₅, hC₁, hε₅, hR1⟩ := typeII_R1_uniform inputs
  set η := min η₀ (1 / 250) with hηdef
  have hη : 0 < η := lt_min hη₀ (by norm_num)
  have hηle : η ≤ η₀ := min_le_left _ _
  have hη' : η ≤ 1 / 250 := min_le_right _ _
  refine ⟨min (min ε₅ (1 / 20000)) (min (1 / (1000 * C₁)) (η / 20)),
    by positivity, ?_⟩
  intro ε hε hεle A hA Bcoeff Acoeff hB hAc
  have hε5 : ε ≤ ε₅ := hεle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hε0 : ε ≤ 1 / 20000 :=
    hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hC₁ε : C₁ * ε ≤ 1 / 1000 := by
    have := hεle.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hεη : 20 * ε ≤ η := by
    have := hεle.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hA0 : 0 < A := by linarith
  obtain ⟨κ₁, hκ₁, hR1'⟩ := hR1 ε hε hε5 Bcoeff hB
  obtain ⟨C₂, CR, hC₂, hCR, hR1ev⟩ := hR1' Acoeff hAc
  obtain ⟨K, hK, hbins⟩ := typeII_bins_uniform inputs hη hη' hε hε0 hεη hA0
    hB hAc hC₁ε
  obtain ⟨XVK, D, hXVK, hD, hVK⟩ :=
    Completion.structuredShortSegmentDecay_of_inputs inputs ε hε A hA
  have hR1N := tendsto_natCast_atTop_atTop.eventually hR1ev
  have habsorb := tendsto_natCast_atTop_atTop.eventually
    (Completion.eventually_logPower_mul_const_structuredBound_sq_small C₂ D)
  have hwidth := tendsto_natCast_atTop_atTop.eventually
    (Completion.eventually_source_width_three_halves hA0)
  have hres := tendsto_natCast_atTop_atTop.eventually
    (Completion.eventually_sourceTypeII_naturalization_reserves (11 / 10) hε)
  have hd1 := eventually_rpow_neg_le_loglogSix hκ₁
  have hd2 := eventually_exp_neg_two_rpow_le_loglogSix
  have hd3 := eventually_logsq_mul_rpow_neg_le (c := (ε / 2) ^ 2) (by positivity)
  have hd4 := eventually_rpow_neg_le_loglogSix (κ := (ε / 2) ^ 2 / 2) (by positivity)
  have hd5 := eventually_rpow_neg_le_loglogSix (κ := 1) one_pos
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    (hR1N.and (hbins.and (habsorb.and (hwidth.and (hres.and (hd1.and (hd2.and
      (hd3.and (hd4.and (hd5.and ((eventually_ge_atTop ⌈XVK⌉₊).and
        (eventually_ge_atTop 3))))))))))))
  set Ctot := 16 * (2 * CR + Real.exp 4 * K + 1) with hCtot
  refine ⟨Ctot, by positivity, N₀, ?_⟩
  intro X hX P hPlo hPhi R M₁ M₂ α β Q hR hRup hM₁ hM₂ hα hβ hM₁lo hM₁hi
    hprodLo hprodHi hQ hprodQ hαdef
  obtain ⟨hR1X, hbinsX, habsorbX, hwidthX, hresX, hd1X, hd2X, hd3X, hd4X, hd5X,
    hXVKX, hX3⟩ := hN₀ X hX
  obtain ⟨hfour, _hfloorRes, hcompl, hlog4⟩ := hresX
  have hαeq : α = matomakiTeravainenStructuredTypeIICoefficient
      ((Real.log (X : ℝ)) ^ (-10 * A)) R Q := funext hαdef
  subst hαeq
  set δ := (Real.log (X : ℝ)) ^ (-10 * A) with hδ
  have hX3' : (3 : ℝ) ≤ X := by exact_mod_cast hX3
  have hXpos : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) < X := by linarith
  have hlogpos : 0 < Real.log (X : ℝ) := Real.log_pos hX1
  have hδ0 : 0 ≤ δ := Real.rpow_nonneg hlogpos.le _
  have hXVK' : XVK ≤ (X : ℝ) := (Nat.le_ceil XVK).trans (by exact_mod_cast hXVKX)
  have hlogX1 : (1 : ℝ) ≤ Real.log (X : ℝ) := by linarith
  have hPlo' : (Real.log (X : ℝ)) ^ (1925 / 1763 + η) ≤ P :=
    (Real.rpow_le_rpow_of_exponent_le hlogX1 (by linarith)).trans hPlo
  have hP1 : 1 ≤ P := by
    have h1 : (1 : ℝ) ≤ (Real.log (X : ℝ)) ^ (1925 / 1763 + η) :=
      Real.one_le_rpow hlogX1 (by positivity)
    linarith
  have hPpos : 0 < P := by linarith
  have hM₁four : 4 ≤ M₁ := hfour.trans hM₁lo
  have hprodLo' : (X : ℝ) / (2 * P) < M₁ * M₂ := by
    rwa [show (X : ℝ) / P / 2 = (X : ℝ) / (2 * P) by rw [div_div, mul_comm]] at hprodLo
  have hprodHi' : M₁ * M₂ ≤ 4 * (X : ℝ) / P := by
    rwa [show 4 * ((X : ℝ) / P) = 4 * (X : ℝ) / P by ring] at hprodHi
  have hreserve : 4 * P * M₁ ≤ (X : ℝ) := by
    calc 4 * P * M₁ ≤ 4 * (Real.log (X : ℝ)) ^ (11 / 10 : ℝ) * M₁ := by gcongr
      _ ≤ 4 * (Real.log (X : ℝ)) ^ (11 / 10 : ℝ) * (X : ℝ) ^ (2 / 11 : ℝ) := by
        gcongr
      _ ≤ (X : ℝ) := hcompl
  have hM₂gt : 2 < M₂ :=
    Completion.representedTypeII_secondScale_ge_two_of_reserve hPpos
      (by linarith) hprodLo' hreserve
  have hupper : (1 + δ) ^ R * M₁ ≤
      2 * (TypeII.naturalDyadicCoreScale M₁ : ℝ) :=
    Completion.structuredUpper_le_two_floor hM₁four (hwidthX R hRup)
  set U := largePrimeValueSet (X : ℝ) P (ε / 2) with hU
  have hUmeas : MeasurableSet U := measurableSet_largePrimeValueSet _ _ _
  have hUsub : U ⊆ Set.Icc 0 (X : ℝ) := fun t ht ↦
    ⟨(Real.rpow_nonneg hXpos.le _).trans ht.1.1, ht.1.2⟩
  -- the structured bound on `𝒰`
  set S := (D * Real.exp (-2 * (Real.log (X : ℝ)) ^ (1 / 10 : ℝ))) ^ (2 : ℕ)
    with hS
  have hQpos : ∀ j, 0 < Q j := fun j ↦ (Real.exp_pos _).trans_le (hQ j).1
  have hSbound : ∀ t ∈ U,
      ‖dyadicDirichletPolynomial
        (Completion.supportedTypeIIFirstCoefficient δ M₁ R
          (matomakiTeravainenStructuredTypeIICoefficient δ R Q))
        (TypeII.naturalDyadicCoreScale M₁ : ℝ)
        (onePlusIT t)‖ ^ (2 : ℕ) ≤ S := by
    intro t ht
    rw [Completion.naturalStructuredFirstFactor_eq_shortPrimeProduct hδ0 hR
      (by linarith) hQpos hprodQ hupper]
    have hb := hVK (X : ℝ) M₁ t R Q hXVK' hR hRup hQ hprodQ hM₁lo hM₁hi
      ht.1.1 ht.1.2
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hS0 : 0 ≤ S := by positivity
  set V := CR * ((X : ℝ) ^ (-κ₁) + (Real.log (X : ℝ)) ^ C₂ * S) +
    (Real.log (X : ℝ) + 1) ^ 2 * (Real.exp 4 * K * (X : ℝ) ^ (-((ε / 2) ^ 2))) +
    (X : ℝ)⁻¹ with hV
  have hN₁gt : (1 : ℝ) < (TypeII.naturalDyadicCoreScale M₁ : ℝ) := by
    have := TypeII.half_le_naturalDyadicCoreScale (by linarith : (2 : ℝ) ≤ M₁)
    linarith
  have hσ0 : 0 ≤ 17 / 70 - C₁ * ε := by linarith
  -- one naturalized product
  have hone : ∀ (N₂ : ℕ) (γ : ℕ → ℂ),
      (N₂ = TypeII.naturalDyadicCoreScale M₂ ∨
        N₂ = TypeII.naturalDyadicBoundaryScale M₂) →
      IsDivisorBoundedByConstant Bcoeff Acoeff γ →
      (∫ t in U,
        ‖dyadicDirichletPolynomial
            (Completion.supportedTypeIIFirstCoefficient δ M₁ R
              (matomakiTeravainenStructuredTypeIICoefficient δ R Q))
            (TypeII.naturalDyadicCoreScale M₁ : ℝ) (onePlusIT t) *
          dyadicDirichletPolynomial γ (N₂ : ℝ) (onePlusIT t)‖ ^ (2 : ℕ)) ≤ V := by
    intro N₂ γ hN₂ hγ
    have hN₂gt : (1 : ℝ) < (N₂ : ℝ) := by
      have hcore : (2 : ℝ) ≤ (TypeII.naturalDyadicCoreScale M₂ : ℝ) := by
        have : 2 ≤ TypeII.naturalDyadicCoreScale M₂ :=
          Nat.le_floor (by push_cast; linarith)
        exact_mod_cast this
      rcases hN₂ with h | h
      · rw [h]; linarith
      · rw [h, TypeII.naturalDyadicBoundaryScale]; push_cast; linarith
    have hlarge := hR1X P M₁ M₂ δ R N₂
      (matomakiTeravainenStructuredTypeIICoefficient δ R Q) γ U S hP1 hPhi
      hM₁lo hM₁hi hprodLo' hprodHi' hN₂ hα hγ hUmeas hUsub hS0 hSbound
    have hbinsB := hbinsX P M₁ M₂ R Q
      (matomakiTeravainenStructuredTypeIICoefficient δ R Q) γ N₂ hPlo' hPhi
      hRup (fun m ↦ rfl) hα hM₁lo hM₁hi hprodLo' hprodHi' hN₂ hγ
    have hmain := naturalProduct_integral_le (by linarith) hN₁gt hN₂gt hσ0
      hK.le (Real.rpow_nonneg hXpos.le _) hUmeas hUsub
      (Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse _ _)
      (Sparse.continuous_dyadicDirichletPolynomial_onePlusIT_sparse _ _)
      hlarge hbinsB
    exact hmain
  have hUsub' : U ⊆ Set.Icc (-(X : ℝ)) X := fun t ht ↦
    ⟨by linarith [(hUsub ht).1], (hUsub ht).2⟩
  have hbdry := (Completion.representedTypeII_naturalCoefficients_divisorBounded
    (delta := δ) (M₁ := M₁) (M₂ := M₂) (R := R) hα hβ).2.2
  have hresid := Completion.integral_representedTypeII_le_four_mul_of_naturalizedResidual
    (f := matomakiTeravainenTypeIIValue δ M₁ M₂ R
      (matomakiTeravainenStructuredTypeIICoefficient δ R Q) β)
    hδ0 (by linarith : 0 < M₁) (by linarith : 1 ≤ M₂) hXpos.le hUmeas hUsub'
    hupper (fun n ↦ rfl)
    ⟨hone _ β (Or.inl rfl) hβ, hone _ _ (Or.inr rfl) hbdry⟩
  have hFcont : Continuous (fun t : ℝ ↦ dirichletPolynomial
      (matomakiTeravainenTypeIIValue δ M₁ M₂ R
        (matomakiTeravainenStructuredTypeIICoefficient δ R Q) β)
      (Sparse.typeIIProductSupport δ M₁ M₂ R) (onePlusIT t)) :=
    Sparse.continuous_dirichletPolynomial_onePlusIT_sparse _ _
  have hP4 := integral_primeFactor_mul_le_four_mul hP1 hUmeas hUsub hFcont
  refine hP4.trans ?_
  -- final numerical comparison
  have hL6 : 0 ≤ loglogSixSaving (X : ℝ) := (Real.exp_pos _).le
  have hterm2 : (Real.log (X : ℝ)) ^ C₂ * S ≤ loglogSixSaving (X : ℝ) :=
    habsorbX.trans hd2X
  have hterm3 : (Real.log (X : ℝ) + 1) ^ 2 * (X : ℝ) ^ (-((ε / 2) ^ 2)) ≤
      loglogSixSaving (X : ℝ) := hd3X.trans hd4X
  have hterm4 : (X : ℝ)⁻¹ ≤ loglogSixSaving (X : ℝ) := by
    rw [← Real.rpow_neg_one]; exact hd5X
  have hVle : V ≤ (2 * CR + Real.exp 4 * K + 1) * loglogSixSaving (X : ℝ) := by
    have h1 : CR * ((X : ℝ) ^ (-κ₁) + (Real.log (X : ℝ)) ^ C₂ * S) ≤
        CR * (loglogSixSaving (X : ℝ) + loglogSixSaving (X : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hd1X hterm2) hCR.le
    have h2 : (Real.log (X : ℝ) + 1) ^ 2 *
        (Real.exp 4 * K * (X : ℝ) ^ (-((ε / 2) ^ 2))) =
        Real.exp 4 * K * ((Real.log (X : ℝ) + 1) ^ 2 *
          (X : ℝ) ^ (-((ε / 2) ^ 2))) := by ring
    have h3 : Real.exp 4 * K * ((Real.log (X : ℝ) + 1) ^ 2 *
          (X : ℝ) ^ (-((ε / 2) ^ 2))) ≤
        Real.exp 4 * K * loglogSixSaving (X : ℝ) :=
      mul_le_mul_of_nonneg_left hterm3 (by positivity)
    rw [hV]
    nlinarith only [h1, h2, h3, hterm4, hL6]
  calc 4 * (∫ t in U, ‖dirichletPolynomial
          (matomakiTeravainenTypeIIValue δ M₁ M₂ R
            (matomakiTeravainenStructuredTypeIICoefficient δ R Q) β)
          (Sparse.typeIIProductSupport δ M₁ M₂ R) (onePlusIT t)‖ ^ (2 : ℕ))
      ≤ 4 * (4 * V) := by linarith only [hresid]
    _ ≤ 16 * ((2 * CR + Real.exp 4 * K + 1) * loglogSixSaving (X : ℝ)) := by
        linarith only [hVle]
    _ = Ctot * loglogSixSaving (X : ℝ) := by rw [hCtot]; ring

end

end Final
end ExactSemiprimes
