import ExactSemiprimes.Sparse.ResidualRange
import ExactSemiprimes.Sparse.PrimePowerPolynomial
import ExactSemiprimes.TypeII.PoweredPolynomial
import ExactSemiprimes.Hybrid.HybridDensity
import ExactSemiprimes.Assumptions

/-! # Second Heath--Brown sparse branch -/

namespace ExactSemiprimes
namespace Sparse

open Filter Set MeasureTheory
open scoped BigOperators

noncomputable section

/-! ## The powered coefficient used in the second branch -/

/-- Specializing the repaired convolution estimate to the fifth power gives
exactly the coefficient exponent `5B+4` asserted in Section 6.  This is an
internal finite-combinatorial fact; it does not use the imported sparse
mean-value theorem. -/
theorem fifthPowerCoefficient_divisorBound
    {a : ℕ → ℂ} {S : Finset ℕ} {B A₀ : ℝ} {n : ℕ}
    (hn : 0 < n) (ha : IsDivisorBoundedByConstant B A₀ a) :
    ‖TypeII.powerConvolutionCoefficient a S 5 n‖ ≤
      A₀ ^ (5 : ℕ) * (divisorCount n : ℝ) ^ (5 * B + 4) := by
  have h := TypeII.norm_powerConvolutionCoefficient_le_divisorCount
    (S := S) (ℓ := 5) (n := n) (by norm_num) hn ha
  simpa only [Nat.cast_ofNat,
    show B * (5 : ℝ) + 5 - 1 = 5 * B + 4 by ring] using h

/-- A finite Dirichlet polynomial on a support not containing zero is
continuous on the line `1+it`. -/
theorem continuous_dirichletPolynomial_onePlusIT_of_zero_not_mem
    (a : ℕ → ℂ) (S : Finset ℕ) (hS : 0 ∉ S) :
    Continuous (fun t : ℝ ↦ dirichletPolynomial a S (onePlusIT t)) := by
  unfold dirichletPolynomial onePlusIT
  apply continuous_finsetSum
  intro n hn
  apply Continuous.const_mul
  apply (show Continuous (fun t : ℝ ↦ -(1 + (t : ℂ) * Complex.I)) by
    fun_prop).const_cpow
  left
  exact_mod_cast (Nat.ne_zero_iff_zero_lt.mpr
    (Nat.pos_of_ne_zero (fun h ↦ hS (h ▸ hn))))

/-- The real coefficient obtained by collecting an `ell`-fold product
according to the product of its indices. -/
def realPowerConvolutionCoefficient (b : ℕ → ℝ) (S : Finset ℕ)
    (ell n : ℕ) : ℝ :=
  ∑ f ∈ TypeII.powerTuples S ell with TypeII.tupleProduct f = n,
    ∏ i, b (f i)

/-- Complexifying the real collected coefficient gives the existing
complex convolution coefficient exactly. -/
theorem realPowerConvolutionCoefficient_cast (b : ℕ → ℝ)
    (S : Finset ℕ) (ell n : ℕ) :
    (realPowerConvolutionCoefficient b S ell n : ℂ) =
      TypeII.powerConvolutionCoefficient
        (fun m ↦ (b m : ℂ)) S ell n := by
  simp [realPowerConvolutionCoefficient,
    TypeII.powerConvolutionCoefficient, TypeII.tupleCoefficient]

/-- Collecting the tuple expansion by its integer product gives a genuine
finite Dirichlet polynomial with real coefficients. -/
theorem real_dirichletPolynomial_pow_eq_supportSum
    (b : ℕ → ℝ) (S : Finset ℕ) (s : ℂ) (ell : ℕ) :
    dirichletPolynomial (fun n ↦ (b n : ℂ)) S s ^ ell =
      ∑ n ∈ (TypeII.powerTuples S ell).image TypeII.tupleProduct,
        (realPowerConvolutionCoefficient b S ell n : ℂ) *
          (n : ℂ) ^ (-s) := by
  rw [TypeII.dirichletPolynomial_pow_eq_tupleSum]
  have hterm : ∀ f : Fin ell → ℕ,
      (∏ i, ((b (f i) : ℂ) * (f i : ℂ) ^ (-s))) =
        (((∏ i, b (f i)) : ℝ) : ℂ) *
          (TypeII.tupleProduct f : ℂ) ^ (-s) := by
    intro f
    rw [Finset.prod_mul_distrib]
    have hcpow : (∏ i, (f i : ℂ) ^ (-s)) =
        (TypeII.tupleProduct f : ℂ) ^ (-s) := by
      change ∏ i, natCpowMonoidHom (-s) (f i) =
        natCpowMonoidHom (-s) (∏ i, f i)
      rw [map_prod]
    rw [hcpow]
    simp
  simp_rw [hterm]
  have hmaps : ∀ f ∈ TypeII.powerTuples S ell,
      TypeII.tupleProduct f ∈
        (TypeII.powerTuples S ell).image TypeII.tupleProduct := by
    intro f hf
    exact Finset.mem_image.mpr ⟨f, hf, rfl⟩
  have hgroup := Finset.sum_fiberwise_of_maps_to hmaps
    (fun f : Fin ell → ℕ ↦
      (((∏ i, b (f i)) : ℝ) : ℂ) *
        (TypeII.tupleProduct f : ℂ) ^ (-s))
  rw [← hgroup]
  apply Finset.sum_congr rfl
  intro n hn
  rw [realPowerConvolutionCoefficient]
  simp only [Finset.sum_filter, Complex.ofReal_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro f hf
  by_cases hfn : TypeII.tupleProduct f = n
  · simp [hfn]
  · simp [hfn]

/-- The real fifth-convolution coefficient has exactly the repaired
divisor exponent `5B+4`. -/
theorem realFifthPowerCoefficient_divisorBound
    {b : ℕ → ℝ} {S : Finset ℕ} {B A₀ : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hb : IsDivisorBoundedByConstant B A₀ (fun m ↦ (b m : ℂ))) :
    |realPowerConvolutionCoefficient b S 5 n| ≤
      A₀ ^ (5 : ℕ) *
        (divisorCount n : ℝ) ^ (5 * B + 4) := by
  have h := fifthPowerCoefficient_divisorBound (S := S) hn hb
  rw [← realPowerConvolutionCoefficient_cast] at h
  simpa using h

/-- A pointwise coefficient bound controls the literal `NNReal` supremum
used by the cited sparse mean-value theorem. -/
theorem dyadicRealCoefficientSup_le
    {a : ℕ → ℝ} {N K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ n ∈ dyadicInterval N, |a n| ≤ K) :
    dyadicRealCoefficientSup a N ≤ K := by
  unfold dyadicRealCoefficientSup
  have hsup :
      (dyadicInterval N).sup (fun n ↦ Real.toNNReal |a n|) ≤
        Real.toNNReal K := by
    apply Finset.sup_le
    intro n hn
    exact Real.toNNReal_le_toNNReal (ha n hn)
  have hcast := (NNReal.coe_le_coe).2 hsup
  rwa [Real.coe_toNNReal K hK] at hcast

/-- The global divisor-subpower theorem makes the fifth-power coefficient
supremum uniformly subpower on every dyadic output block. -/
theorem realFifthPower_dyadicSup_subpower
    (hglobal : Hybrid.GlobalDivisorSubpowerStatement)
    {b : ℕ → ℝ} {S : Finset ℕ} {B A₀ rho : ℝ}
    (hrho : 0 < rho)
    (hb : IsDivisorBoundedByConstant B A₀ (fun m ↦ (b m : ℂ))) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ N : ℝ, 1 ≤ N →
      dyadicRealCoefficientSup
          (realPowerConvolutionCoefficient b S 5) N ≤
        A₀ ^ (5 : ℕ) * D * (2 * N) ^ rho := by
  have hE : 0 ≤ 5 * B + 4 := by nlinarith [hb.1]
  obtain ⟨D, hD, hDbound⟩ := hglobal (5 * B + 4) rho hE hrho
  refine ⟨D, hD, ?_⟩
  intro N hN
  have hN0 : 0 ≤ N := by linarith
  have hA₀pow : 0 ≤ A₀ ^ (5 : ℕ) := pow_nonneg hb.2.1.le _
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  apply dyadicRealCoefficientSup_le
  · exact mul_nonneg (mul_nonneg hA₀pow hD0)
      (Real.rpow_nonneg (by positivity) rho)
  intro n hn
  have hnrange := (mem_dyadicInterval hN0).mp hn
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt hN0 hnrange.1
    exact_mod_cast this
  have hcoeff := realFifthPowerCoefficient_divisorBound
    (S := S) hnpos hb
  have hdiv := hDbound n hnpos
  have hnpow : (n : ℝ) ^ rho ≤ (2 * N) ^ rho :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) hnrange.2 hrho.le
  calc
    |realPowerConvolutionCoefficient b S 5 n| ≤
        A₀ ^ (5 : ℕ) *
          (divisorCount n : ℝ) ^ (5 * B + 4) := hcoeff
    _ ≤ A₀ ^ (5 : ℕ) * (D * (n : ℝ) ^ rho) :=
      mul_le_mul_of_nonneg_left hdiv hA₀pow
    _ ≤ A₀ ^ (5 : ℕ) * (D * (2 * N) ^ rho) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hnpow hD0) hA₀pow
    _ = A₀ ^ (5 : ℕ) * D * (2 * N) ^ rho := by ring

/-- Exact large-value-set consequence of MT23 Lemma 3.4 with its third
term deleted.  The constant depends only on `eta`.  This is the analytic
application required in the second sparse branch before substituting the
paper's powers of `X`. -/
theorem secondBranch_largeValueMeasure_of_matomakiTeravainen
    (inputs : ExternalInputs) {eta : ℝ} (heta : 0 < eta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (T M N : ℝ) (S : Finset ℕ) (epsilon : ℕ → ℂ)
        (a : ℕ → ℝ) (E : Set ℝ) (L : ℝ),
        1 ≤ M → M ≤ T → 2 ≤ N →
        (∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ T) →
        (∀ m ∈ S, ‖epsilon m‖ ≤ 1) →
        (N ≥ T ^ (2 / 3 : ℝ) ∨
          (S.card : ℝ) ≤ T ^ (1 / 3 : ℝ)) →
        MeasurableSet E → E ⊆ Set.Icc (-T) T → 0 ≤ L →
        (∀ t ∈ E, L ≤
          ‖dirichletPolynomial epsilon S (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖dyadicDirichletPolynomial (fun n ↦ (a n : ℂ)) N
            (onePlusIT t)‖ ^ (2 : ℕ)) →
        volume.real E * L ≤
          C *
            (((S.card : ℝ) / M) ^ (2 : ℕ) +
              (N * T) ^ eta *
                ((S.card : ℝ) * T /
                  (M ^ (2 : ℕ) * N))) *
            (dyadicRealCoefficientSup a N) ^ (2 : ℕ) := by
  obtain ⟨C, hC, hsource⟩ :=
    inputs.matomakiTeravainenLemmaThreeFour eta heta
  refine ⟨C, hC, ?_⟩
  intro T M N S epsilon a E L hM hMT hN hS hepsilon hdelete
    hEmeas hEsub hL hlower
  have hsource' := hsource T M N S epsilon a hM hMT hN hS hepsilon
  have hI := hsource'.2 hdelete
  have hzeroQ : 0 ∉ S := by
    intro hzero
    have hm := hS 0 hzero
    norm_num at hm
    linarith
  have hqcont : Continuous (fun t : ℝ ↦
      dirichletPolynomial epsilon S (onePlusIT t)) :=
    continuous_dirichletPolynomial_onePlusIT_of_zero_not_mem
      epsilon S hzeroQ
  have hzeroA : 0 ∉ dyadicInterval N := by
    intro hz
    have hzrange := (mem_dyadicInterval (by linarith : 0 ≤ N)).mp hz
    norm_num [InDyadicRange] at hzrange
    linarith [hzrange.1]
  have hacont : Continuous (fun t : ℝ ↦
      dyadicDirichletPolynomial (fun n ↦ (a n : ℂ)) N
        (onePlusIT t)) :=
    continuous_dirichletPolynomial_onePlusIT_of_zero_not_mem
      (fun n ↦ (a n : ℂ)) (dyadicInterval N) hzeroA
  let f : ℝ → ℝ := fun t ↦
    ‖dirichletPolynomial epsilon S (onePlusIT t)‖ ^ (2 : ℕ) *
      ‖dyadicDirichletPolynomial (fun n ↦ (a n : ℂ)) N
        (onePlusIT t)‖ ^ (2 : ℕ)
  have hfcont : Continuous f := by
    dsimp [f]
    exact hqcont.norm.pow 2 |>.mul (hacont.norm.pow 2)
  have hfIcc : IntegrableOn f (Set.Icc (-T) T) :=
    hfcont.integrableOn_Icc
  have hfE : IntegrableOn f E := hfIcc.mono_set hEsub
  have hconstE : IntegrableOn (fun _ : ℝ ↦ L) E :=
    continuous_const.integrableOn_Icc.mono_set hEsub
  have hlowerInt : (∫ t in E, L) ≤ ∫ t in E, f t := by
    exact setIntegral_mono_on hconstE hfE hEmeas (by
      intro t ht
      exact hlower t ht)
  have hsubsetInt : (∫ t in E, f t) ≤
      ∫ t in Set.Icc (-T) T, f t := by
    apply setIntegral_mono_set hfIcc
    · filter_upwards [] with t
      dsimp [f]
      positivity
    · filter_upwards [] with t ht
      exact hEsub ht
  calc
    volume.real E * L = ∫ _t in E, L := by
      rw [setIntegral_const]
      simp
    _ ≤ ∫ t in E, f t := hlowerInt
    _ ≤ ∫ t in Set.Icc (-T) T, f t := hsubsetInt
    _ ≤ _ := hI

/-- Dyadic intervals whose starting points differ by powers of two are
pairwise disjoint with the project's open-left, closed-right convention. -/
theorem scaledDyadicIntervals_pairwiseDisjoint {L : ℝ} (hL : 0 < L) :
    (Set.univ : Set ℕ).PairwiseDisjoint
      (fun j : ℕ ↦ dyadicInterval ((2 : ℝ) ^ j * L)) := by
  intro i _ j _ hij
  change Disjoint (dyadicInterval ((2 : ℝ) ^ i * L))
    (dyadicInterval ((2 : ℝ) ^ j * L))
  rw [Finset.disjoint_left]
  intro n hni hnj
  have hscale (r : ℕ) : 0 ≤ (2 : ℝ) ^ r * L := by positivity
  have hi := (mem_dyadicInterval (hscale i)).mp hni
  have hj := (mem_dyadicInterval (hscale j)).mp hnj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hp : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hscaled : (2 : ℝ) ^ (i + 1) * L ≤
        (2 : ℝ) ^ j * L :=
      mul_le_mul_of_nonneg_right hp hL.le
    have hi' : (n : ℝ) ≤ (2 : ℝ) ^ (i + 1) * L := by
      rw [pow_succ]
      nlinarith [hi.2]
    exact (not_lt_of_ge (hi'.trans hscaled)) hj.1
  · have hp : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ i :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hscaled : (2 : ℝ) ^ (j + 1) * L ≤
        (2 : ℝ) ^ i * L :=
      mul_le_mul_of_nonneg_right hp hL.le
    have hj' : (n : ℝ) ≤ (2 : ℝ) ^ (j + 1) * L := by
      rw [pow_succ]
      nlinarith [hj.2]
    exact (not_lt_of_ge (hj'.trans hscaled)) hi.1

theorem fifthTupleProduct_strictLower
    {S : Finset ℕ} {M : ℝ} (hM : 0 < M)
    (hS : ∀ n ∈ S, InDyadicRange M n)
    {f : Fin 5 → ℕ} (hf : f ∈ TypeII.powerTuples S 5) :
    M ^ 5 < (TypeII.tupleProduct f : ℝ) := by
  rw [TypeII.tupleProduct, Nat.cast_prod]
  have hall : ∀ i : Fin 5, M < (f i : ℝ) := by
    intro i
    exact (hS (f i) ((TypeII.mem_powerTuples_iff.mp hf) i)).1
  have hle : ∀ i ∈ (Finset.univ : Finset (Fin 5)),
      M ≤ (f i : ℝ) := by
    intro i hi
    exact (hall i).le
  have hex : ∃ i ∈ (Finset.univ : Finset (Fin 5)),
      M < (f i : ℝ) := by
    exact ⟨0, Finset.mem_univ _, hall 0⟩
  simpa using (Finset.prod_lt_prod₀ (fun _ _ ↦ hM) hle hex)

def fifthPowerDyadicBlocks (M : ℝ) (j : ℕ) : Finset ℕ :=
  dyadicInterval ((2 : ℝ) ^ j * M ^ (5 : ℕ))

theorem fifthPowerSupport_subset_biUnion_blocks
    {S : Finset ℕ} {M : ℝ} (hM : 0 < M)
    (hS : ∀ n ∈ S, InDyadicRange M n) :
    (TypeII.powerTuples S 5).image TypeII.tupleProduct ⊆
      (Finset.range 5).biUnion (fifthPowerDyadicBlocks M) := by
  intro n hn
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hn
  have hlower := fifthTupleProduct_strictLower hM hS hf
  have hbounds := TypeII.tupleProduct_mem_poweredSupport hM.le hf hS
  have hupper : (TypeII.tupleProduct f : ℝ) ≤
      (2 : ℝ) ^ 5 * M ^ 5 := by
    simpa [mul_pow] using hbounds.2
  let x : ℝ := (TypeII.tupleProduct f : ℝ)
  by_cases h₀ : x ≤ 2 * M ^ 5
  · apply Finset.mem_biUnion.mpr
    refine ⟨0, by simp, ?_⟩
    apply (mem_dyadicInterval (by positivity)).2
    simpa [InDyadicRange, fifthPowerDyadicBlocks, x] using
      And.intro hlower h₀
  by_cases h₁ : x ≤ 4 * M ^ 5
  · apply Finset.mem_biUnion.mpr
    refine ⟨1, by simp, ?_⟩
    apply (mem_dyadicInterval (by positivity)).2
    constructor <;> norm_num [InDyadicRange, fifthPowerDyadicBlocks, x] at * <;> linarith
  by_cases h₂ : x ≤ 8 * M ^ 5
  · apply Finset.mem_biUnion.mpr
    refine ⟨2, by simp, ?_⟩
    apply (mem_dyadicInterval (by positivity)).2
    constructor <;> norm_num [InDyadicRange, fifthPowerDyadicBlocks, x] at * <;> linarith
  by_cases h₃ : x ≤ 16 * M ^ 5
  · apply Finset.mem_biUnion.mpr
    refine ⟨3, by simp, ?_⟩
    apply (mem_dyadicInterval (by positivity)).2
    constructor <;> norm_num [InDyadicRange, fifthPowerDyadicBlocks, x] at * <;> linarith
  · apply Finset.mem_biUnion.mpr
    refine ⟨4, by simp, ?_⟩
    apply (mem_dyadicInterval (by positivity)).2
    constructor <;> norm_num [InDyadicRange, fifthPowerDyadicBlocks, x] at * <;> linarith

/-- Outside the product image the collected coefficient is zero. -/
theorem realPowerConvolutionCoefficient_eq_zero_of_not_mem
    {b : ℕ → ℝ} {S : Finset ℕ} {ell n : ℕ}
    (hn : n ∉ (TypeII.powerTuples S ell).image TypeII.tupleProduct) :
    realPowerConvolutionCoefficient b S ell n = 0 := by
  rw [realPowerConvolutionCoefficient]
  apply Finset.sum_eq_zero
  intro f hf
  simp only [Finset.mem_filter] at hf
  exact (hn (Finset.mem_image.mpr ⟨f, hf.1, hf.2⟩)).elim

/-- The actual fifth power is exactly the sum of its five dyadic output
polynomials. -/
theorem real_dirichletPolynomial_fifth_eq_sum_dyadicBlocks
    {b : ℕ → ℝ} {S : Finset ℕ} {M : ℝ} (hM : 0 < M)
    (hS : ∀ n ∈ S, InDyadicRange M n) (s : ℂ) :
    dirichletPolynomial (fun n ↦ (b n : ℂ)) S s ^ (5 : ℕ) =
      ∑ j ∈ Finset.range 5,
        dyadicDirichletPolynomial
          (fun n ↦ (realPowerConvolutionCoefficient b S 5 n : ℂ))
          ((2 : ℝ) ^ j * M ^ (5 : ℕ)) s := by
  rw [real_dirichletPolynomial_pow_eq_supportSum]
  let support : Finset ℕ :=
    (TypeII.powerTuples S 5).image TypeII.tupleProduct
  let blocks : Finset ℕ :=
    (Finset.range 5).biUnion (fifthPowerDyadicBlocks M)
  have hsubset : support ⊆ blocks :=
    fifthPowerSupport_subset_biUnion_blocks hM hS
  have hextra : ∀ n ∈ blocks, n ∉ support →
      (realPowerConvolutionCoefficient b S 5 n : ℂ) *
          (n : ℂ) ^ (-s) = 0 := by
    intro n hn hnSupp
    rw [realPowerConvolutionCoefficient_eq_zero_of_not_mem hnSupp]
    simp
  rw [Finset.sum_subset hsubset hextra]
  have hpair :
      ((↑(Finset.range 5) : Set ℕ)).PairwiseDisjoint
        (fifthPowerDyadicBlocks M) := by
    intro i hi j hj hij
    exact scaledDyadicIntervals_pairwiseDisjoint
      (pow_pos hM (5 : ℕ)) (Set.mem_univ i) (Set.mem_univ j) hij
  rw [Finset.sum_biUnion hpair]
  apply Finset.sum_congr rfl
  intro j hj
  rfl

/-- Finite Cauchy--Schwarz for complex sums. -/
theorem norm_finset_sum_sq_le_card_mul {ι : Type*}
    (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ (2 : ℕ) ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ (2 : ℕ) := by
  have hnorm : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le s f
  have hsq : ‖∑ i ∈ s, f i‖ ^ (2 : ℕ) ≤
      (∑ i ∈ s, ‖f i‖) ^ (2 : ℕ) := by
    nlinarith [norm_nonneg (∑ i ∈ s, f i),
      Finset.sum_nonneg (s := s) (fun i _ ↦ norm_nonneg (f i))]
  exact hsq.trans
    (sq_sum_le_card_mul_sum_sq (s := s) (f := fun i ↦ ‖f i‖))

/-- Pointwise, the squared norm of the actual fifth power costs at most
five times the sum of the squared norms of its dyadic blocks. -/
theorem norm_real_dirichletPolynomial_fifth_sq_le_five_blocks
    {b : ℕ → ℝ} {S : Finset ℕ} {M : ℝ} (hM : 0 < M)
    (hS : ∀ n ∈ S, InDyadicRange M n) (s : ℂ) :
    ‖dirichletPolynomial (fun n ↦ (b n : ℂ)) S s ^ (5 : ℕ)‖ ^
        (2 : ℕ) ≤
      5 * ∑ j ∈ Finset.range 5,
        ‖dyadicDirichletPolynomial
          (fun n ↦ (realPowerConvolutionCoefficient b S 5 n : ℂ))
          ((2 : ℝ) ^ j * M ^ (5 : ℕ)) s‖ ^ (2 : ℕ) := by
  rw [real_dirichletPolynomial_fifth_eq_sum_dyadicBlocks hM hS]
  simpa using norm_finset_sum_sq_le_card_mul (Finset.range 5)
    (fun j ↦ dyadicDirichletPolynomial
      (fun n ↦ (realPowerConvolutionCoefficient b S 5 n : ℂ))
      ((2 : ℝ) ^ j * M ^ (5 : ℕ)) s)

/-- The continuous fifth-power mean value is reduced to the five literal
dyadic mean values accepted by MT23 Lemma 3.4. -/
theorem integral_real_dirichletPolynomial_fifth_le_five_blocks
    {b : ℕ → ℝ} {S Q : Finset ℕ} {q : ℕ → ℂ}
    {M T : ℝ} (hM : 0 < M)
    (hS : ∀ n ∈ S, InDyadicRange M n) (hQzero : 0 ∉ Q) :
    (∫ t in Set.Icc (-T) T,
        ‖dirichletPolynomial q Q (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖dirichletPolynomial (fun n ↦ (b n : ℂ)) S
            (onePlusIT t) ^ (5 : ℕ)‖ ^ (2 : ℕ)) ≤
      5 * ∑ j ∈ Finset.range 5,
        ∫ t in Set.Icc (-T) T,
          ‖dirichletPolynomial q Q (onePlusIT t)‖ ^ (2 : ℕ) *
            ‖dyadicDirichletPolynomial
              (fun n ↦
                (realPowerConvolutionCoefficient b S 5 n : ℂ))
              ((2 : ℝ) ^ j * M ^ (5 : ℕ))
              (onePlusIT t)‖ ^ (2 : ℕ) := by
  let qpoly : ℝ → ℂ := fun t ↦
    dirichletPolynomial q Q (onePlusIT t)
  let base : ℝ → ℂ := fun t ↦
    dirichletPolynomial (fun n ↦ (b n : ℂ)) S (onePlusIT t)
  let block : ℕ → ℝ → ℂ := fun j t ↦
    dyadicDirichletPolynomial
      (fun n ↦ (realPowerConvolutionCoefficient b S 5 n : ℂ))
      ((2 : ℝ) ^ j * M ^ (5 : ℕ)) (onePlusIT t)
  have hSzero : 0 ∉ S := by
    intro hzero
    have hz := hS 0 hzero
    norm_num [InDyadicRange] at hz
    linarith
  have hqcont : Continuous qpoly :=
    continuous_dirichletPolynomial_onePlusIT_of_zero_not_mem q Q hQzero
  have hbasecont : Continuous base :=
    continuous_dirichletPolynomial_onePlusIT_of_zero_not_mem
      (fun n ↦ (b n : ℂ)) S hSzero
  have hblockcont : ∀ j : ℕ, Continuous (block j) := by
    intro j
    have hscale : 0 ≤ (2 : ℝ) ^ j * M ^ (5 : ℕ) := by positivity
    have hzero : 0 ∉
        dyadicInterval ((2 : ℝ) ^ j * M ^ (5 : ℕ)) := by
      intro hz
      have hzrange := (mem_dyadicInterval hscale).mp hz
      norm_num [InDyadicRange] at hzrange
      linarith [hzrange.1]
    exact continuous_dirichletPolynomial_onePlusIT_of_zero_not_mem
      (fun n ↦ (realPowerConvolutionCoefficient b S 5 n : ℂ))
      (dyadicInterval ((2 : ℝ) ^ j * M ^ (5 : ℕ))) hzero
  let wholeWeight : ℝ → ℝ := fun t ↦
    ‖qpoly t‖ ^ (2 : ℕ) * ‖base t ^ (5 : ℕ)‖ ^ (2 : ℕ)
  let blockWeight : ℕ → ℝ → ℝ := fun j t ↦
    ‖qpoly t‖ ^ (2 : ℕ) * ‖block j t‖ ^ (2 : ℕ)
  have hwholeInt : IntegrableOn wholeWeight (Set.Icc (-T) T) := by
    apply Continuous.integrableOn_Icc
    dsimp [wholeWeight]
    exact (hqcont.norm.pow 2).mul ((hbasecont.pow 5).norm.pow 2)
  have hblockInt : ∀ j ∈ Finset.range 5,
      IntegrableOn (blockWeight j) (Set.Icc (-T) T) := by
    intro j hj
    apply Continuous.integrableOn_Icc
    dsimp [blockWeight]
    exact (hqcont.norm.pow 2).mul ((hblockcont j).norm.pow 2)
  have hsumInt : IntegrableOn
      (fun t ↦ 5 * ∑ j ∈ Finset.range 5, blockWeight j t)
      (Set.Icc (-T) T) := by
    apply Integrable.const_mul
    exact integrable_finsetSum (Finset.range 5)
      (fun j hj ↦ hblockInt j hj)
  have hmono : (∫ t in Set.Icc (-T) T, wholeWeight t) ≤
      ∫ t in Set.Icc (-T) T,
        5 * ∑ j ∈ Finset.range 5, blockWeight j t := by
    apply setIntegral_mono_on hwholeInt hsumInt measurableSet_Icc
    intro t ht
    have hp := norm_real_dirichletPolynomial_fifth_sq_le_five_blocks
      (b := b) (S := S) (M := M) hM hS (onePlusIT t)
    dsimp [wholeWeight, blockWeight, qpoly, base, block] at *
    calc
      ‖dirichletPolynomial q Q (onePlusIT t)‖ ^ (2 : ℕ) *
            ‖dirichletPolynomial (fun n ↦ (b n : ℂ)) S
              (onePlusIT t) ^ (5 : ℕ)‖ ^ (2 : ℕ)
          ≤ ‖dirichletPolynomial q Q (onePlusIT t)‖ ^ (2 : ℕ) *
              (5 * ∑ j ∈ Finset.range 5,
                ‖dyadicDirichletPolynomial
                  (fun n ↦ (realPowerConvolutionCoefficient b S 5 n : ℂ))
                  ((2 : ℝ) ^ j * M ^ (5 : ℕ))
                  (onePlusIT t)‖ ^ (2 : ℕ)) :=
            mul_le_mul_of_nonneg_left hp (sq_nonneg _)
      _ = 5 * ∑ j ∈ Finset.range 5,
            ‖dirichletPolynomial q Q (onePlusIT t)‖ ^ (2 : ℕ) *
              ‖dyadicDirichletPolynomial
                (fun n ↦ (realPowerConvolutionCoefficient b S 5 n : ℂ))
                ((2 : ℝ) ^ j * M ^ (5 : ℕ))
                (onePlusIT t)‖ ^ (2 : ℕ) := by
          calc
            _ = 5 * (‖dirichletPolynomial q Q (onePlusIT t)‖ ^ (2 : ℕ) *
                ∑ j ∈ Finset.range 5,
                  ‖dyadicDirichletPolynomial
                    (fun n ↦ (realPowerConvolutionCoefficient b S 5 n : ℂ))
                    ((2 : ℝ) ^ j * M ^ (5 : ℕ))
                    (onePlusIT t)‖ ^ (2 : ℕ)) := by ring
            _ = _ := by rw [Finset.mul_sum]
  dsimp [wholeWeight, blockWeight, qpoly, base, block] at hmono ⊢
  calc
    _ ≤ ∫ t in Set.Icc (-T) T,
        5 * ∑ j ∈ Finset.range 5,
          (‖dirichletPolynomial q Q (onePlusIT t)‖ ^ (2 : ℕ) *
            ‖dyadicDirichletPolynomial
              (fun n ↦ (realPowerConvolutionCoefficient b S 5 n : ℂ))
              ((2 : ℝ) ^ j * M ^ (5 : ℕ))
              (onePlusIT t)‖ ^ (2 : ℕ)) := hmono
    _ = _ := by
      rw [integral_const_mul]
      rw [integral_finsetSum]
      intro j hj
      exact hblockInt j hj

/-- Any five bounds supplied by the cited sparse theorem can now be inserted
block by block with only the fixed factor five. -/
theorem integral_real_fifth_le_of_dyadicBlock_bounds
    {b : ℕ → ℝ} {S Q : Finset ℕ} {q : ℕ → ℂ}
    {M T : ℝ} (hM : 0 < M)
    (hS : ∀ n ∈ S, InDyadicRange M n) (hQzero : 0 ∉ Q)
    (B : ℕ → ℝ)
    (hblock : ∀ j ∈ Finset.range 5,
      (∫ t in Set.Icc (-T) T,
          ‖dirichletPolynomial q Q (onePlusIT t)‖ ^ (2 : ℕ) *
            ‖dyadicDirichletPolynomial
              (fun n ↦
                (realPowerConvolutionCoefficient b S 5 n : ℂ))
              ((2 : ℝ) ^ j * M ^ (5 : ℕ))
              (onePlusIT t)‖ ^ (2 : ℕ)) ≤ B j) :
    (∫ t in Set.Icc (-T) T,
        ‖dirichletPolynomial q Q (onePlusIT t)‖ ^ (2 : ℕ) *
          ‖dirichletPolynomial (fun n ↦ (b n : ℂ)) S
            (onePlusIT t) ^ (5 : ℕ)‖ ^ (2 : ℕ)) ≤
      5 * ∑ j ∈ Finset.range 5, B j := by
  refine (integral_real_dirichletPolynomial_fifth_le_five_blocks
    (b := b) (S := S) (Q := Q) (q := q) (M := M) (T := T)
    hM hS hQzero).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun j hj ↦ hblock j hj) (by norm_num)

/-- One-call second-branch mean-value theorem.  The base polynomial is
required to have real coefficients; no nonnegativity is needed.  The
constant `C` depends only on `eta`, while the divisor-subpower constant `D`
depends only on the displayed divisor exponent `B` and `rho`. -/
theorem secondBranch_fifthPower_integral
    (inputs : ExternalInputs) {eta rho : ℝ}
    (heta : 0 < eta) (hrho : 0 < rho) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 ≤ B →
      ∃ D : ℝ, 1 ≤ D ∧
        ∀ (T sparseScale baseScale A₀ : ℝ)
          (sparseSupport baseSupport : Finset ℕ)
          (epsilon : ℕ → ℂ) (b : ℕ → ℝ),
          0 < baseScale →
          IsDivisorBoundedByConstant B A₀ (fun n ↦ (b n : ℂ)) →
          (∀ n ∈ baseSupport, InDyadicRange baseScale n) →
          1 ≤ sparseScale → sparseScale ≤ T →
          (∀ m ∈ sparseSupport,
            sparseScale ≤ (m : ℝ) ∧ (m : ℝ) ≤ T) →
          (∀ m ∈ sparseSupport, ‖epsilon m‖ ≤ 1) →
          (∀ j ∈ Finset.range 5,
            2 ≤ (2 : ℝ) ^ j * baseScale ^ (5 : ℕ)) →
          (∀ j ∈ Finset.range 5,
            (2 : ℝ) ^ j * baseScale ^ (5 : ℕ) ≥
                T ^ (2 / 3 : ℝ) ∨
              (sparseSupport.card : ℝ) ≤ T ^ (1 / 3 : ℝ)) →
          (∫ t in Set.Icc (-T) T,
              ‖dirichletPolynomial epsilon sparseSupport (onePlusIT t)‖ ^
                  (2 : ℕ) *
                ‖dirichletPolynomial (fun n ↦ (b n : ℂ)) baseSupport
                  (onePlusIT t) ^ (5 : ℕ)‖ ^ (2 : ℕ)) ≤
            5 * ∑ j ∈ Finset.range 5,
              C *
                ((((sparseSupport.card : ℝ) / sparseScale) ^ (2 : ℕ) +
                  (((2 : ℝ) ^ j * baseScale ^ (5 : ℕ)) * T) ^ eta *
                    ((sparseSupport.card : ℝ) * T /
                      (sparseScale ^ (2 : ℕ) *
                        ((2 : ℝ) ^ j * baseScale ^ (5 : ℕ))))) *
                  (A₀ ^ (5 : ℕ) * D *
                    (2 * ((2 : ℝ) ^ j * baseScale ^ (5 : ℕ))) ^ rho) ^
                      (2 : ℕ)) := by
  obtain ⟨C, hC, hsource⟩ :=
    inputs.matomakiTeravainenLemmaThreeFour eta heta
  refine ⟨C, hC, ?_⟩
  intro B hB
  have hE : 0 ≤ 5 * B + 4 := by nlinarith
  obtain ⟨D, hD, hDpoint⟩ :=
    Hybrid.globalDivisorSubpower (5 * B + 4) rho hE hrho
  refine ⟨D, hD, ?_⟩
  intro T sparseScale baseScale A₀ sparseSupport baseSupport epsilon b
    hbaseScale hb hbaseSupport hsparseScale hsparseT hsparseSupport hepsilon
    hlength hdelete
  have hT : 0 < T := lt_of_lt_of_le
    (zero_lt_one.trans_le hsparseScale) hsparseT
  have hsparseZero : 0 ∉ sparseSupport := by
    intro hzero
    have hm := hsparseSupport 0 hzero
    norm_num at hm
    linarith
  let coeff : ℕ → ℝ :=
    realPowerConvolutionCoefficient b baseSupport 5
  let N : ℕ → ℝ := fun j ↦
    (2 : ℝ) ^ j * baseScale ^ (5 : ℕ)
  let K : ℕ → ℝ := fun j ↦
    A₀ ^ (5 : ℕ) * D * (2 * N j) ^ rho
  let bound : ℕ → ℝ := fun j ↦
    C *
      ((((sparseSupport.card : ℝ) / sparseScale) ^ (2 : ℕ) +
        (N j * T) ^ eta *
          ((sparseSupport.card : ℝ) * T /
            (sparseScale ^ (2 : ℕ) * N j))) *
        (K j) ^ (2 : ℕ))
  have hblock : ∀ j ∈ Finset.range 5,
      (∫ t in Set.Icc (-T) T,
          ‖dirichletPolynomial epsilon sparseSupport (onePlusIT t)‖ ^
              (2 : ℕ) *
            ‖dyadicDirichletPolynomial (fun n ↦ (coeff n : ℂ))
              (N j) (onePlusIT t)‖ ^ (2 : ℕ)) ≤ bound j := by
    intro j hj
    have hN : 2 ≤ N j := hlength j hj
    have hsourceJ := (hsource T sparseScale (N j) sparseSupport epsilon coeff
      hsparseScale hsparseT hN hsparseSupport hepsilon).2 (hdelete j hj)
    have hN0 : 0 ≤ N j := by linarith
    have hA₀pow : 0 ≤ A₀ ^ (5 : ℕ) := pow_nonneg hb.2.1.le _
    have hD0 : 0 ≤ D := le_trans zero_le_one hD
    have hsup : dyadicRealCoefficientSup coeff (N j) ≤ K j := by
      apply dyadicRealCoefficientSup_le
      · dsimp [K]
        exact mul_nonneg (mul_nonneg hA₀pow hD0)
          (Real.rpow_nonneg (by positivity) rho)
      intro n hn
      have hnrange := (mem_dyadicInterval hN0).mp hn
      have hnpos : 0 < n := by
        have : (0 : ℝ) < n := lt_of_le_of_lt hN0 hnrange.1
        exact_mod_cast this
      have hcoeff := realFifthPowerCoefficient_divisorBound
        (S := baseSupport) hnpos hb
      have hdiv := hDpoint n hnpos
      have hnpow : (n : ℝ) ^ rho ≤ (2 * N j) ^ rho :=
        Real.rpow_le_rpow (Nat.cast_nonneg n) hnrange.2 hrho.le
      dsimp [coeff, K]
      calc
        |realPowerConvolutionCoefficient b baseSupport 5 n| ≤
            A₀ ^ (5 : ℕ) *
              (divisorCount n : ℝ) ^ (5 * B + 4) := hcoeff
        _ ≤ A₀ ^ (5 : ℕ) * (D * (n : ℝ) ^ rho) :=
          mul_le_mul_of_nonneg_left hdiv hA₀pow
        _ ≤ A₀ ^ (5 : ℕ) * (D * (2 * N j) ^ rho) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hnpow hD0) hA₀pow
        _ = A₀ ^ (5 : ℕ) * D * (2 * N j) ^ rho := by ring
    have hsupSq :
        (dyadicRealCoefficientSup coeff (N j)) ^ (2 : ℕ) ≤
          (K j) ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ (by
        unfold dyadicRealCoefficientSup
        exact NNReal.coe_nonneg _) hsup 2
    have hprefactor : 0 ≤ C *
        (((sparseSupport.card : ℝ) / sparseScale) ^ (2 : ℕ) +
          (N j * T) ^ eta *
            ((sparseSupport.card : ℝ) * T /
              (sparseScale ^ (2 : ℕ) * N j))) := by
      have hsparsePos : 0 < sparseScale := zero_lt_one.trans_le hsparseScale
      have hNpos : 0 < N j := lt_of_lt_of_le (by norm_num) hN
      positivity
    exact hsourceJ.trans (by
      dsimp [bound]
      convert mul_le_mul_of_nonneg_left hsupSq hprefactor using 1
      ring)
  have hmain := integral_real_fifth_le_of_dyadicBlock_bounds
    (b := b) (S := baseSupport) (Q := sparseSupport) (q := epsilon)
    (M := baseScale) (T := T) hbaseScale hbaseSupport hsparseZero bound hblock
  simpa [coeff, N, K, bound] using hmain

/-- Fully assembled measurable-set theorem for the second sparse branch.
It consumes the actual fifth power (not a preselected block), applies the
cited MT23/Heath--Brown estimate to all five dyadic output blocks, and
inserts the locally proved uniform coefficient-supremum bound.  The only
shape restriction is that the base coefficients are real; they may have
either sign. -/
theorem secondBranch_fifthPower_largeValueMeasure
    (inputs : ExternalInputs) {eta rho : ℝ}
    (heta : 0 < eta) (hrho : 0 < rho) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 0 ≤ B →
      ∃ D : ℝ, 1 ≤ D ∧
        ∀ (T sparseScale baseScale A₀ : ℝ)
          (sparseSupport baseSupport : Finset ℕ)
          (epsilon : ℕ → ℂ) (b : ℕ → ℝ)
          (E : Set ℝ) (L : ℝ),
          0 < baseScale →
          IsDivisorBoundedByConstant B A₀ (fun n ↦ (b n : ℂ)) →
          (∀ n ∈ baseSupport, InDyadicRange baseScale n) →
          1 ≤ sparseScale → sparseScale ≤ T →
          (∀ m ∈ sparseSupport,
            sparseScale ≤ (m : ℝ) ∧ (m : ℝ) ≤ T) →
          (∀ m ∈ sparseSupport, ‖epsilon m‖ ≤ 1) →
          (∀ j ∈ Finset.range 5,
            2 ≤ (2 : ℝ) ^ j * baseScale ^ (5 : ℕ)) →
          (∀ j ∈ Finset.range 5,
            (2 : ℝ) ^ j * baseScale ^ (5 : ℕ) ≥
                T ^ (2 / 3 : ℝ) ∨
              (sparseSupport.card : ℝ) ≤ T ^ (1 / 3 : ℝ)) →
          MeasurableSet E → E ⊆ Set.Icc (-T) T → 0 ≤ L →
          (∀ t ∈ E, L ≤
            ‖dirichletPolynomial epsilon sparseSupport (onePlusIT t)‖ ^
                (2 : ℕ) *
              ‖dirichletPolynomial (fun n ↦ (b n : ℂ)) baseSupport
                (onePlusIT t) ^ (5 : ℕ)‖ ^ (2 : ℕ)) →
          volume.real E * L ≤
            5 * ∑ j ∈ Finset.range 5,
              C *
                ((((sparseSupport.card : ℝ) / sparseScale) ^ (2 : ℕ) +
                  (((2 : ℝ) ^ j * baseScale ^ (5 : ℕ)) * T) ^ eta *
                    ((sparseSupport.card : ℝ) * T /
                      (sparseScale ^ (2 : ℕ) *
                        ((2 : ℝ) ^ j * baseScale ^ (5 : ℕ))))) *
                  (A₀ ^ (5 : ℕ) * D *
                    (2 * ((2 : ℝ) ^ j * baseScale ^ (5 : ℕ))) ^ rho) ^
                      (2 : ℕ)) := by
  obtain ⟨C, hC, hCmain⟩ :=
    secondBranch_fifthPower_integral inputs heta hrho
  refine ⟨C, hC, ?_⟩
  intro B hB
  obtain ⟨D, hD, hDmain⟩ := hCmain B hB
  refine ⟨D, hD, ?_⟩
  intro T sparseScale baseScale A₀ sparseSupport baseSupport epsilon b E L
    hbaseScale hb hbaseSupport hsparseScale hsparseT hsparseSupport hepsilon
    hlength hdelete hEmeas hEsub hL hlower
  have hIntegral := hDmain T sparseScale baseScale A₀ sparseSupport
    baseSupport epsilon b hbaseScale hb hbaseSupport hsparseScale hsparseT
    hsparseSupport hepsilon hlength hdelete
  have hsparseZero : 0 ∉ sparseSupport := by
    intro hzero
    have hm := hsparseSupport 0 hzero
    norm_num at hm
    linarith
  have hbaseZero : 0 ∉ baseSupport := by
    intro hzero
    have hm := hbaseSupport 0 hzero
    norm_num [InDyadicRange] at hm
    linarith
  have hqcont : Continuous (fun t : ℝ ↦
      dirichletPolynomial epsilon sparseSupport (onePlusIT t)) :=
    continuous_dirichletPolynomial_onePlusIT_of_zero_not_mem
      epsilon sparseSupport hsparseZero
  have hbasecont : Continuous (fun t : ℝ ↦
      dirichletPolynomial (fun n ↦ (b n : ℂ)) baseSupport
        (onePlusIT t)) :=
    continuous_dirichletPolynomial_onePlusIT_of_zero_not_mem
      (fun n ↦ (b n : ℂ)) baseSupport hbaseZero
  let f : ℝ → ℝ := fun t ↦
    ‖dirichletPolynomial epsilon sparseSupport (onePlusIT t)‖ ^
        (2 : ℕ) *
      ‖dirichletPolynomial (fun n ↦ (b n : ℂ)) baseSupport
        (onePlusIT t) ^ (5 : ℕ)‖ ^ (2 : ℕ)
  have hfcont : Continuous f := by
    dsimp [f]
    exact (hqcont.norm.pow 2).mul ((hbasecont.pow 5).norm.pow 2)
  have hfIcc : IntegrableOn f (Set.Icc (-T) T) :=
    hfcont.integrableOn_Icc
  have hfE : IntegrableOn f E := hfIcc.mono_set hEsub
  have hconstE : IntegrableOn (fun _ : ℝ ↦ L) E :=
    continuous_const.integrableOn_Icc.mono_set hEsub
  have hlowerInt : (∫ t in E, L) ≤ ∫ t in E, f t := by
    exact setIntegral_mono_on hconstE hfE hEmeas (by
      intro t ht
      exact hlower t ht)
  have hsubsetInt : (∫ t in E, f t) ≤
      ∫ t in Set.Icc (-T) T, f t := by
    apply setIntegral_mono_set hfIcc
    · filter_upwards [] with t
      dsimp [f]
      positivity
    · filter_upwards [] with t ht
      exact hEsub ht
  calc
    volume.real E * L = ∫ _t in E, L := by
      rw [setIntegral_const]
      simp
    _ ≤ ∫ t in E, f t := hlowerInt
    _ ≤ ∫ t in Set.Icc (-T) T, f t := hsubsetInt
    _ ≤ _ := by simpa [f] using hIntegral

/-! ## Exact exponent model for the tenth-moment condition -/

/-- The exponent appearing on the right of the paper's key inequality. -/
def secondBranchKeyExponent (θ σ₁ σ₂ : ℝ) : ℝ :=
  (5 - 8 * σ₁) * θ + 2 * σ₂ * (1 - θ)

/-- Under the exact power model `M₁=X^θ`, `M₂=X^(1-θ)`, the product in
the sufficient tenth-moment condition is precisely a single power of `X`.
The paper subsequently spends a small epsilon margin to absorb the
polylogarithmic discrepancy in `M₁M₂=X(log X)^{O(1)}`. -/
theorem secondBranch_power_identity {X θ σ₁ σ₂ : ℝ} (hX : 0 < X) :
    (X ^ θ) ^ (5 - 8 * σ₁) *
        (X ^ (1 - θ)) ^ (2 * σ₂) =
      X ^ secondBranchKeyExponent θ σ₁ σ₂ := by
  rw [← Real.rpow_mul hX.le, ← Real.rpow_mul hX.le,
    secondBranchKeyExponent]
  rw [mul_comm θ (5 - 8 * σ₁),
    mul_comm (1 - θ) (2 * σ₂), Real.rpow_add hX]

/-- The displayed exponent inequality is sufficient for the exact-model
tenth-moment inequality. -/
theorem secondBranch_keyExponent_suffices
    {X a ε θ σ₁ σ₂ : ℝ} (hX : 1 < X)
    (hkey : 1 / a + 4 * ε ≤ secondBranchKeyExponent θ σ₁ σ₂) :
    X ^ (1 / a + 4 * ε) ≤
      (X ^ θ) ^ (5 - 8 * σ₁) *
        (X ^ (1 - θ)) ^ (2 * σ₂) := by
  rw [secondBranch_power_identity (lt_trans zero_lt_one hX)]
  exact Real.rpow_le_rpow_of_exponent_le hX.le hkey

/-- Conversely, in the exact power model and for `X>1`, the sufficient
product inequality is equivalent to the key exponent inequality. -/
theorem secondBranch_product_inequality_iff
    {X a ε θ σ₁ σ₂ : ℝ} (hX : 1 < X) :
    X ^ (1 / a + 4 * ε) ≤
        (X ^ θ) ^ (5 - 8 * σ₁) *
          (X ^ (1 - θ)) ^ (2 * σ₂) ↔
      1 / a + 4 * ε ≤ secondBranchKeyExponent θ σ₁ σ₂ := by
  rw [secondBranch_power_identity (lt_trans zero_lt_one hX)]
  exact Real.rpow_le_rpow_left_iff hX

def secondBranchModule : ProofModule :=
  { name := "Sparse.SecondBranch"
    paperLocation := "Section 6.1, application with A(s) = M₁(s)^5"
    purpose :=
      "Collect the real fifth power into exactly five dyadic blocks, propagate the repaired 5B+4 divisor exponent, instantiate the cited sparse mean-value theorem uniformly on every block, recombine the measurable-set estimate, and verify the exact exponent conversion. Global X-parameter substitution belongs to Propagation."
    dependsOn :=
      [ "Sparse.ResidualRange",
        "Sparse.PrimePowerPolynomial",
        "TypeII.PoweredPolynomial",
        "Hybrid.HybridDensity.globalDivisorSubpower",
        "Assumptions.matomakiTeravainenLemmaThreeFour" ]
    status := .proved }

end

end Sparse
end ExactSemiprimes
