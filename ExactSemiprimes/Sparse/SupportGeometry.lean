import ExactSemiprimes.Sparse.SmoothSupport
import ExactSemiprimes.Sparse.QLowerBound

/-!
# Geometry of the sparse prime-power support

This module connects the finite support of the normalized prime power with
the smooth-number counting function.  It supplies the deterministic bridge
needed before the Hildebrand--Tenenbaum input can be used in either sparse
Heath--Brown branch.
-/

namespace ExactSemiprimes
namespace Sparse

open Filter
open scoped BigOperators

noncomputable section

/-- A tuple of primes has positive product, including the empty tuple whose
product is one. -/
theorem primeTupleProduct_pos {S : Finset ℕ} {k : ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (f : PrimeTuple S k) :
    0 < primeTupleProduct f := by
  apply Finset.prod_pos
  intro i _hi
  exact (hS (f i) (f i).property).pos

/-- If every permitted prime is at most `Y`, every `k`-fold tuple product
is at most `Y^k`. -/
theorem primeTupleProduct_le_pow {S : Finset ℕ} {k Y : ℕ}
    (hS : ∀ p ∈ S, p ≤ Y) (f : PrimeTuple S k) :
    primeTupleProduct f ≤ Y ^ k := by
  calc
    primeTupleProduct f = ∏ i : Fin k, (f i : ℕ) := rfl
    _ ≤ ∏ _i : Fin k, Y := by
      apply Finset.prod_le_prod
      intro i _hi
      exact hS (f i) (f i).property
    _ = Y ^ k := by simp

/-- The greatest prime factor of a tuple product is bounded by the common
upper bound for the tuple entries. -/
theorem maxPrimeFac_primeTupleProduct_le {S : Finset ℕ} {k Y : ℕ}
    (hY : 1 ≤ Y) (hPrime : ∀ p ∈ S, Nat.Prime p)
    (hBound : ∀ p ∈ S, p ≤ Y) (f : PrimeTuple S k) :
    (primeTupleProduct f).maxPrimeFac ≤ Y := by
  by_cases hone : primeTupleProduct f = 1
  · simp [hone, hY]
  · have hpos := primeTupleProduct_pos hPrime f
    have hgt : 1 < primeTupleProduct f := by omega
    rw [Nat.maxPrimeFac_le_iff hgt]
    intro q hq hqdiv
    have hqprod : q ∣ ∏ i : Fin k, (f i : ℕ) := by
      simpa only [primeTupleProduct] using hqdiv
    obtain ⟨i, _hi, hqfi⟩ :=
      (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hq)
        (fun i : Fin k ↦ (f i : ℕ))).mp hqprod
    have heq : q = (f i : ℕ) :=
      (Nat.prime_dvd_prime_iff_eq hq
        (hPrime (f i) (f i).property)).mp hqfi
    rw [heq]
    exact hBound (f i) (f i).property

/-- The complete finite support is contained in the corresponding set of
`Y`-smooth positive integers up to `X`. -/
theorem primePowerSupport_subset_smoothNumbers
    {S : Finset ℕ} {k X Y : ℕ}
    (hY : 1 ≤ Y) (hPrime : ∀ p ∈ S, Nat.Prime p)
    (hBound : ∀ p ∈ S, p ≤ Y) (hPower : Y ^ k ≤ X) :
    primePowerSupport S k ⊆
      (Finset.Icc 1 X).filter fun n ↦ n.maxPrimeFac ≤ Y := by
  intro n hn
  obtain ⟨f, hf⟩ := mem_primePowerSupport.mp hn
  have hpos := primeTupleProduct_pos hPrime f
  have hnpos : 1 ≤ n := by
    rw [← hf]
    omega
  have hnupper : n ≤ X := by
    rw [← hf]
    exact (primeTupleProduct_le_pow hBound f).trans hPower
  have hsmooth : n.maxPrimeFac ≤ Y := by
    rw [← hf]
    exact maxPrimeFac_primeTupleProduct_le hY hPrime hBound f
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hnpos, hnupper⟩,
    hsmooth⟩

/-- Consequently the sparse support cardinality is at most the standard
smooth-number count. -/
theorem card_primePowerSupport_le_smoothNumberCount
    {S : Finset ℕ} {k X Y : ℕ}
    (hY : 1 ≤ Y) (hPrime : ∀ p ∈ S, Nat.Prime p)
    (hBound : ∀ p ∈ S, p ≤ Y) (hPower : Y ^ k ≤ X) :
    (primePowerSupport S k).card ≤ smoothNumberCount X Y := by
  exact Finset.card_le_card
    (primePowerSupport_subset_smoothNumbers hY hPrime hBound hPower)

/-- Specialization to the paper's dyadic prime set.  The only remaining
size hypothesis is the transparent natural inequality saying that the
largest permitted prime, raised to the chosen order, does not exceed `X`. -/
theorem card_dyadicPrimePowerSupport_le_smoothNumberCount
    {P : ℝ} {k X : ℕ} (hP : 0 ≤ P)
    (hY : 1 ≤ ⌊2 * P⌋₊) (hPower : ⌊2 * P⌋₊ ^ k ≤ X) :
    (primePowerSupport (dyadicPrimes P) k).card ≤
      smoothNumberCount X ⌊2 * P⌋₊ := by
  apply card_primePowerSupport_le_smoothNumberCount hY
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p hp
    have hpRange : InDyadicRange P p :=
      (mem_dyadicInterval hP).mp (Finset.mem_filter.mp hp).1
    exact (Nat.le_floor_iff (by positivity : 0 ≤ 2 * P)).2 hpRange.2
  · exact hPower

/-- The smooth-number count is monotone in its smoothness cutoff. -/
theorem smoothNumberCount_mono_right {X Y Z : ℕ} (hYZ : Y ≤ Z) :
    smoothNumberCount X Y ≤ smoothNumberCount X Z := by
  apply Finset.card_le_card
  intro n hn
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hn).1,
      (Finset.mem_filter.mp hn).2.trans hYZ⟩

/-- The factor two in the dyadic prime support is absorbed by an arbitrarily
small increase of the logarithmic smoothness exponent. -/
theorem eventually_two_mul_log_rpow_le_log_rpow_add
    (a : ℝ) {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ X : ℝ in atTop,
      2 * (Real.log X) ^ a ≤ (Real.log X) ^ (a + delta) := by
  have hgrowth : Tendsto (fun X : ℝ ↦ (Real.log X) ^ delta) atTop atTop :=
    (tendsto_rpow_atTop hdelta).comp Real.tendsto_log_atTop
  have htwo : ∀ᶠ X : ℝ in atTop, 2 ≤ (Real.log X) ^ delta :=
    hgrowth.eventually_ge_atTop 2
  filter_upwards [htwo, eventually_gt_atTop (1 : ℝ)] with X htwoX hX
  have hlog : 0 < Real.log X := Real.log_pos hX
  calc
    2 * (Real.log X) ^ a ≤
        (Real.log X) ^ delta * (Real.log X) ^ a :=
      mul_le_mul_of_nonneg_right htwoX (Real.rpow_nonneg hlog.le _)
    _ = (Real.log X) ^ (a + delta) := by
      rw [add_comm, Real.rpow_add hlog]

/-- Natural floors preserve the preceding eventual cutoff comparison. -/
theorem eventually_floor_two_mul_log_rpow_le_floor_log_rpow_add
    (a : ℝ) {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ X : ℝ in atTop,
      ⌊2 * (Real.log X) ^ a⌋₊ ≤
        ⌊(Real.log X) ^ (a + delta)⌋₊ := by
  filter_upwards [eventually_two_mul_log_rpow_le_log_rpow_add a hdelta] with
      X hX
  exact Nat.floor_mono hX

/-- Every integer in the dyadic prime-power support lies between the nominal
lower scale `M=P^k` and any natural upper scale that dominates
`floor (2P)^k`. -/
theorem dyadicPrimePowerSupport_range
    {P M : ℝ} {k X : ℕ}
    (hP : 0 ≤ P) (hM : M = P ^ k)
    (hPower : ⌊2 * P⌋₊ ^ k ≤ X) :
    ∀ n ∈ primePowerSupport (dyadicPrimes P) k,
      M ≤ (n : ℝ) ∧ (n : ℝ) ≤ X := by
  intro n hn
  obtain ⟨f, rfl⟩ := mem_primePowerSupport.mp hn
  have hlower : P ^ k ≤ (primeTupleProduct f : ℝ) := by
    rw [show P ^ k = ∏ _i : Fin k, P by simp [Finset.prod_const]]
    rw [primeTupleProduct, Nat.cast_prod]
    apply Finset.prod_le_prod₀
    · intro i _hi
      exact hP
    · intro i _hi
      have hmem := (f i).property
      have hrange : InDyadicRange P (f i : ℕ) :=
        (mem_dyadicInterval hP).mp (Finset.mem_filter.mp hmem).1
      exact hrange.1.le
  constructor
  · simpa [hM] using hlower
  · exact_mod_cast
      (primeTupleProduct_le_pow
        (fun p hp ↦ by
          have hrange : InDyadicRange P p :=
            (mem_dyadicInterval hP).mp (Finset.mem_filter.mp hp).1
          exact (Nat.le_floor_iff (by positivity : 0 ≤ 2 * P)).2 hrange.2)
        f).trans hPower

/-- For the paper's floor choice of `k`, the entire `k`-fold dyadic support
lies below `X`; this is the exact floor arithmetic behind that assertion. -/
theorem floor_two_mul_pow_paperExponent_le
    {X : ℕ} {P : ℝ}
    (hX : 1 < (X : ℝ))
    (hP : 0 < P)
    (hden : 1 ≤ Real.log (2 * P)) :
    ⌊2 * P⌋₊ ^ (⌊Real.log (X : ℝ) / Real.log (2 * P)⌋₊ : ℕ) ≤ X := by
  let k : ℕ := ⌊Real.log (X : ℝ) / Real.log (2 * P)⌋₊
  have hbasePos : 0 < 2 * P := by positivity
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hX
  have hlogBase : 0 < Real.log (2 * P) := lt_of_lt_of_le zero_lt_one hden
  have hbaseOne : 1 ≤ 2 * P :=
    (Real.log_pos_iff hbasePos.le).mp hlogBase |>.le
  have hquotNonneg : 0 ≤ Real.log (X : ℝ) / Real.log (2 * P) :=
    div_nonneg hlogX.le hlogBase.le
  have hk : (k : ℝ) ≤ Real.log (X : ℝ) / Real.log (2 * P) := by
    exact Nat.floor_le hquotNonneg
  have hfloor : ((⌊2 * P⌋₊ : ℕ) : ℝ) ≤ 2 * P :=
    Nat.floor_le hbasePos.le
  have hpowFloor : ((⌊2 * P⌋₊ : ℕ) : ℝ) ^ k ≤ (2 * P) ^ k :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor k
  have hpowBase : (2 * P) ^ k ≤ (X : ℝ) := by
    calc
      (2 * P) ^ k = (2 * P) ^ (k : ℝ) := by rw [Real.rpow_natCast]
      _ ≤ (2 * P) ^ (Real.log (X : ℝ) / Real.log (2 * P)) :=
        Real.rpow_le_rpow_of_exponent_le hbaseOne hk
      _ = (X : ℝ) := by
        rw [Real.rpow_def_of_pos hbasePos]
        have hlogBaseNe : Real.log (2 * P) ≠ 0 := ne_of_gt hlogBase
        rw [mul_div_cancel₀ _ hlogBaseNe,
          Real.exp_log (by positivity : 0 < (X : ℝ))]
  exact_mod_cast hpowFloor.trans hpowBase

/-- A single eventual package for the sparse polynomial used in Section 6.
The fixed positive slack `delta` absorbs the factor two in the dyadic prime
window, while `eta` is the Hildebrand--Tenenbaum power slack. -/
theorem eventually_paperSparsePolynomial_package
    (hHT : HildebrandTenenbaumCorollaryOneThreeStatement)
    {a delta eta : ℝ} (ha : 1 < a) (hdelta : 0 < delta)
    (heta : 0 < eta) :
    ∀ᶠ X : ℕ in atTop,
      let P : ℝ := (Real.log (X : ℝ)) ^ a
      let k : ℕ :=
        ⌊Real.log (X : ℝ) / Real.log (2 * P)⌋₊
      let M : ℝ := P ^ k
      (∀ n : ℕ,
        primePowerCoefficient (dyadicPrimes P) k n ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ n ∈ primePowerSupport (dyadicPrimes P) k,
        M ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) ∧
      ((primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
        (X : ℝ) ^ (1 - 1 / (a + delta) + eta) ∧
      (∀ (s : ℂ) (epsilon : ℝ),
        P ^ (-epsilon / 10) ≤
            ‖primeBasePolynomial (dyadicPrimes P) s‖ →
        M ^ (-epsilon / 10 - 1 / a) ≤
            ‖primePowerPolynomial (dyadicPrimes P) k s‖) := by
  have haPos : 0 < a := lt_trans zero_lt_one ha
  have hab : 1 < a + delta := by linarith
  have hlogNat :
      Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hPtop :
      Tendsto (fun X : ℕ ↦ (Real.log (X : ℝ)) ^ a) atTop atTop :=
    (tendsto_rpow_atTop haPos).comp hlogNat
  have htwoPtop :
      Tendsto (fun X : ℕ ↦ 2 * (Real.log (X : ℝ)) ^ a) atTop atTop :=
    hPtop.const_mul_atTop (by norm_num)
  have hden : ∀ᶠ X : ℕ in atTop,
      1 ≤ Real.log (2 * (Real.log (X : ℝ)) ^ a) :=
    (Real.tendsto_log_atTop.comp htwoPtop).eventually_ge_atTop 1
  have hcutReal :=
    eventually_floor_two_mul_log_rpow_le_floor_log_rpow_add a hdelta
  have hcut : ∀ᶠ X : ℕ in atTop,
      ⌊2 * (Real.log (X : ℝ)) ^ a⌋₊ ≤
        ⌊(Real.log (X : ℝ)) ^ (a + delta)⌋₊ :=
    tendsto_natCast_atTop_atTop.eventually hcutReal
  have hsmooth := eventually_logPowerSmoothNumberCount_le_rpow
    hHT hab heta
  filter_upwards [eventually_ge_atTop (2 : ℕ), hden, hcut, hsmooth] with
      X hXNat hdenX hcutX hsmoothX
  dsimp only
  have hX : 1 < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
  let P : ℝ := (Real.log (X : ℝ)) ^ a
  let k : ℕ :=
    ⌊Real.log (X : ℝ) / Real.log (2 * P)⌋₊
  let M : ℝ := P ^ k
  have hP : 0 < P := by
    dsimp [P]
    exact Real.rpow_pos_of_pos (Real.log_pos hX) a
  have hpower : ⌊2 * P⌋₊ ^ k ≤ X := by
    exact floor_two_mul_pow_paperExponent_le hX hP
      (by simpa [P] using hdenX)
  have hY : 1 ≤ ⌊2 * P⌋₊ := by
    apply Nat.le_floor
    have hlogPos : 0 < Real.log (2 * P) :=
      lt_of_lt_of_le zero_lt_one (by simpa [P] using hdenX)
    simpa only [Nat.cast_one] using
      ((Real.log_pos_iff (by positivity : 0 ≤ 2 * P)).mp hlogPos).le
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    exact dyadic_primePowerCoefficient_mem_unitInterval P k n
  · exact dyadicPrimePowerSupport_range hP.le rfl hpower
  · have hcardNat :
        (primePowerSupport (dyadicPrimes P) k).card ≤
          logPowerSmoothNumberCount (a + delta) X := by
      calc
        (primePowerSupport (dyadicPrimes P) k).card ≤
            smoothNumberCount X ⌊2 * P⌋₊ :=
          card_dyadicPrimePowerSupport_le_smoothNumberCount hP.le hY hpower
        _ ≤ smoothNumberCount X
              ⌊(Real.log (X : ℝ)) ^ (a + delta)⌋₊ :=
          smoothNumberCount_mono_right (by simpa [P] using hcutX)
        _ = logPowerSmoothNumberCount (a + delta) X := rfl
    have hcardReal :
        ((primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
          (logPowerSmoothNumberCount (a + delta) X : ℝ) := by
      exact_mod_cast hcardNat
    exact hcardReal.trans hsmoothX
  · intro s epsilon hU
    have hq := paper_Q_lower_bound_for_floor_choice
      (z := primeBasePolynomial (dyadicPrimes P) s)
      (X := (X : ℝ)) (P := P) (M := M) (ε := epsilon) (a := a)
      hX haPos rfl (by simpa [P] using hdenX) rfl hU
    simpa [factorialNormalizedPower, primePowerPolynomial] using hq

/-- The smooth-support exponent can be returned in the paper's preferred
`1-1/a+omega` form: the cutoff slack and the Hildebrand--Tenenbaum slack are
chosen once from the requested fixed `omega`. -/
theorem eventually_card_paperSparseSupport_le
    (hHT : HildebrandTenenbaumCorollaryOneThreeStatement)
    {a omega : ℝ} (ha : 1 < a) (homega : 0 < omega) :
    ∀ᶠ X : ℕ in atTop,
      let P : ℝ := (Real.log (X : ℝ)) ^ a
      let k : ℕ :=
        ⌊Real.log (X : ℝ) / Real.log (2 * P)⌋₊
      ((primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
        (X : ℝ) ^ (1 - 1 / a + omega) := by
  let delta : ℝ := omega / 4
  let eta : ℝ := omega / 2
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hpack := eventually_paperSparsePolynomial_package
    hHT ha hdelta heta
  have haPos : 0 < a := lt_trans zero_lt_one ha
  have haDeltaPos : 0 < a + delta := add_pos haPos hdelta
  have hdenom : 1 ≤ a * (a + delta) := by
    have haOne : 1 ≤ a := ha.le
    have haDeltaOne : 1 ≤ a + delta := by linarith
    nlinarith
  have hdeltaFrac : delta / (a * (a + delta)) ≤ delta := by
    apply (div_le_iff₀ (mul_pos haPos haDeltaPos)).2
    nlinarith [mul_nonneg hdelta.le (sub_nonneg.mpr hdenom)]
  have hreciprocal :
      1 / a - 1 / (a + delta) = delta / (a * (a + delta)) := by
    field_simp [ne_of_gt haPos, ne_of_gt haDeltaPos]
    ring
  have hexponent :
      1 - 1 / (a + delta) + eta ≤ 1 - 1 / a + omega := by
    rw [show 1 - 1 / (a + delta) + eta =
        1 - 1 / a + (1 / a - 1 / (a + delta)) + eta by ring,
      hreciprocal]
    dsimp [delta, eta] at hdeltaFrac ⊢
    nlinarith
  filter_upwards [hpack, eventually_ge_atTop (1 : ℕ)] with X hpackX hX
  dsimp only at hpackX ⊢
  exact hpackX.2.2.1.trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX) hexponent)

/-- In the range `1<a<3/2` used by the paper, the actual moving sparse
support automatically satisfies the `X^(1/3)` deletion condition required
by both Heath--Brown branches.  No separate cutoff or floor hypotheses are
left in this specialization. -/
theorem eventually_card_paperSparseSupport_le_oneThird
    (hHT : HildebrandTenenbaumCorollaryOneThreeStatement)
    {a : ℝ} (ha : 1 < a) (haUpper : a < 3 / 2) :
    ∀ᶠ X : ℕ in atTop,
      let P : ℝ := (Real.log (X : ℝ)) ^ a
      let k : ℕ :=
        ⌊Real.log (X : ℝ) / Real.log (2 * P)⌋₊
      ((primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
        (X : ℝ) ^ (1 / 3 : ℝ) := by
  let omega : ℝ := (1 / a - 2 / 3) / 2
  have haPos : 0 < a := lt_trans zero_lt_one ha
  have hreciprocal : (2 : ℝ) / 3 < 1 / a := by
    apply (lt_div_iff₀ haPos).2
    nlinarith
  have homega : 0 < omega := by
    dsimp [omega]
    linarith
  have hmain := eventually_card_paperSparseSupport_le hHT ha homega
  have hexponent : 1 - 1 / a + omega ≤ (1 : ℝ) / 3 := by
    dsimp [omega]
    linarith
  filter_upwards [hmain, eventually_ge_atTop (1 : ℕ)] with X hbound hX
  dsimp only at hbound ⊢
  exact hbound.trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX) hexponent)

/-- The complete moving sparse-polynomial geometry needed by the two
Heath--Brown branches, specialized to the paper's range `1<a<3/2`.
It combines coefficient positivity, the exact support interval, the
`X^(1/3)` deletion bound, and the normalized-power lower bound in one
eventual statement. -/
theorem eventually_paperSparsePolynomial_oneThird_package
    (hHT : HildebrandTenenbaumCorollaryOneThreeStatement)
    {a : ℝ} (ha : 1 < a) (haUpper : a < 3 / 2) :
    ∀ᶠ X : ℕ in atTop,
      let P : ℝ := (Real.log (X : ℝ)) ^ a
      let k : ℕ :=
        ⌊Real.log (X : ℝ) / Real.log (2 * P)⌋₊
      let M : ℝ := P ^ k
      (∀ n : ℕ,
        primePowerCoefficient (dyadicPrimes P) k n ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ n ∈ primePowerSupport (dyadicPrimes P) k,
        M ≤ (n : ℝ) ∧ (n : ℝ) ≤ X) ∧
      ((primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
        (X : ℝ) ^ (1 / 3 : ℝ) ∧
      (∀ (s : ℂ) (epsilon : ℝ),
        P ^ (-epsilon / 10) ≤
            ‖primeBasePolynomial (dyadicPrimes P) s‖ →
        M ^ (-epsilon / 10 - 1 / a) ≤
            ‖primePowerPolynomial (dyadicPrimes P) k s‖) := by
  have hgeometry := eventually_paperSparsePolynomial_package
    hHT ha (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  have hcard :=
    eventually_card_paperSparseSupport_le_oneThird hHT ha haUpper
  filter_upwards [hgeometry, hcard] with X hgeometryX hcardX
  dsimp only at hgeometryX hcardX ⊢
  exact ⟨hgeometryX.1, hgeometryX.2.1, hcardX, hgeometryX.2.2.2⟩

/-- Metadata for the deterministic sparse-support geometry. -/
def supportGeometryModule : ProofModule :=
  { name := "Sparse.SupportGeometry"
    paperLocation := "Section 6.1, smooth-support bound"
    purpose :=
      "Place the normalized prime-power support inside an explicit smooth-number set, absorb the dyadic factor two into an arbitrarily small logarithmic exponent slack, and verify the complete moving paper-scale support and Q-lower-bound package."
    dependsOn :=
      ["Sparse.PrimePowerPolynomial", "Sparse.SmoothSupport", "Sparse.QLowerBound"]
    status := .proved }

end

end Sparse
end ExactSemiprimes
