import ExactSemiprimes.TypeII.PolynomialLengthRanges
import ExactSemiprimes.TypeII.MediumThresholdBridge

/-!
# Outer Type-II length geometry

This module packages the deterministic length choices needed outside the
discrete medium-bin theorem. It deliberately adds no analytic input.
-/

namespace ExactSemiprimes
namespace TypeII

open Filter

noncomputable section

/-- Explicit order cap for the powered medium branch. -/
def mediumPowerOrderCap (eps : ℝ) : ℕ :=
  ⌈5 / eps⌉₊

theorem one_le_mediumPowerOrderCap {eps : ℝ} (heps : 0 < eps) :
    1 ≤ mediumPowerOrderCap eps := by
  rw [mediumPowerOrderCap, Nat.one_le_iff_ne_zero]
  exact (Nat.ceil_pos.mpr (by positivity : 0 < 5 / eps)).ne'

/-- The exponent supplied by `existsPoweringExponent` is bounded by the
explicit order cap depending only on `eps`. -/
theorem exists_poweringExponent_le_mediumPowerOrderCap
    {eps theta : ℝ}
    (heps : 0 < eps) (hepsSmall : eps ≤ 2 / 121)
    (hthetaLower : eps / 5 ≤ theta)
    (hthetaUpper : theta ≤ 2 / 11 + eps) :
    ∃ ell : ℕ,
      5 ≤ ell ∧ ell ≤ mediumPowerOrderCap eps ∧
      5 / 6 - eps ≤ (ell : ℝ) * theta ∧
      (ell : ℝ) * theta ≤ 1 - eps / 2 := by
  obtain ⟨ell, hellFive, hellLower, hellUpper⟩ :=
    existsPoweringExponent heps hepsSmall hthetaLower hthetaUpper
  have hnonneg : 0 ≤ (ell : ℝ) := Nat.cast_nonneg ell
  have hscaled : (ell : ℝ) * (eps / 5) ≤ (ell : ℝ) * theta :=
    mul_le_mul_of_nonneg_left hthetaLower hnonneg
  have hellEps : (ell : ℝ) * eps ≤ 5 := by
    nlinarith
  have hellRatio : (ell : ℝ) ≤ 5 / eps := by
    exact (le_div_iff₀ heps).2 (by simpa [mul_comm] using hellEps)
  have hratioCeil : 5 / eps ≤ (mediumPowerOrderCap eps : ℝ) := by
    exact Nat.le_ceil _
  have hellCapReal : (ell : ℝ) ≤ (mediumPowerOrderCap eps : ℝ) :=
    hellRatio.trans hratioCeil
  have hellCap : ell ≤ mediumPowerOrderCap eps := by
    exact_mod_cast hellCapReal
  exact ⟨ell, hellFive, hellCap, hellLower, hellUpper⟩

/-- A single eventual cutoff absorbs the dyadic support factor for every
order below a fixed cap. -/
theorem eventually_twoPow_le_mediumMargin_uniform
    (K : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ T : ℝ in atTop, ∀ ell : ℕ, ell ≤ K →
      (2 : ℝ) ^ ell ≤ T ^ (2 * eps / 5) := by
  have hexponent : 0 < 2 * eps / 5 := by positivity
  have hK : ∀ᶠ T : ℝ in atTop,
      (2 : ℝ) ^ K ≤ T ^ (2 * eps / 5) :=
    (tendsto_rpow_atTop hexponent).eventually_ge_atTop ((2 : ℝ) ^ K)
  filter_upwards [hK] with T hTK
  intro ell hellK
  exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hellK).trans hTK

/-! ## Uniform control of the unit log-bin widths -/

/-- A positive power lower bound for a length makes its normalized unit
log-bin width eventually smaller than any prescribed positive constant. -/
theorem eventually_inv_log_le_of_rpow_lower
    {alpha delta : ℝ} (halpha : 0 < alpha) (hdelta : 0 < delta) :
    ∀ᶠ T : ℝ in atTop, ∀ N : ℝ,
      T ^ alpha ≤ N → 1 / Real.log N ≤ delta := by
  have hproduct : 0 < alpha * delta := mul_pos halpha hdelta
  have hlog : ∀ᶠ T : ℝ in atTop,
      1 / (alpha * delta) ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually_ge_atTop (1 / (alpha * delta))
  filter_upwards [hlog, eventually_gt_atTop (1 : ℝ)] with T hlogT hT
  intro N hNlower
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hTpowerOne : 1 < T ^ alpha := by
    rw [← Real.rpow_zero T]
    exact (Real.rpow_lt_rpow_left_iff hT).2 halpha
  have hNone : 1 < N := hTpowerOne.trans_le hNlower
  have hlogNpos : 0 < Real.log N := Real.log_pos hNone
  have hlogLower : alpha * Real.log T ≤ Real.log N := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hTpos alpha) hNlower
    rwa [Real.log_rpow hTpos] at h
  have hscale : 1 ≤ (alpha * delta) * Real.log T := by
    have hmul := mul_le_mul_of_nonneg_left hlogT hproduct.le
    calc
      (1 : ℝ) = (alpha * delta) * (1 / (alpha * delta)) := by
        field_simp [hproduct.ne']
      _ ≤ (alpha * delta) * Real.log T := hmul
  have hscaledLog : delta * (alpha * Real.log T) ≤
      delta * Real.log N :=
    mul_le_mul_of_nonneg_left hlogLower hdelta.le
  apply (div_le_iff₀ hlogNpos).2
  nlinarith

/-- Both literal unit-bin widths, including the powered-slice shift in the
first coordinate, fit inside the two-epsilon allowance used by the outer
threshold transfer. -/
theorem eventually_typeII_logBin_widths
    {eps shift : ℝ} (heps : 0 < eps) (hepsSmall : eps ≤ 1 / 1000)
    (hshift : shift ≤ eps) :
    ∀ᶠ T : ℝ in atTop, ∀ N₁ N₂ : ℝ,
      T ^ (eps / 5) ≤ N₁ →
      T ^ (9 / 11 - 10 * eps) ≤ N₂ →
      1 / Real.log N₁ + shift ≤ 2 * eps ∧
        1 / Real.log N₂ ≤ 2 * eps := by
  have halpha₂ : 0 < 9 / 11 - 10 * eps := by
    norm_num at hepsSmall ⊢
    linarith
  have hwidth₁ := eventually_inv_log_le_of_rpow_lower
    (show 0 < eps / 5 by positivity) heps
  have hwidth₂ := eventually_inv_log_le_of_rpow_lower halpha₂ heps
  filter_upwards [hwidth₁, hwidth₂] with T hwidth₁T hwidth₂T
  intro N₁ N₂ hN₁ hN₂
  have hw₁ := hwidth₁T N₁ hN₁
  have hw₂ := hwidth₂T N₂ hN₂
  constructor <;> linarith

/-- Exponent bounds and uniform absorption of `2^ell` give the literal
natural-number support bounds required by the prepared powered branch. -/
theorem natural_poweredSupportBounds
    {T eps theta : ℝ} {N ell : ℕ}
    (hT : 1 < T) (heps : 0 ≤ eps)
    (hmodel : (N : ℝ) = T ^ theta)
    (hellLower : 5 / 6 - eps ≤ (ell : ℝ) * theta)
    (hellUpper : (ell : ℝ) * theta ≤ 1 - eps / 2)
    (hfactor : (2 : ℝ) ^ ell ≤ T ^ (2 * eps / 5)) :
    T ^ (9 / 11 - 10 * eps) ≤ ((N ^ ell : ℕ) : ℝ) ∧
      (((2 * N) ^ ell : ℕ) : ℝ) ≤ T ^ (1 - eps / 10) := by
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hNpow : ((N ^ ell : ℕ) : ℝ) =
      T ^ ((ell : ℝ) * theta) := by
    calc
      ((N ^ ell : ℕ) : ℝ) = (N : ℝ) ^ ell := by norm_num
      _ = (T ^ theta) ^ ell := by rw [hmodel]
      _ = T ^ ((ell : ℝ) * theta) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hTpos.le]
        congr 1
        ring
  have hbaseLower :
      T ^ (9 / 11 - 10 * eps) ≤ ((N ^ ell : ℕ) : ℝ) := by
    rw [hNpow]
    apply Real.rpow_le_rpow_of_exponent_le hT.le
    nlinarith
  have hbaseUpper :
      ((N ^ ell : ℕ) : ℝ) ≤ T ^ (1 - eps / 2) := by
    rw [hNpow]
    exact Real.rpow_le_rpow_of_exponent_le hT.le hellUpper
  refine ⟨hbaseLower, ?_⟩
  have hexpanded := dyadicExpansionPreservesUpperRange hTpos
    (show 0 ≤ ((N ^ ell : ℕ) : ℝ) by positivity) hbaseUpper hfactor
  simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, mul_pow] using
    hexpanded

/-- The logarithmic product hypotheses imply the strong complementary
interval used by the weighted extreme-range theorem.  This is the literal
output of `complementaryLengthBounds`; it is exported separately so that a
caller needing the sharper lower exponent `9/11 - 2 * eps` does not have to
reconstruct it from the outer hypotheses. -/
theorem eventually_complementaryNatural_bounds
    (L : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ T : ℝ in atTop, ∀ N₁ N₂ : ℕ,
      1 ≤ N₁ → 1 ≤ N₂ →
      (Real.log T) ^ (-L) ≤ ((N₁ : ℝ) * (N₂ : ℝ)) / T →
      ((N₁ : ℝ) * (N₂ : ℝ)) / T ≤ (Real.log T) ^ L →
      T ^ (eps / 5) ≤ (N₁ : ℝ) →
      (N₁ : ℝ) ≤ T ^ (2 / 11 + eps) →
      T ^ (9 / 11 - 2 * eps) ≤ (N₂ : ℝ) ∧
        (N₂ : ℝ) ≤ T ^ (1 - eps / 6) := by
  have hproduct := eventually_product_power_bounds L
    (show 0 < eps / 30 by positivity)
  filter_upwards [hproduct, eventually_gt_atTop (1 : ℝ)] with T hproductT hT
  intro N₁ N₂ hN₁ _hN₂ hprodLower hprodUpper hN₁lower hN₁upper
  have hN₁pos : 0 < (N₁ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN₁)
  have hpowerBounds := hproductT (N₁ : ℝ) (N₂ : ℝ) hN₁pos
    hprodLower hprodUpper
  have hcomplement := complementaryLengthBounds hT.le heps.le hN₁pos
    hpowerBounds.1 hpowerBounds.2 hN₁lower hN₁upper
  exact hcomplement

/-- The strong complementary interval is contained in the wider interval
accepted by the hybrid-density input.  The cutoff remains uniform in both
natural lengths. -/
theorem eventually_complementaryNatural_fitsHybridRange
    (L : ℝ) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ T : ℝ in atTop, ∀ N₁ N₂ : ℕ,
      1 ≤ N₁ → 1 ≤ N₂ →
      (Real.log T) ^ (-L) ≤ ((N₁ : ℝ) * (N₂ : ℝ)) / T →
      ((N₁ : ℝ) * (N₂ : ℝ)) / T ≤ (Real.log T) ^ L →
      T ^ (eps / 5) ≤ (N₁ : ℝ) →
      (N₁ : ℝ) ≤ T ^ (2 / 11 + eps) →
      T ^ (9 / 11 - 10 * eps) ≤ (N₂ : ℝ) ∧
        (N₂ : ℝ) ≤ T ^ (1 - eps / 10) := by
  have hstrong := eventually_complementaryNatural_bounds L heps
  filter_upwards [hstrong, eventually_gt_atTop (1 : ℝ)] with
      T hstrongT hT
  intro N₁ N₂ hN₁ hN₂ hprodLower hprodUpper hN₁lower hN₁upper
  have hbounds := hstrongT N₁ N₂ hN₁ hN₂ hprodLower hprodUpper
    hN₁lower hN₁upper
  exact complementaryLengthFitsHybridRange hT.le heps.le
    hbounds.1 hbounds.2

/-- The outer short-length hypotheses produce all literal geometry for the
powered branch: an exact logarithmic model, a bounded order, the natural
support interval, and uniform absorption of the finite slice loss. -/
theorem eventually_exists_naturalPoweredGeometry
    {eps shift : ℝ} (heps : 0 < eps) (hepsSmall : eps ≤ 2 / 121)
    (hshift : 0 < shift) :
    ∀ᶠ T : ℝ in atTop, ∀ N₁ : ℕ,
      1 ≤ N₁ →
      T ^ (eps / 5) ≤ (N₁ : ℝ) →
      (N₁ : ℝ) ≤ T ^ (2 / 11 + eps) →
      ∃ theta : ℝ, ∃ ell : ℕ,
        (N₁ : ℝ) = T ^ theta ∧
        0 ≤ theta ∧
        eps / 5 ≤ theta ∧ theta ≤ 2 / 11 + eps ∧
        5 ≤ ell ∧ ell ≤ mediumPowerOrderCap eps ∧
        5 / 6 - eps ≤ (ell : ℝ) * theta ∧
        (ell : ℝ) * theta ≤ 1 - eps / 2 ∧
        T ^ (9 / 11 - 10 * eps) ≤ ((N₁ ^ ell : ℕ) : ℝ) ∧
        (((2 * N₁) ^ ell : ℕ) : ℝ) ≤ T ^ (1 - eps / 10) ∧
        (ell : ℝ) ≤ (((N₁ : ℝ) ^ ell) ^ shift) := by
  have hfactor := eventually_twoPow_le_mediumMargin_uniform
    (mediumPowerOrderCap eps) heps
  have habsorb := eventually_ell_le_poweredScale_rpow_medium_ceil heps hshift
  filter_upwards [hfactor, habsorb,
    eventually_gt_atTop (1 : ℝ)] with T hfactorT habsorbT hT
  intro N₁ hN₁ hN₁lower hN₁upper
  have hN₁pos : 0 < (N₁ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN₁)
  let theta := Hybrid.logarithmicLengthExponent T (N₁ : ℝ)
  have hmodel : (N₁ : ℝ) = T ^ theta :=
    Hybrid.eq_rpow_logarithmicLengthExponent hT hN₁pos
  have hthetaBounds : eps / 5 ≤ theta ∧ theta ≤ 2 / 11 + eps :=
    Hybrid.logarithmicLengthExponent_bounds hT hN₁pos
      hN₁lower hN₁upper
  obtain ⟨ell, hellFive, hellCap, hellLower, hellUpper⟩ :=
    exists_poweringExponent_le_mediumPowerOrderCap heps hepsSmall
      hthetaBounds.1 hthetaBounds.2
  have hsupport := natural_poweredSupportBounds hT heps.le hmodel
    hellLower hellUpper (hfactorT ell hellCap)
  have habsorbActual :
      (ell : ℝ) ≤ (((N₁ : ℝ) ^ ell) ^ shift) := by
    apply habsorbT (N₁ : ℝ) ell hN₁lower
    · omega
    · simpa only [mediumPowerOrderCap] using hellCap
  exact ⟨theta, ell, hmodel,
    (show 0 ≤ theta from (by positivity : 0 ≤ eps / 5).trans hthetaBounds.1),
    hthetaBounds.1, hthetaBounds.2, hellFive, hellCap,
    hellLower, hellUpper, hsupport.1, hsupport.2, habsorbActual⟩

/-- Combined outer package matching the geometric arguments of the complete
medium-bin theorem. The logarithmic product error is exposed as an arbitrary
positive reserve `xi`, so the caller can choose it after the hybrid saving
`kappa` is known. -/
theorem eventually_exists_outerTypeIILengthGeometry
    (L : ℝ) {eps shift xi : ℝ}
    (heps : 0 < eps) (hepsSmall : eps ≤ 2 / 121)
    (hshift : 0 < shift) (hxi : 0 < xi) :
    ∀ᶠ T : ℝ in atTop, ∀ N₁ N₂ : ℕ,
      1 ≤ N₁ → 1 ≤ N₂ →
      (Real.log T) ^ (-L) ≤ ((N₁ : ℝ) * (N₂ : ℝ)) / T →
      ((N₁ : ℝ) * (N₂ : ℝ)) / T ≤ (Real.log T) ^ L →
      T ^ (eps / 5) ≤ (N₁ : ℝ) →
      (N₁ : ℝ) ≤ T ^ (2 / 11 + eps) →
      ∃ eta₁ eta₂ : ℝ, ∃ ell : ℕ,
        (N₁ : ℝ) = T ^ eta₁ ∧
        (N₂ : ℝ) = T ^ eta₂ ∧
        0 ≤ eta₁ ∧ 0 ≤ eta₂ ∧
        5 ≤ ell ∧ ell ≤ mediumPowerOrderCap eps ∧
        T ^ (1 - xi) ≤ (N₁ : ℝ) * (N₂ : ℝ) ∧
        T ^ (9 / 11 - 10 * eps) ≤ ((N₁ ^ ell : ℕ) : ℝ) ∧
        (((2 * N₁) ^ ell : ℕ) : ℝ) ≤ T ^ (1 - eps / 10) ∧
        T ^ (9 / 11 - 10 * eps) ≤ (N₂ : ℝ) ∧
        (N₂ : ℝ) ≤ T ^ (1 - eps / 10) ∧
        (ell : ℝ) ≤ (((N₁ : ℝ) ^ ell) ^ shift) := by
  have hpowered := eventually_exists_naturalPoweredGeometry
    heps hepsSmall hshift
  have hcomplement := eventually_complementaryNatural_fitsHybridRange L heps
  have hproduct := eventually_product_power_bounds L hxi
  filter_upwards [hpowered, hcomplement, hproduct,
    eventually_gt_atTop (1 : ℝ)] with T hpoweredT hcomplementT hproductT hT
  intro N₁ N₂ hN₁ hN₂ hprodLower hprodUpper hN₁lower hN₁upper
  obtain ⟨eta₁, ell, hmodel₁, heta₁, _heta₁lower, _heta₁upper,
      hellFive, hellCap, _hellLower, _hellUpper,
      hpoweredLower, hpoweredUpper, habsorb⟩ :=
    hpoweredT N₁ hN₁ hN₁lower hN₁upper
  have hcomplementBounds := hcomplementT N₁ N₂ hN₁ hN₂
    hprodLower hprodUpper hN₁lower hN₁upper
  have hN₁pos : 0 < (N₁ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN₁)
  have hN₂pos : 0 < (N₂ : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN₂)
  have hproductBounds := hproductT (N₁ : ℝ) (N₂ : ℝ) hN₁pos
    hprodLower hprodUpper
  let eta₂ := Hybrid.logarithmicLengthExponent T (N₂ : ℝ)
  have hmodel₂ : (N₂ : ℝ) = T ^ eta₂ :=
    Hybrid.eq_rpow_logarithmicLengthExponent hT hN₂pos
  have hN₂one : T ^ (0 : ℝ) ≤ (N₂ : ℝ) := by
    simpa using (show (1 : ℝ) ≤ (N₂ : ℝ) by exact_mod_cast hN₂)
  have heta₂ : 0 ≤ eta₂ :=
    (Hybrid.logarithmicLengthExponent_bounds hT hN₂pos hN₂one
      hcomplementBounds.2).1
  exact ⟨eta₁, eta₂, ell, hmodel₁, hmodel₂, heta₁, heta₂,
    hellFive, hellCap, hproductBounds.1, hpoweredLower, hpoweredUpper,
    hcomplementBounds.1, hcomplementBounds.2, habsorb⟩

/-- Metadata for the complete outer length geometry. -/
def outerLengthGeometryModule : ProofModule :=
  { name := "TypeII.OuterLengthGeometry"
    paperLocation :=
      "Proof of Proposition 5.1, powered and complementary length choices"
    purpose :=
      "Choose a bounded powering order, prove the literal natural support bounds, export both the strong complementary interval and its hybrid-range weakening, absorb dyadic expansion and slice losses uniformly, model both lengths as powers of T, and expose an arbitrary positive product-loss reserve."
    dependsOn := ["TypeII.PolynomialLengthRanges", "TypeII.MediumThresholdBridge"]
    status := .proved }

end

end TypeII
end ExactSemiprimes
