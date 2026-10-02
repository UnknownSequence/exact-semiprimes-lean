import ExactSemiprimes.Sparse.PropagationParameters

/-!
# Sparse support bounds uniformly over a window of prime scales

The Section 7.2 argument sums over `≍ log log X` prime blocks `P`, so every
estimate used for one block must hold uniformly for `P = (log X)^a` with
`a` in a fixed compact window.  The Hildebrand--Tenenbaum input is a
fixed-`a` limit; this file upgrades the resulting smooth-support bound to a
uniform one by a finite subdivision of the window and monotonicity of
`Ψ(X,Y)` in `Y`.
-/

namespace ExactSemiprimes
namespace Final

open Filter Real

noncomputable section

/-- The exponent `a` with `P = (log X)^a`. -/
def scaleExponent (X P : ℝ) : ℝ := Real.logb (Real.log X) P

theorem rpow_scaleExponent {X P : ℝ} (hX : Real.exp 1 < X) (hP : 0 < P) :
    (Real.log X) ^ scaleExponent X P = P := by
  have hXpos : 0 < X := (Real.exp_pos 1).trans hX
  have hlog : 1 < Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hX
  exact Real.rpow_logb (by linarith) (by linarith) hP

theorem scaleExponent_le_of_le_rpow {X P b : ℝ} (hX : Real.exp 1 < X)
    (hP : 0 < P) (hPb : P ≤ (Real.log X) ^ b) : scaleExponent X P ≤ b := by
  have hlog : 1 < Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hX
  rw [scaleExponent, Real.logb_le_iff_le_rpow hlog hP]
  exact hPb

theorem le_scaleExponent_of_rpow_le {X P b : ℝ} (hX : Real.exp 1 < X)
    (hP : 0 < P) (hPb : (Real.log X) ^ b ≤ P) : b ≤ scaleExponent X P := by
  have hlog : 1 < Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hX
  rw [scaleExponent, Real.le_logb_iff_rpow_le hlog hP]
  exact hPb

/-- Elementary reciprocal comparison used to trade an upper exponent for the
actual one. -/
theorem one_div_sub_one_div_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    1 / a - 1 / b ≤ b - a := by
  have hapos : 0 < a := by linarith
  have hbpos : 0 < b := by linarith
  rw [div_sub_div _ _ hapos.ne' hbpos.ne', div_le_iff₀ (mul_pos hapos hbpos)]
  have : 1 ≤ a * b := by nlinarith
  nlinarith

/-- One fixed-exponent support estimate, with the cutoff stated through an
upper bound `P ≤ (log X)^b`. -/
theorem eventually_card_dyadicPrimePowerSupport_le_of_le_rpow
    (hHT : HildebrandTenenbaumCorollaryOneThreeStatement)
    {b slack powerSlack : ℝ} (hb : 1 < b) (hslack : 0 < slack)
    (hpowerSlack : 0 < powerSlack) :
    ∀ᶠ X : ℕ in atTop, ∀ (P : ℝ) (k : ℕ),
      0 ≤ P → P ≤ (Real.log (X : ℝ)) ^ b →
      1 ≤ ⌊2 * P⌋₊ → ⌊2 * P⌋₊ ^ k ≤ X →
      ((Sparse.primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
        (X : ℝ) ^ (1 - 1 / (b + slack) + powerSlack) := by
  have hbSlack : 1 < b + slack := by linarith
  have hcutReal :=
    Sparse.eventually_floor_two_mul_log_rpow_le_floor_log_rpow_add b hslack
  have hcutNat :
      ∀ᶠ X : ℕ in atTop,
        ⌊2 * (Real.log (X : ℝ)) ^ b⌋₊ ≤
          ⌊(Real.log (X : ℝ)) ^ (b + slack)⌋₊ :=
    tendsto_natCast_atTop_atTop.eventually hcutReal
  have hHTX := Sparse.eventually_logPowerSmoothNumberCount_le_rpow
    hHT hbSlack hpowerSlack
  filter_upwards [hcutNat, hHTX] with X hcut hHTbound
  intro P k hP0 hPb hY hPower
  have hcard := Sparse.card_dyadicPrimePowerSupport_le_smoothNumberCount
    hP0 hY hPower
  have hfloor : ⌊2 * P⌋₊ ≤ ⌊(Real.log (X : ℝ)) ^ (b + slack)⌋₊ :=
    (Nat.floor_mono (by linarith)).trans hcut
  have hmono := Sparse.smoothNumberCount_mono_right (X := X) hfloor
  have hnat : (Sparse.primePowerSupport (dyadicPrimes P) k).card ≤
      logPowerSmoothNumberCount (b + slack) X := hcard.trans hmono
  exact (by exact_mod_cast hnat :
    ((Sparse.primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
      (logPowerSmoothNumberCount (b + slack) X : ℝ)).trans hHTbound

/-- **Uniform sparse support bound.**  For every window `[alo, ahi]` with
`1 < alo < ahi` and every `ω > 0`, eventually every block `P` in
`[(log X)^alo, (log X)^ahi]` has sparse support of size at most
`X^(1 - 1/a + ω)`, where `P = (log X)^a`. -/
theorem eventually_uniform_card_sparseSupport
    (hHT : HildebrandTenenbaumCorollaryOneThreeStatement)
    {alo ahi ω : ℝ} (halo : 1 < alo) (hlohi : alo < ahi) (hω : 0 < ω) :
    ∀ᶠ X : ℕ in atTop, ∀ (P : ℝ) (k : ℕ),
      (Real.log (X : ℝ)) ^ alo ≤ P → P ≤ (Real.log (X : ℝ)) ^ ahi →
      1 ≤ ⌊2 * P⌋₊ → ⌊2 * P⌋₊ ^ k ≤ X →
      ((Sparse.primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
        (X : ℝ) ^ (1 - 1 / scaleExponent (X : ℝ) P + ω) := by
  -- Subdivide `[alo, ahi]` into `J` pieces of width `w ≤ ω/4`.
  set J : ℕ := ⌈(ahi - alo) / (ω / 4)⌉₊ + 1 with hJdef
  have hJpos : (0 : ℝ) < J := by positivity
  set w : ℝ := (ahi - alo) / J with hwdef
  have hω4 : 0 < ω / 4 := by positivity
  have hwpos : 0 < w := div_pos (by linarith) hJpos
  have hw : w ≤ ω / 4 := by
    rw [hwdef, div_le_iff₀ hJpos]
    have hceil := Nat.le_ceil ((ahi - alo) / (ω / 4))
    have hJge : (ahi - alo) / (ω / 4) ≤ (J : ℝ) := by
      rw [hJdef]; push_cast; linarith
    rw [div_le_iff₀ hω4] at hJge
    linarith
  let grid : Fin (J + 1) → ℝ := fun j ↦ alo + (j : ℕ) * w
  have hgrid_one : ∀ j, 1 < grid j := by
    intro j
    have : 0 ≤ ((j : ℕ) : ℝ) * w := mul_nonneg (Nat.cast_nonneg _) hwpos.le
    simp only [grid]; linarith
  have heach : ∀ j : Fin (J + 1), ∀ᶠ X : ℕ in atTop, ∀ (P : ℝ) (k : ℕ),
      0 ≤ P → P ≤ (Real.log (X : ℝ)) ^ grid j →
      1 ≤ ⌊2 * P⌋₊ → ⌊2 * P⌋₊ ^ k ≤ X →
      ((Sparse.primePowerSupport (dyadicPrimes P) k).card : ℝ) ≤
        (X : ℝ) ^ (1 - 1 / (grid j + ω / 4) + ω / 4) := fun j ↦
    eventually_card_dyadicPrimePowerSupport_le_of_le_rpow hHT
      (hgrid_one j) hω4 hω4
  have hall := Filter.eventually_all.2 heach
  have hXe : ∀ᶠ X : ℕ in atTop, Real.exp 1 < (X : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  filter_upwards [hall, hXe] with X hXall hXe
  intro P k hPlo hPhi hY hPower
  have hlog : 1 < Real.log (X : ℝ) := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hXe
  have hPpos : 0 < P := (Real.rpow_pos_of_pos (by linarith) _).trans_le hPlo
  set b := scaleExponent (X : ℝ) P with hbdef
  have hblo : alo ≤ b := le_scaleExponent_of_rpow_le hXe hPpos hPlo
  have hbhi : b ≤ ahi := scaleExponent_le_of_le_rpow hXe hPpos hPhi
  -- Choose the grid point just above `b`.
  set jn : ℕ := ⌈(b - alo) / w⌉₊ with hjn
  have hjnle : jn ≤ J := by
    rw [hjn]
    apply Nat.ceil_le.2
    rw [div_le_iff₀ hwpos, hwdef, mul_div_cancel₀ _ hJpos.ne']
    linarith
  let j : Fin (J + 1) := ⟨jn, Nat.lt_succ_of_le hjnle⟩
  have hgj : grid j = alo + (jn : ℝ) * w := rfl
  have hceil1 : (b - alo) / w ≤ (jn : ℝ) := Nat.le_ceil _
  have hceil2 : (jn : ℝ) < (b - alo) / w + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (by linarith) hwpos.le)
  have hbg : b ≤ grid j := by
    rw [hgj]
    have := (div_le_iff₀ hwpos).1 hceil1
    linarith
  have hgb : grid j ≤ b + w := by
    rw [hgj]
    have h2 : (jn : ℝ) * w < ((b - alo) / w + 1) * w :=
      mul_lt_mul_of_pos_right hceil2 hwpos
    rw [add_mul, div_mul_cancel₀ _ hwpos.ne'] at h2
    linarith
  have hPgrid : P ≤ (Real.log (X : ℝ)) ^ grid j := by
    calc P = (Real.log (X : ℝ)) ^ b := (rpow_scaleExponent hXe hPpos).symm
      _ ≤ (Real.log (X : ℝ)) ^ grid j :=
        Real.rpow_le_rpow_of_exponent_le hlog.le hbg
  have hbound := hXall j P k hPpos.le hPgrid hY hPower
  refine hbound.trans (Real.rpow_le_rpow_of_exponent_le
    (by linarith [Real.add_one_le_exp (1 : ℝ)] : (1 : ℝ) ≤ (X : ℝ)) ?_)
  have hb1 : 1 ≤ b := by linarith
  have hrec := one_div_sub_one_div_le hb1
    (show b ≤ grid j + ω / 4 by linarith)
  linarith

/-- `log log X / log X → 0` along the naturals, in the eventual form used
below. -/
theorem eventually_loglog_div_log_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop,
      Real.log (Real.log (X : ℝ)) / Real.log (X : ℝ) ≤ c := by
  have hlim : Tendsto (fun y : ℝ ↦ Real.log y / y) atTop (nhds 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have hlogNat : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact (hlim.comp hlogNat).eventually (ge_mem_nhds hc)

/-- **Uniform sparse geometry.**  Uniformly for blocks
`P ∈ [(log X)^alo, (log X)^ahi]`, the floor choice
`k = ⌊log X / log 2P⌋` gives a sparse polynomial of length
`M = P^k ∈ [X^(1-s), X]` with the support cutoff `⌊2P⌋^k ≤ X`. -/
theorem eventually_uniform_sparseGeometry
    {alo ahi s : ℝ} (halo : 1 < alo) (hs : 0 < s) :
    ∀ᶠ X : ℕ in atTop, ∀ P : ℝ,
      (Real.log (X : ℝ)) ^ alo ≤ P → P ≤ (Real.log (X : ℝ)) ^ ahi →
      1 < (X : ℝ) ∧ 0 < P ∧ 1 ≤ Real.log (2 * P) ∧ 1 ≤ ⌊2 * P⌋₊ ∧
        ⌊2 * P⌋₊ ^ ⌊Real.log (X : ℝ) / Real.log (2 * P)⌋₊ ≤ X ∧
        1 ≤ P ^ ⌊Real.log (X : ℝ) / Real.log (2 * P)⌋₊ ∧
        P ^ ⌊Real.log (X : ℝ) / Real.log (2 * P)⌋₊ ≤ (X : ℝ) ∧
        1 - s ≤ Real.log (P ^ ⌊Real.log (X : ℝ) / Real.log (2 * P)⌋₊) /
          Real.log (X : ℝ) := by
  have hlogNat : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglogNat : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ)))
      atTop atTop := Real.tendsto_log_atTop.comp hlogNat
  have hs2 : 0 < s / 2 := by positivity
  have hahi : 0 < |ahi| + 1 := by positivity
  filter_upwards [hlogNat.eventually_ge_atTop (Real.exp 2),
    hloglogNat.eventually_ge_atTop (Real.log 2 / (s / 2)),
    hloglogNat.eventually_ge_atTop 1,
    eventually_loglog_div_log_le (div_pos hs2 hahi)] with
      X hlogX hll hll1 hratio
  intro P hPlo hPhi
  have hlogXpos : 0 < Real.log (X : ℝ) :=
    lt_of_lt_of_le (Real.exp_pos 2) hlogX
  have hX1 : 1 < (X : ℝ) := by
    by_contra h
    push Not at h
    have : Real.log (X : ℝ) ≤ 0 := Real.log_nonpos (Nat.cast_nonneg _) h
    linarith
  have hlogX1 : 1 ≤ Real.log (X : ℝ) := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have hloglogPos : 0 < Real.log (Real.log (X : ℝ)) := by linarith
  have hlogXrpow : Real.log (X : ℝ) ≤ (Real.log (X : ℝ)) ^ alo := by
    calc Real.log (X : ℝ) = (Real.log (X : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Real.log (X : ℝ)) ^ alo :=
        Real.rpow_le_rpow_of_exponent_le hlogX1 halo.le
  have hPge : Real.exp 2 ≤ P := hlogX.trans (hlogXrpow.trans hPlo)
  have hPpos : 0 < P := lt_of_lt_of_le (Real.exp_pos 2) hPge
  have hP1 : 1 ≤ P := by have := Real.add_one_le_exp (2 : ℝ); linarith
  have hlogP : 2 ≤ Real.log P := by
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) hPge
  have hlog2P : Real.log (2 * P) = Real.log 2 + Real.log P :=
    Real.log_mul (by norm_num) hPpos.ne'
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 1 ≤ Real.log (2 * P) := by rw [hlog2P]; linarith
  have hfloor1 : 1 ≤ ⌊2 * P⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hpower := Sparse.floor_two_mul_pow_paperExponent_le hX1 hPpos hden
  set k := ⌊Real.log (X : ℝ) / Real.log (2 * P)⌋₊ with hk
  have hPfloor : P ≤ ((⌊2 * P⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (2 * P)
    linarith
  have hM1 : 1 ≤ P ^ k := one_le_pow₀ hP1
  have hMX : P ^ k ≤ (X : ℝ) := by
    calc P ^ k ≤ ((⌊2 * P⌋₊ : ℕ) : ℝ) ^ k := pow_le_pow_left₀ hPpos.le hPfloor k
      _ ≤ (X : ℝ) := by exact_mod_cast hpower
  refine ⟨hX1, hPpos, hden, hfloor1, hpower, hM1, hMX, ?_⟩
  -- Lower bound for `log M / log X`.
  have hdenpos : 0 < Real.log (2 * P) := by linarith
  have hkLower : Real.log (X : ℝ) / Real.log (2 * P) - 1 < (k : ℝ) :=
    by have := Nat.lt_floor_add_one (Real.log (X : ℝ) / Real.log (2 * P)); linarith
  have hlogM : Real.log (P ^ k) = k * Real.log P := by rw [Real.log_pow]
  have hlogPle : Real.log P ≤ ahi * Real.log (Real.log (X : ℝ)) := by
    have := Real.log_le_log hPpos hPhi
    rwa [Real.log_rpow hlogXpos] at this
  have hlogPge : alo * Real.log (Real.log (X : ℝ)) ≤ Real.log P := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hlogXpos _) hPlo
    rwa [Real.log_rpow hlogXpos] at this
  -- `log 2 / log(2P) ≤ s/2`
  have hA : Real.log 2 / Real.log (2 * P) ≤ s / 2 := by
    rw [div_le_iff₀ hdenpos]
    have h1 : Real.log 2 ≤ s / 2 * Real.log (Real.log (X : ℝ)) := by
      rw [div_le_iff₀ hs2] at hll; linarith
    have h2 : Real.log (Real.log (X : ℝ)) ≤ Real.log (2 * P) := by
      rw [hlog2P]; nlinarith
    nlinarith
  -- `log P / log X ≤ s/2`
  have hB : Real.log P / Real.log (X : ℝ) ≤ s / 2 := by
    rw [div_le_iff₀ hlogXpos]
    rw [div_le_iff₀ hlogXpos] at hratio
    have hahiabs : ahi ≤ |ahi| + 1 := by linarith [le_abs_self ahi]
    have : Real.log P ≤ (|ahi| + 1) * Real.log (Real.log (X : ℝ)) :=
      hlogPle.trans (mul_le_mul_of_nonneg_right hahiabs hloglogPos.le)
    have h3 : (|ahi| + 1) * Real.log (Real.log (X : ℝ)) ≤
        s / 2 * Real.log (X : ℝ) := by
      have := mul_le_mul_of_nonneg_left hratio hahi.le
      have heq : (|ahi| + 1) * (s / 2 / (|ahi| + 1) * Real.log (X : ℝ)) =
          s / 2 * Real.log (X : ℝ) := by field_simp
      linarith
    linarith
  rw [hlogM, le_div_iff₀ hlogXpos]
  have hlogPnn : 0 ≤ Real.log P := by linarith
  have hkP : (Real.log (X : ℝ) / Real.log (2 * P) - 1) * Real.log P ≤
      (k : ℝ) * Real.log P := mul_le_mul_of_nonneg_right hkLower.le hlogPnn
  have hident : (Real.log (X : ℝ) / Real.log (2 * P) - 1) * Real.log P =
      Real.log (X : ℝ) - Real.log (X : ℝ) * (Real.log 2 / Real.log (2 * P))
        - Real.log P := by
    field_simp
    rw [hlog2P]; ring
  have hC : Real.log (X : ℝ) * (Real.log 2 / Real.log (2 * P)) ≤
      Real.log (X : ℝ) * (s / 2) := mul_le_mul_of_nonneg_left hA hlogXpos.le
  have hD : Real.log P ≤ s / 2 * Real.log (X : ℝ) := by
    rwa [div_le_iff₀ hlogXpos] at hB
  nlinarith

end

end Final
end ExactSemiprimes
