import ExactSemiprimes.Completion.RealToIntegerExceptions
import ExactSemiprimes.Completion.PrimeWindowTransfer
import ExactSemiprimes.Completion.UniqueSmallPrimeFactor

/-!
# Globalization from dyadic blocks

This file contains only elementary bookkeeping.  Any estimate for the number
of exceptions on one dyadic block is an explicit hypothesis.  We prove that
the dyadic blocks cover an initial interval, sum their exceptional counts,
and pass from a density-zero statement along powers of two to a density-zero
statement along all natural numbers.
-/

namespace ExactSemiprimes
namespace Completion

open Filter Finset Asymptotics

noncomputable section

/-- Exceptions up to `2^(K+1)` are either exceptions up to `2^K` or lie in
the next dyadic block `[2^K,2^(K+1)]`.  The overlap at `2^K` is harmless. -/
theorem exceptionalUpTo_two_pow_succ_subset (P : ℕ → Prop) (K : ℕ) :
    exceptionalUpTo P (2 ^ (K + 1)) ⊆
      exceptionalUpTo P (2 ^ K) ∪ exceptionalOnDyadicBlock P (2 ^ K) := by
  intro n hn
  simp only [exceptionalUpTo, exceptionalOnDyadicBlock, Finset.mem_union,
    Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  rcases hn with ⟨⟨hn_one, hn_top⟩, hnP⟩
  by_cases hn_mid : n ≤ 2 ^ K
  · exact Or.inl ⟨⟨hn_one, hn_mid⟩, hnP⟩
  · refine Or.inr ⟨⟨Nat.le_of_lt (Nat.lt_of_not_ge hn_mid), ?_⟩, hnP⟩
    simpa [pow_succ, Nat.mul_comm] using hn_top

/-- Cardinality form of the one-step dyadic decomposition. -/
theorem card_exceptionalUpTo_two_pow_succ_le (P : ℕ → Prop) (K : ℕ) :
    (exceptionalUpTo P (2 ^ (K + 1))).card ≤
      (exceptionalUpTo P (2 ^ K)).card +
        (exceptionalOnDyadicBlock P (2 ^ K)).card := by
  calc
    (exceptionalUpTo P (2 ^ (K + 1))).card
        ≤ (exceptionalUpTo P (2 ^ K) ∪
            exceptionalOnDyadicBlock P (2 ^ K)).card :=
          Finset.card_le_card (exceptionalUpTo_two_pow_succ_subset P K)
    _ ≤ (exceptionalUpTo P (2 ^ K)).card +
          (exceptionalOnDyadicBlock P (2 ^ K)).card :=
      Finset.card_union_le (exceptionalUpTo P (2 ^ K))
        (exceptionalOnDyadicBlock P (2 ^ K))

/-- Start the dyadic decomposition at an arbitrary earlier scale `J`. -/
theorem card_exceptionalUpTo_two_pow_le_from (P : ℕ → Prop)
    {J K : ℕ} (hJK : J ≤ K) :
    (exceptionalUpTo P (2 ^ K)).card ≤
      (exceptionalUpTo P (2 ^ J)).card +
        ∑ k ∈ Finset.Ico J K,
          (exceptionalOnDyadicBlock P (2 ^ k)).card := by
  induction K, hJK using Nat.le_induction with
  | base => simp
  | succ K hJK ih =>
      calc
        (exceptionalUpTo P (2 ^ (K + 1))).card
            ≤ (exceptionalUpTo P (2 ^ K)).card +
                (exceptionalOnDyadicBlock P (2 ^ K)).card :=
              card_exceptionalUpTo_two_pow_succ_le P K
        _ ≤ ((exceptionalUpTo P (2 ^ J)).card +
              ∑ k ∈ Finset.Ico J K,
                (exceptionalOnDyadicBlock P (2 ^ k)).card) +
              (exceptionalOnDyadicBlock P (2 ^ K)).card :=
            Nat.add_le_add_right ih _
        _ = (exceptionalUpTo P (2 ^ J)).card +
              ∑ k ∈ Finset.Ico J (K + 1),
                (exceptionalOnDyadicBlock P (2 ^ k)).card := by
            rw [Finset.sum_Ico_succ_top hJK]
            omega

/-- The exceptional set is contained in its ambient integer interval. -/
theorem card_exceptionalUpTo_le (P : ℕ → Prop) (X : ℕ) :
    (exceptionalUpTo P X).card ≤ X := by
  classical
  calc
    (exceptionalUpTo P X).card ≤ (Finset.Icc 1 X).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ X := by simp

/-- Summing the exceptional counts of the dyadic blocks covers every
exception up to a power of two.  No analytic estimate is used here. -/
theorem card_exceptionalUpTo_two_pow_le_sum_dyadic (P : ℕ → Prop) (K : ℕ) :
    (exceptionalUpTo P (2 ^ K)).card ≤
      1 + ∑ k ∈ Finset.range K,
        (exceptionalOnDyadicBlock P (2 ^ k)).card := by
  classical
  induction K with
  | zero =>
      simp only [pow_zero, Finset.range_zero, Finset.sum_empty, add_zero]
      calc
        (exceptionalUpTo P 1).card ≤ (Finset.Icc 1 1).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = 1 := by simp
  | succ K ih =>
      calc
        (exceptionalUpTo P (2 ^ (K + 1))).card
            ≤ (exceptionalUpTo P (2 ^ K)).card +
                (exceptionalOnDyadicBlock P (2 ^ K)).card :=
              card_exceptionalUpTo_two_pow_succ_le P K
        _ ≤ (1 + ∑ k ∈ Finset.range K,
                (exceptionalOnDyadicBlock P (2 ^ k)).card) +
              (exceptionalOnDyadicBlock P (2 ^ K)).card :=
            Nat.add_le_add_right ih _
        _ = 1 + ∑ k ∈ Finset.range (K + 1),
              (exceptionalOnDyadicBlock P (2 ^ k)).card := by
            rw [Finset.sum_range_succ]
            omega

/-- Real-valued summation principle.  In applications `B k` is the
power-of-logarithm majorant supplied by the analytic argument on the block
`[2^k,2^(k+1)]`. -/
theorem card_exceptionalUpTo_two_pow_le_sum_majorants
    (P : ℕ → Prop) (B : ℕ → ℝ) (K : ℕ)
    (hB : ∀ k < K,
      ((exceptionalOnDyadicBlock P (2 ^ k)).card : ℝ) ≤ B k) :
    ((exceptionalUpTo P (2 ^ K)).card : ℝ) ≤
      1 + ∑ k ∈ Finset.range K, B k := by
  calc
    ((exceptionalUpTo P (2 ^ K)).card : ℝ)
        ≤ 1 + ∑ k ∈ Finset.range K,
            ((exceptionalOnDyadicBlock P (2 ^ k)).card : ℝ) := by
          exact_mod_cast card_exceptionalUpTo_two_pow_le_sum_dyadic P K
    _ ≤ 1 + ∑ k ∈ Finset.range K, B k := by
      gcongr with k hk
      exact hB k (Finset.mem_range.mp hk)

/-- A geometric weighted sum of a density-zero sequence is again
density-zero.  This is the analytic-free summation lemma needed for dyadic
globalization. -/
theorem isLittleO_sum_range_geometric {a : ℕ → ℝ}
    (ha : a =o[atTop] fun k : ℕ ↦ (2 : ℝ) ^ k) :
    (fun K : ℕ ↦ ∑ k ∈ Finset.range K, a k) =o[atTop]
      fun K : ℕ ↦ (2 : ℝ) ^ K := by
  apply isLittleO_iff.2
  intro ε hε
  have htail := isLittleO_iff.1 ha (show 0 < ε / 2 by positivity)
  rw [eventually_atTop] at htail
  obtain ⟨N, hN⟩ := htail
  let A : ℝ := ‖∑ k ∈ Finset.range N, a k‖
  have hpow : ∀ᶠ K : ℕ in atTop, A ≤ ε / 2 * (2 : ℝ) ^ K := by
    have ht : Tendsto (fun K : ℕ ↦ (2 : ℝ) ^ K) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    exact (ht.eventually (eventually_ge_atTop (A / (ε / 2)))).mono fun K hK ↦ by
      have hε2 : 0 < ε / 2 := by positivity
      calc
        A = (A / (ε / 2)) * (ε / 2) := by field_simp
        _ ≤ (2 : ℝ) ^ K * (ε / 2) :=
          mul_le_mul_of_nonneg_right hK hε2.le
        _ = ε / 2 * (2 : ℝ) ^ K := by ring
  filter_upwards [hpow, Ici_mem_atTop N] with K hAK hNK
  have hsplit :
      ∑ k ∈ Finset.range K, a k =
        (∑ k ∈ Finset.range N, a k) + ∑ k ∈ Finset.Ico N K, a k := by
    rw [Finset.sum_range_add_sum_Ico _ hNK]
  rw [hsplit]
  calc
    ‖(∑ k ∈ Finset.range N, a k) + ∑ k ∈ Finset.Ico N K, a k‖
        ≤ A + ∑ k ∈ Finset.Ico N K, ‖a k‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ ε / 2 * (2 : ℝ) ^ K +
          ∑ k ∈ Finset.Ico N K, (ε / 2) * (2 : ℝ) ^ k := by
      gcongr with k hk
      simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ k)] using
        hN k (Finset.mem_Ico.mp hk).1
    _ ≤ ε / 2 * (2 : ℝ) ^ K +
          (ε / 2) * ∑ k ∈ Finset.range K, (2 : ℝ) ^ k := by
      rw [Finset.mul_sum]
      have hsum :
          (∑ k ∈ Finset.Ico N K, (ε / 2) * (2 : ℝ) ^ k) ≤
            ∑ k ∈ Finset.range K, (ε / 2) * (2 : ℝ) ^ k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
        · intro k _ _
          positivity
      exact add_le_add_right hsum _
    _ ≤ ε / 2 * (2 : ℝ) ^ K +
          (ε / 2) * (2 : ℝ) ^ K := by
      gcongr
      have hgeom :
          (∑ k ∈ Finset.range K, (2 : ℝ) ^ k) =
            (2 : ℝ) ^ K - 1 := by
        have h := geom_sum_mul (2 : ℝ) K
        norm_num at h ⊢
        exact h
      rw [hgeom]
      linarith
    _ = ε * ‖(2 : ℝ) ^ K‖ := by
      rw [Real.norm_of_nonneg (by positivity)]
      ring

/-- A density-zero exceptional count on dyadic blocks yields a density-zero
exceptional count along the endpoints `2^K`. -/
theorem exceptionalUpTo_two_pow_isLittleO_of_dyadic
    (P : ℕ → Prop)
    (hlocal :
      (fun k : ℕ ↦ ((exceptionalOnDyadicBlock P (2 ^ k)).card : ℝ))
        =o[atTop] fun k : ℕ ↦ (2 : ℝ) ^ k) :
    (fun K : ℕ ↦ ((exceptionalUpTo P (2 ^ K)).card : ℝ))
      =o[atTop] fun K : ℕ ↦ (2 : ℝ) ^ K := by
  have hsum := isLittleO_sum_range_geometric hlocal
  have hone : (fun _K : ℕ ↦ (1 : ℝ)) =o[atTop]
      fun K : ℕ ↦ (2 : ℝ) ^ K := by
    have ht : Tendsto (fun K : ℕ ↦ (2 : ℝ) ^ K) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (r := (2 : ℝ)) (by norm_num)
    have htnorm : Tendsto (fun K : ℕ ↦ ‖(2 : ℝ) ^ K‖) atTop atTop := by
      apply ht.congr'
      filter_upwards with K
      rw [Real.norm_of_nonneg (by positivity)]
    exact isLittleO_const_left.2 (.inr htnorm)
  have hmajor := hone.add hsum
  apply isLittleO_iff.2
  intro ε hε
  filter_upwards [isLittleO_iff.1 hmajor hε] with K hK
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  have hnonneg :
      0 ≤ (1 : ℝ) + ∑ k ∈ Finset.range K,
        ((exceptionalOnDyadicBlock P (2 ^ k)).card : ℝ) := by positivity
  rw [Real.norm_of_nonneg hnonneg] at hK
  have hcard :
      ((exceptionalUpTo P (2 ^ K)).card : ℝ) ≤
        1 + ∑ k ∈ Finset.range K,
          ((exceptionalOnDyadicBlock P (2 ^ k)).card : ℝ) := by
    exact_mod_cast card_exceptionalUpTo_two_pow_le_sum_dyadic P K
  exact hcard.trans hK

/-- Monotonicity of the exceptional set with respect to its upper endpoint. -/
theorem exceptionalUpTo_mono (P : ℕ → Prop) {X Y : ℕ} (hXY : X ≤ Y) :
    exceptionalUpTo P X ⊆ exceptionalUpTo P Y := by
  intro n hn
  simp only [exceptionalUpTo, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans hXY⟩, hn.2⟩

/-- It is enough to prove density zero at the endpoints `2^K`.  The ceiling
binary logarithm chooses an endpoint between `X` and `2X`, so the change of
normalization costs only the harmless factor two. -/
theorem forAlmostAll_of_dyadic_endpoints
    (P : ℕ → Prop)
    (hdyadic :
      (fun K : ℕ ↦ ((exceptionalUpTo P (2 ^ K)).card : ℝ))
        =o[atTop] fun K : ℕ ↦ (2 : ℝ) ^ K) :
    ForAlmostAllIntegers P := by
  rw [ForAlmostAllIntegers]
  apply isLittleO_iff.2
  intro ε hε
  have hbound := isLittleO_iff.1 hdyadic (show 0 < ε / 2 by positivity)
  rw [eventually_atTop] at hbound
  obtain ⟨N, hN⟩ := hbound
  filter_upwards [eventually_ge_atTop (max 2 (2 ^ N))] with X hX
  let K := Nat.clog 2 X
  have hX_two : 2 ≤ X := (le_max_left _ _).trans hX
  have hX_pow : X ≤ 2 ^ K := Nat.le_pow_clog (by norm_num) X
  have hN_pow : 2 ^ N ≤ X := (le_max_right _ _).trans hX
  have hNK : N ≤ K := by
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp
      (hN_pow.trans hX_pow)
  have hKpos : 0 < K := by
    exact Nat.clog_pos (by norm_num) (by omega)
  have hpow_le : 2 ^ K ≤ 2 * X := by
    have hpred : 2 ^ K.pred < X := by
      dsimp [K]
      exact Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
    rw [← Nat.succ_pred_eq_of_pos hKpos, pow_succ]
    omega
  have hcard :
      ((exceptionalUpTo P X).card : ℝ) ≤
        ((exceptionalUpTo P (2 ^ K)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (exceptionalUpTo_mono P hX_pow)
  calc
    ‖((exceptionalUpTo P X).card : ℝ)‖
        = ((exceptionalUpTo P X).card : ℝ) :=
          Real.norm_of_nonneg (Nat.cast_nonneg _)
    _ ≤ ((exceptionalUpTo P (2 ^ K)).card : ℝ) := hcard
    _ = ‖((exceptionalUpTo P (2 ^ K)).card : ℝ)‖ :=
      (Real.norm_of_nonneg (Nat.cast_nonneg _)).symm
    _ ≤ ε / 2 * ‖(2 : ℝ) ^ K‖ := hN K hNK
    _ = ε / 2 * (2 : ℝ) ^ K := by
      rw [Real.norm_of_nonneg (by positivity)]
    _ ≤ ε / 2 * (2 * (X : ℝ)) := by
      gcongr
      exact_mod_cast hpow_le
    _ = ε * ‖(X : ℝ)‖ := by
      rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
      ring

/-- The standard power-of-logarithm majorant on the dyadic block based at
`2^k`.  Since `k+1` is a fixed positive multiple of
`log (2^(k+1))`, this is the convenient zero-safe form of
`X / (log X)^δ`. -/
def dyadicLogPowerMajorant (δ : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ) ^ k / (((k + 1 : ℕ) : ℝ) ^ δ)

/-- The contribution of all scales below `2^(K/2)` is negligible even on
the quantitative log-power scale at `2^K`. -/
theorem dyadicHalf_isLittleO_logPowerMajorant (δ : ℝ) :
    (fun K : ℕ ↦ (2 : ℝ) ^ (K / 2)) =o[atTop]
      dyadicLogPowerMajorant δ := by
  rw [isLittleO_iff_tendsto]
  · let b : ℝ := Real.log 2 / 2
    have hb : 0 < b := div_pos (Real.log_pos (by norm_num)) (by norm_num)
    have hbase : Tendsto (fun K : ℕ ↦ ((K + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hcore :
        Tendsto
          (fun K : ℕ ↦ (((K + 1 : ℕ) : ℝ) ^ δ) *
            Real.exp (-b * ((K + 1 : ℕ) : ℝ))) atTop (nhds 0) :=
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero δ b hb).comp hbase
    have hq :
        Tendsto
          (fun K : ℕ ↦ (((K + 1 : ℕ) : ℝ) ^ δ) *
            Real.exp (-b * (K : ℝ))) atTop (nhds 0) := by
      convert hcore.mul_const (Real.exp b) using 1
      · funext K
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        push_cast
        ring
      · simp
    apply squeeze_zero
      (g := fun K : ℕ ↦ (((K + 1 : ℕ) : ℝ) ^ δ) *
        Real.exp (-b * (K : ℝ)))
    · intro K
      dsimp [dyadicLogPowerMajorant]
      positivity
    · intro K
      have hhalfcast : ((K / 2 : ℕ) : ℝ) ≤ (K : ℝ) / 2 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
        exact_mod_cast Nat.div_mul_le_self K 2
      have hpown (n : ℕ) :
          (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
        calc
          (2 : ℝ) ^ n = (Real.exp (Real.log 2)) ^ n := by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          _ = Real.exp ((n : ℝ) * Real.log 2) :=
            (Real.exp_nat_mul (Real.log 2) n).symm
      have hpowRatio :
          (2 : ℝ) ^ (K / 2) / (2 : ℝ) ^ K ≤
            Real.exp (-b * (K : ℝ)) := by
        rw [hpown, hpown, ← Real.exp_sub]
        apply Real.exp_le_exp.mpr
        dsimp [b]
        have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        calc
          ((K / 2 : ℕ) : ℝ) * Real.log 2 - (K : ℝ) * Real.log 2
              ≤ ((K : ℝ) / 2) * Real.log 2 - (K : ℝ) * Real.log 2 := by
                gcongr
          _ = -(Real.log 2 / 2) * (K : ℝ) := by ring
      have hratio :
          (2 : ℝ) ^ (K / 2) / dyadicLogPowerMajorant δ K =
            (((K + 1 : ℕ) : ℝ) ^ δ) *
              ((2 : ℝ) ^ (K / 2) / (2 : ℝ) ^ K) := by
        dsimp [dyadicLogPowerMajorant]
        field_simp
      rw [hratio]
      exact mul_le_mul_of_nonneg_left hpowRatio (Real.rpow_nonneg (by positivity) _)
    · exact hq
  · intro K hzero
    have hne : dyadicLogPowerMajorant δ K ≠ 0 := by
      dsimp [dyadicLogPowerMajorant]
      positivity
    exact False.elim (hne hzero)

/-- Quantitative dyadic summation with a common top-scale logarithmic
denominator.  Only blocks in the upper half of the dyadic scales are needed;
the entire lower half is bounded by its ambient interval. -/
theorem exceptionalUpTo_two_pow_isBigO_of_upperHalf_logPower
    (P : ℕ → Prop) {δ C : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ᶠ K : ℕ in atTop, ∀ k ∈ Finset.Ico (K / 2) K,
      ((exceptionalOnDyadicBlock P (2 ^ k)).card : ℝ) ≤
        C * (2 : ℝ) ^ k / (((K + 1 : ℕ) : ℝ) ^ δ)) :
    (fun K : ℕ ↦ ((exceptionalUpTo P (2 ^ K)).card : ℝ))
      =O[atTop] dyadicLogPowerMajorant δ := by
  have hlow := isLittleO_iff.1 (dyadicHalf_isLittleO_logPowerMajorant δ)
    (show (0 : ℝ) < 1 by norm_num)
  apply IsBigO.of_bound (1 + C)
  filter_upwards [hupper, hlow] with K hblocks hsmall
  have hmajorantPos : 0 < dyadicLogPowerMajorant δ K := by
    dsimp [dyadicLogPowerMajorant]
    positivity
  have hsmall' :
      (2 : ℝ) ^ (K / 2) ≤ dyadicLogPowerMajorant δ K := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ (K / 2)),
      one_mul, Real.norm_eq_abs, abs_of_pos hmajorantPos] at hsmall
    exact hsmall
  have hsplitNat := card_exceptionalUpTo_two_pow_le_from P
    (Nat.div_le_self K 2)
  have hsplit :
      ((exceptionalUpTo P (2 ^ K)).card : ℝ) ≤
        ((exceptionalUpTo P (2 ^ (K / 2))).card : ℝ) +
          ∑ k ∈ Finset.Ico (K / 2) K,
            ((exceptionalOnDyadicBlock P (2 ^ k)).card : ℝ) := by
    exact_mod_cast hsplitNat
  have hprefix :
      ((exceptionalUpTo P (2 ^ (K / 2))).card : ℝ) ≤
        (2 : ℝ) ^ (K / 2) := by
    exact_mod_cast card_exceptionalUpTo_le P (2 ^ (K / 2))
  have hpowers :
      (∑ k ∈ Finset.Ico (K / 2) K, (2 : ℝ) ^ k) ≤ (2 : ℝ) ^ K := by
    calc
      (∑ k ∈ Finset.Ico (K / 2) K, (2 : ℝ) ^ k)
          ≤ ∑ k ∈ Finset.range K, (2 : ℝ) ^ k := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro k hk
              exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
            · intro k _ _
              positivity
      _ = (2 : ℝ) ^ K - 1 := by
        have h := geom_sum_mul (2 : ℝ) K
        norm_num at h ⊢
        exact h
      _ ≤ (2 : ℝ) ^ K := by linarith
  have hdenPos : 0 < (((K + 1 : ℕ) : ℝ) ^ δ) := by positivity
  have htail :
      (∑ k ∈ Finset.Ico (K / 2) K,
        ((exceptionalOnDyadicBlock P (2 ^ k)).card : ℝ)) ≤
          C * dyadicLogPowerMajorant δ K := by
    calc
      (∑ k ∈ Finset.Ico (K / 2) K,
          ((exceptionalOnDyadicBlock P (2 ^ k)).card : ℝ))
          ≤ ∑ k ∈ Finset.Ico (K / 2) K,
              C * (2 : ℝ) ^ k / (((K + 1 : ℕ) : ℝ) ^ δ) := by
            exact Finset.sum_le_sum hblocks
      _ = (C / (((K + 1 : ℕ) : ℝ) ^ δ)) *
            ∑ k ∈ Finset.Ico (K / 2) K, (2 : ℝ) ^ k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ ≤ (C / (((K + 1 : ℕ) : ℝ) ^ δ)) * (2 : ℝ) ^ K := by
          exact mul_le_mul_of_nonneg_left hpowers (div_nonneg hC hdenPos.le)
      _ = C * dyadicLogPowerMajorant δ K := by
          dsimp [dyadicLogPowerMajorant]
          ring
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg hmajorantPos.le]
  calc
    ((exceptionalUpTo P (2 ^ K)).card : ℝ)
        ≤ ((exceptionalUpTo P (2 ^ (K / 2))).card : ℝ) +
            ∑ k ∈ Finset.Ico (K / 2) K,
              ((exceptionalOnDyadicBlock P (2 ^ k)).card : ℝ) := hsplit
    _ ≤ (2 : ℝ) ^ (K / 2) + C * dyadicLogPowerMajorant δ K :=
      add_le_add hprefix htail
    _ ≤ dyadicLogPowerMajorant δ K + C * dyadicLogPowerMajorant δ K :=
      add_le_add_left hsmall' _
    _ = (1 + C) * dyadicLogPowerMajorant δ K := by ring

/-- A uniform `O(2^k/(k+1)^δ)` bound on the individual dyadic blocks
preserves the same exponent after summation up to the endpoint `2^K`. -/
theorem exceptionalUpTo_two_pow_isBigO_of_dyadic_logPower
    (P : ℕ → Prop) {δ : ℝ} (hδ : 0 < δ)
    (hlocal :
      (fun k : ℕ ↦ ((exceptionalOnDyadicBlock P (2 ^ k)).card : ℝ))
        =O[atTop] dyadicLogPowerMajorant δ) :
    (fun K : ℕ ↦ ((exceptionalUpTo P (2 ^ K)).card : ℝ))
      =O[atTop] dyadicLogPowerMajorant δ := by
  obtain ⟨c, hc⟩ := hlocal.bound
  rw [eventually_atTop] at hc
  obtain ⟨N, hN⟩ := hc
  let C : ℝ := |c| * (2 : ℝ) ^ δ
  have hC : 0 ≤ C := mul_nonneg (abs_nonneg c) (Real.rpow_nonneg (by norm_num) _)
  apply exceptionalUpTo_two_pow_isBigO_of_upperHalf_logPower P hC
  filter_upwards [eventually_ge_atTop (2 * N)] with K hK
  intro k hk
  have hkN : N ≤ k := by
    have hhalfN : N ≤ K / 2 := by omega
    exact hhalfN.trans (Finset.mem_Ico.mp hk).1
  have hloc := hN k hkN
  have hloc' :
      ((exceptionalOnDyadicBlock P (2 ^ k)).card : ℝ) ≤
        |c| * dyadicLogPowerMajorant δ k := by
    have hmajNonneg : 0 ≤ dyadicLogPowerMajorant δ k := by
      dsimp [dyadicLogPowerMajorant]
      positivity
    calc
      ((exceptionalOnDyadicBlock P (2 ^ k)).card : ℝ)
          = ‖((exceptionalOnDyadicBlock P (2 ^ k)).card : ℝ)‖ :=
            (Real.norm_of_nonneg (Nat.cast_nonneg _)).symm
      _ ≤ c * ‖dyadicLogPowerMajorant δ k‖ := hloc
      _ = c * dyadicLogPowerMajorant δ k := by
        rw [Real.norm_of_nonneg hmajNonneg]
      _ ≤ |c| * dyadicLogPowerMajorant δ k :=
        mul_le_mul_of_nonneg_right (le_abs_self c) hmajNonneg
  have hKkNat : K + 1 ≤ 2 * (k + 1) := by
    have hkhalf := (Finset.mem_Ico.mp hk).1
    omega
  have hKk : (((K + 1 : ℕ) : ℝ)) ≤ 2 * (((k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hKkNat
  have hden : (((K + 1 : ℕ) : ℝ) ^ δ) ≤
      (2 : ℝ) ^ δ * (((k + 1 : ℕ) : ℝ) ^ δ) := by
    calc
      (((K + 1 : ℕ) : ℝ) ^ δ)
          ≤ (2 * (((k + 1 : ℕ) : ℝ))) ^ δ :=
            Real.rpow_le_rpow (by positivity) hKk hδ.le
      _ = (2 : ℝ) ^ δ * (((k + 1 : ℕ) : ℝ) ^ δ) := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
  have hA : 0 < (((k + 1 : ℕ) : ℝ) ^ δ) := by positivity
  have hB : 0 < (((K + 1 : ℕ) : ℝ) ^ δ) := by positivity
  have hcompare :
      dyadicLogPowerMajorant δ k ≤
        (2 : ℝ) ^ δ * (2 : ℝ) ^ k /
          (((K + 1 : ℕ) : ℝ) ^ δ) := by
    dsimp [dyadicLogPowerMajorant]
    apply (le_div_iff₀ hB).2
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hA).2
    calc
      (2 : ℝ) ^ k * (((K + 1 : ℕ) : ℝ) ^ δ)
          ≤ (2 : ℝ) ^ k *
              ((2 : ℝ) ^ δ * (((k + 1 : ℕ) : ℝ) ^ δ)) :=
            mul_le_mul_of_nonneg_left hden (by positivity)
      _ = ((2 : ℝ) ^ δ * (2 : ℝ) ^ k) *
            (((k + 1 : ℕ) : ℝ) ^ δ) := by ring
  calc
    ((exceptionalOnDyadicBlock P (2 ^ k)).card : ℝ)
        ≤ |c| * dyadicLogPowerMajorant δ k := hloc'
    _ ≤ |c| * ((2 : ℝ) ^ δ * (2 : ℝ) ^ k /
          (((K + 1 : ℕ) : ℝ) ^ δ)) :=
      mul_le_mul_of_nonneg_left hcompare (abs_nonneg c)
    _ = C * (2 : ℝ) ^ k / (((K + 1 : ℕ) : ℝ) ^ δ) := by
      dsimp [C]
      ring

/-- A quantitative log-power estimate at powers of two transfers to all
natural cutoffs with the same exponent. -/
theorem hasLogPowerExceptionalBound_of_dyadic_endpoints
    (P : ℕ → Prop) {δ : ℝ} (hδ : 0 < δ)
    (hdyadic :
      (fun K : ℕ ↦ ((exceptionalUpTo P (2 ^ K)).card : ℝ))
        =O[atTop] dyadicLogPowerMajorant δ) :
    HasLogPowerExceptionalBound P δ := by
  obtain ⟨c, hc⟩ := hdyadic.bound
  rw [eventually_atTop] at hc
  obtain ⟨N, hN⟩ := hc
  rw [HasLogPowerExceptionalBound]
  apply IsBigO.of_bound (2 * |c|)
  filter_upwards [eventually_ge_atTop (max 2 (2 ^ N))] with X hX
  let K := Nat.clog 2 X
  have hX_two : 2 ≤ X := (le_max_left _ _).trans hX
  have hXpos : 0 < (X : ℝ) := by positivity
  have hlogXpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hX_pow : X ≤ 2 ^ K := Nat.le_pow_clog (by norm_num) X
  have hN_pow : 2 ^ N ≤ X := (le_max_right _ _).trans hX
  have hNK : N ≤ K :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp
      (hN_pow.trans hX_pow)
  have hKpos : 0 < K := Nat.clog_pos (by norm_num) (by omega)
  have hpow_le : 2 ^ K ≤ 2 * X := by
    have hpred : 2 ^ K.pred < X := by
      dsimp [K]
      exact Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
    rw [← Nat.succ_pred_eq_of_pos hKpos, pow_succ]
    omega
  have hcard :
      ((exceptionalUpTo P X).card : ℝ) ≤
        ((exceptionalUpTo P (2 ^ K)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (exceptionalUpTo_mono P hX_pow)
  have hmajorantPos : 0 < dyadicLogPowerMajorant δ K := by
    dsimp [dyadicLogPowerMajorant]
    positivity
  have hendpoint :
      ((exceptionalUpTo P (2 ^ K)).card : ℝ) ≤
        |c| * dyadicLogPowerMajorant δ K := by
    have hb := hN K hNK
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
      Real.norm_of_nonneg hmajorantPos.le] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_abs_self c) hmajorantPos.le)
  have hlogTwoNonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogTwoLeOne : Real.log 2 ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hlogPow :
      Real.log (((2 ^ K : ℕ) : ℝ)) = (K : ℝ) * Real.log 2 := by
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.log_pow]
  have hlog_le : Real.log (X : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
    calc
      Real.log (X : ℝ) ≤ Real.log (((2 ^ K : ℕ) : ℝ)) := by
        apply Real.log_le_log hXpos
        exact_mod_cast hX_pow
      _ = (K : ℝ) * Real.log 2 := hlogPow
      _ ≤ (K : ℝ) := by
        simpa using mul_le_mul_of_nonneg_left hlogTwoLeOne (Nat.cast_nonneg K)
      _ ≤ ((K + 1 : ℕ) : ℝ) := by norm_num
  have hlogDen :
      (Real.log (X : ℝ)) ^ δ ≤ (((K + 1 : ℕ) : ℝ) ^ δ) :=
    Real.rpow_le_rpow hlogXpos.le hlog_le hδ.le
  have htopDenPos : 0 < (((K + 1 : ℕ) : ℝ) ^ δ) := by positivity
  have hlogDenPos : 0 < (Real.log (X : ℝ)) ^ δ :=
    Real.rpow_pos_of_pos hlogXpos δ
  have hmajorantCompare :
      dyadicLogPowerMajorant δ K ≤
        2 * (X : ℝ) / (Real.log (X : ℝ)) ^ δ := by
    dsimp [dyadicLogPowerMajorant]
    calc
      (2 : ℝ) ^ K / (((K + 1 : ℕ) : ℝ) ^ δ)
          ≤ (2 * (X : ℝ)) / (((K + 1 : ℕ) : ℝ) ^ δ) := by
            apply div_le_div_of_nonneg_right _ htopDenPos.le
            exact_mod_cast hpow_le
      _ ≤ (2 * (X : ℝ)) / (Real.log (X : ℝ)) ^ δ :=
        div_le_div_of_nonneg_left (by positivity) hlogDenPos hlogDen
  have htargetNonneg :
      0 ≤ (X : ℝ) / (Real.log (X : ℝ)) ^ δ :=
    div_nonneg (Nat.cast_nonneg _) hlogDenPos.le
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
    Real.norm_of_nonneg htargetNonneg]
  calc
    ((exceptionalUpTo P X).card : ℝ)
        ≤ ((exceptionalUpTo P (2 ^ K)).card : ℝ) := hcard
    _ ≤ |c| * dyadicLogPowerMajorant δ K := hendpoint
    _ ≤ |c| * (2 * (X : ℝ) / (Real.log (X : ℝ)) ^ δ) :=
      mul_le_mul_of_nonneg_left hmajorantCompare (abs_nonneg c)
    _ = (2 * |c|) * ((X : ℝ) / (Real.log (X : ℝ)) ^ δ) := by ring

/-- **Quantitative dyadic globalization.**  A uniform block estimate
`O(2^k/(k+1)^δ)` with `δ > 0` implies the global estimate
`O(X/(log X)^δ)` with no loss in the logarithmic exponent. -/
theorem hasLogPowerExceptionalBound_of_dyadic_logPower
    (P : ℕ → Prop) {δ : ℝ} (hδ : 0 < δ)
    (hlocal :
      (fun k : ℕ ↦ ((exceptionalOnDyadicBlock P (2 ^ k)).card : ℝ))
        =O[atTop] dyadicLogPowerMajorant δ) :
    HasLogPowerExceptionalBound P δ :=
  hasLogPowerExceptionalBound_of_dyadic_endpoints P hδ
    (exceptionalUpTo_two_pow_isBigO_of_dyadic_logPower P hδ hlocal)

/-- A positive power of the logarithm gives a genuine density saving along
dyadic blocks. -/
theorem dyadicLogPowerMajorant_isLittleO {δ : ℝ} (hδ : 0 < δ) :
    dyadicLogPowerMajorant δ =o[atTop] fun k : ℕ ↦ (2 : ℝ) ^ k := by
  have hbase : Tendsto (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hden : Tendsto (fun k : ℕ ↦ (((k + 1 : ℕ) : ℝ) ^ δ)) atTop atTop :=
    (_root_.tendsto_rpow_atTop hδ).comp hbase
  have hinv : Tendsto (fun k : ℕ ↦ (((k + 1 : ℕ) : ℝ) ^ δ)⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hden
  rw [isLittleO_iff_tendsto]
  · convert hinv using 1
    funext k
    dsimp [dyadicLogPowerMajorant]
    field_simp
  · intro k hk
    exact False.elim ((by positivity : (2 : ℝ) ^ k ≠ 0) hk)

/-- Power-of-logarithm exceptional counts on the individual dyadic blocks
imply the global almost-all statement.  The analytic work in an application
is exactly the `hlocal` hypothesis; the rest is the elementary globalization
proved in this file. -/
theorem forAlmostAll_of_dyadic_logPower_bound
    (P : ℕ → Prop) {δ : ℝ} (hδ : 0 < δ)
    (hlocal :
      (fun k : ℕ ↦ ((exceptionalOnDyadicBlock P (2 ^ k)).card : ℝ))
        =O[atTop] dyadicLogPowerMajorant δ) :
    ForAlmostAllIntegers P := by
  have hlocal' := hlocal.trans_isLittleO (dyadicLogPowerMajorant_isLittleO hδ)
  exact forAlmostAll_of_dyadic_endpoints P
    (exceptionalUpTo_two_pow_isLittleO_of_dyadic P hlocal')

def dyadicGlobalizationModule : ProofModule :=
  { name := "Completion.DyadicGlobalization"
    paperLocation := "End of Section 7.2"
    purpose :=
      "Cover initial intervals by dyadic blocks and globalize log-power exceptional bounds without exponent loss."
    dependsOn :=
      [ "Completion.RealToIntegerExceptions",
        "Completion.PrimeWindowTransfer",
        "Completion.UniqueSmallPrimeFactor",
        "Mathlib finite sums and asymptotics" ]
    status := .proved }

end

end Completion
end ExactSemiprimes
