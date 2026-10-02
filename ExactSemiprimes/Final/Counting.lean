import ExactSemiprimes.Final.BlockVariance
import ExactSemiprimes.Completion.DyadicPrimeBlocks
import ExactSemiprimes.Completion.PrimeWindowTransfer
import ExactSemiprimes.Completion.UniqueSmallPrimeFactor
import ExactSemiprimes.Completion.RealToIntegerExceptions

/-!
# Section 7.2: measure-theoretic and combinatorial bookkeeping

* The block deviation `x ↦ |S_P(x,h)/h - S_P(x,h₁)/h₁|²` is a bounded
  measurable step function, hence integrable on `(X,2X]`.
* Chebyshev's inequality and a union bound over the blocks.
* The sum over buffered blocks of prime-pair counts injects into the
  windowed prime products of `(m, m + (log m)^c]` (unique small prime factor).
-/

namespace ExactSemiprimes
namespace Final

open Filter Real MeasureTheory

noncomputable section

/-! ## Integrability of the block deviation -/

theorem measurable_weightedPrimeProductSum (w : ℕ → ℝ) (P h : ℝ) :
    Measurable (fun x : ℝ ↦ Completion.weightedPrimeProductSum w P x h) := by
  unfold Completion.weightedPrimeProductSum
  refine Finset.measurable_sum _ (fun p _ ↦ ?_)
  -- each prime contributes a function of two floors
  let G : ℕ × ℕ → ℝ := fun q ↦ ∑ n ∈ Finset.Ioc q.1 q.2, w n
  have hG : Measurable G := measurable_of_countable G
  have h1 : Measurable (fun x : ℝ ↦ ⌊x / (p : ℝ)⌋₊) := (measurable_id.div_const _).nat_floor
  have h2 : Measurable (fun x : ℝ ↦ ⌊x / (p : ℝ) + h / (p : ℝ)⌋₊) :=
    ((measurable_id.div_const _).add_const _).nat_floor
  exact hG.comp (h1.prodMk h2)

theorem abs_weightedPrimeProductSum_le (w : ℕ → ℝ) {P x h B : ℝ} (hx : 0 ≤ x)
    (hh : 0 ≤ h) (hxB : x + h ≤ B) :
    |Completion.weightedPrimeProductSum w P x h| ≤
      ∑ _p ∈ dyadicPrimes P, ∑ n ∈ Finset.range (⌊B⌋₊ + 1), |w n| := by
  unfold Completion.weightedPrimeProductSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p hp ↦ ?_))
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have hp1 : (1 : ℝ) ≤ p := by
      have := (Finset.mem_filter.mp hp).2.two_le
      exact_mod_cast (by omega : 1 ≤ p)
    simp only [shortInterval, natOpenClosedInterval, Finset.mem_Ioc] at hn
    rw [Finset.mem_range, Nat.lt_succ_iff]
    refine hn.2.trans (Nat.floor_le_floor ?_)
    have : x / p + h / p ≤ x + h := by
      rw [← add_div]; exact div_le_self (by linarith) hp1
    linarith
  · intro n _ _; exact abs_nonneg _

theorem integrableOn_blockDeviation_sq (w : ℕ → ℝ) (X P h h₁ : ℝ) (hX : 0 ≤ X)
    (hh : 0 < h) (hh₁ : 0 < h₁) :
    IntegrableOn (fun x ↦ |Completion.weightedPrimeProductSum w P x h / h -
        Completion.weightedPrimeProductSum w P x h₁ / h₁| ^ (2 : ℕ))
      (Set.Ioc X (2 * X)) := by
  set M := ∑ p ∈ dyadicPrimes P, ∑ n ∈ Finset.range (⌊2 * X + h⌋₊ + 1), |w n|
  set M₁ := ∑ p ∈ dyadicPrimes P, ∑ n ∈ Finset.range (⌊2 * X + h₁⌋₊ + 1), |w n|
  refine IntegrableOn.of_bound measure_Ioc_lt_top ?_ ((M / h + M₁ / h₁) ^ (2 : ℕ)) ?_
  · exact ((((measurable_weightedPrimeProductSum w P h).div_const h).sub
      ((measurable_weightedPrimeProductSum w P h₁).div_const h₁)).abs.pow_const
        2).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx ↦ ?_)
    have hx0 : 0 ≤ x := by linarith [hx.1]
    have h1 := abs_weightedPrimeProductSum_le w (P := P) hx0 hh.le
      (show x + h ≤ 2 * X + h by linarith [hx.2])
    have h2 := abs_weightedPrimeProductSum_le w (P := P) hx0 hh₁.le
      (show x + h₁ ≤ 2 * X + h₁ by linarith [hx.2])
    rw [Real.norm_eq_abs, abs_pow, abs_abs]
    have hd : |Completion.weightedPrimeProductSum w P x h / h -
        Completion.weightedPrimeProductSum w P x h₁ / h₁| ≤ M / h + M₁ / h₁ := by
      refine (abs_sub _ _).trans ?_
      rw [abs_div, abs_div, abs_of_pos hh, abs_of_pos hh₁]
      exact add_le_add (div_le_div_of_nonneg_right h1 hh.le)
        (div_le_div_of_nonneg_right h2 hh₁.le)
    exact pow_le_pow_left₀ (abs_nonneg _) hd 2

/-! ## Chebyshev and the union bound -/

theorem volume_ge_inter_Ioc_le {f : ℝ → ℝ} {X θ V : ℝ} (hθ : 0 < θ)
    (hint : IntegrableOn f (Set.Ioc X (2 * X))) (hf0 : ∀ x, 0 ≤ f x)
    (hV : (∫ x in Set.Ioc X (2 * X), f x) ≤ V) :
    volume ({x | θ ≤ f x} ∩ Set.Ioc X (2 * X)) ≤ ENNReal.ofReal (V / θ) := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (μ := volume.restrict (Set.Ioc X (2 * X)))
    (Filter.Eventually.of_forall (fun x ↦ hf0 x)) hint θ
  rw [measureReal_def, Measure.restrict_apply' measurableSet_Ioc] at h
  have hfin : volume ({x | θ ≤ f x} ∩ Set.Ioc X (2 * X)) ≠ ⊤ :=
    ((measure_mono Set.inter_subset_right).trans_lt measure_Ioc_lt_top).ne
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  rw [le_div_iff₀ hθ]
  linarith

theorem volume_le_of_subset_biUnion {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    {X θ V : ℝ} {B : Set ℝ} (hθ : 0 < θ)
    (hB : B ⊆ ⋃ i ∈ s, ({x | θ ≤ f i x} ∩ Set.Ioc X (2 * X)))
    (hint : ∀ i ∈ s, IntegrableOn (f i) (Set.Ioc X (2 * X)))
    (hf0 : ∀ i ∈ s, ∀ x, 0 ≤ f i x)
    (hV : ∀ i ∈ s, (∫ x in Set.Ioc X (2 * X), f i x) ≤ V) :
    volume B ≤ (s.card : ENNReal) * ENNReal.ofReal (V / θ) := by
  calc volume B ≤ volume (⋃ i ∈ s, ({x | θ ≤ f i x} ∩ Set.Ioc X (2 * X))) :=
        measure_mono hB
    _ ≤ ∑ i ∈ s, volume ({x | θ ≤ f i x} ∩ Set.Ioc X (2 * X)) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ s, ENNReal.ofReal (V / θ) :=
        Finset.sum_le_sum (fun i hi ↦
          volume_ge_inter_Ioc_le hθ (hint i hi) (hf0 i hi) (hV i hi))
    _ = (s.card : ENNReal) * ENNReal.ofReal (V / θ) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## Disjointness of the buffered blocks -/

theorem disjoint_dyadicPrimes_of_two_mul_le {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (h2 : 2 * P ≤ Q) : Disjoint (dyadicPrimes P) (dyadicPrimes Q) := by
  rw [Finset.disjoint_left]
  intro n hnP hnQ
  have h1 := (mem_dyadicInterval hP).mp (Finset.mem_filter.mp hnP).1
  have h2' := (mem_dyadicInterval hQ).mp (Finset.mem_filter.mp hnQ).1
  linarith [h1.2, h2'.1]

theorem bufferedDyadicScales_pairwiseDisjoint {c Δ X : ℝ} (hX : 1 < X) :
    ((Completion.bufferedDyadicScales c Δ X : Finset ℝ) : Set ℝ).PairwiseDisjoint
      dyadicPrimes := by
  intro P hP Q hQ hPQ
  rcases Completion.mem_bufferedDyadicScales.mp hP with ⟨i, -, rfl⟩
  rcases Completion.mem_bufferedDyadicScales.mp hQ with ⟨j, -, rfl⟩
  have hA : 0 < (Real.log X) ^ Completion.bufferedPrimeLowerExponent c Δ :=
    Real.rpow_pos_of_pos (Real.log_pos hX) _
  have hij : i ≠ j := by rintro rfl; exact hPQ rfl
  show Disjoint _ _
  rcases lt_or_gt_of_ne hij with h | h
  · apply disjoint_dyadicPrimes_of_two_mul_le (by positivity) (by positivity)
    have : (2 : ℝ) ^ (i + 1 + 1) ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc 2 * ((Real.log X) ^ Completion.bufferedPrimeLowerExponent c Δ * 2 ^ (i + 1)) =
          (Real.log X) ^ Completion.bufferedPrimeLowerExponent c Δ * 2 ^ (i + 1 + 1) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hA.le
  · apply Disjoint.symm
    apply disjoint_dyadicPrimes_of_two_mul_le (by positivity) (by positivity)
    have : (2 : ℝ) ^ (j + 1 + 1) ≤ 2 ^ (i + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    calc 2 * ((Real.log X) ^ Completion.bufferedPrimeLowerExponent c Δ * 2 ^ (j + 1)) =
          (Real.log X) ^ Completion.bufferedPrimeLowerExponent c Δ * 2 ^ (j + 1 + 1) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this hA.le

/-! ## From prime pairs over the blocks to windowed prime products -/

/-- The prime pairs `(p,q)`, `p` in one of the disjoint blocks, `y < pq ≤ y+h`,
inject (via `(p,q) ↦ pq`) into the windowed prime products in
`(m, m+H]`, because the small factor of `pq` is unique. -/
theorem sum_blocks_primeIndicator_le_windowedCount
    {s : Finset ℝ} {y h H L' U' Ucut Xr : ℝ} {m : ℕ}
    (hdisj : (s : Set ℝ).PairwiseDisjoint dyadicPrimes)
    (hmy : (m : ℝ) ≤ y) (hyH : y + h ≤ (m : ℝ) + H) (hh : 0 ≤ h) (hXr : Xr ≤ y)
    (hwin : ∀ P ∈ s, ∀ p ∈ dyadicPrimes P, L' < (p : ℝ) ∧ (p : ℝ) ≤ U')
    (hcut : ∀ P ∈ s, ∀ p ∈ dyadicPrimes P, (p : ℝ) ≤ Ucut) (hcut2 : Ucut ^ 2 ≤ Xr) :
    (∑ P ∈ s, Completion.weightedPrimeProductSum Completion.realPrimeIndicator P y h) ≤
      (windowedPrimeProductCount (m : ℝ) H L' U' : ℝ) := by
  have hy0 : 0 ≤ y := le_trans (Nat.cast_nonneg m) hmy
  have h1 : (∑ P ∈ s, Completion.weightedPrimeProductSum Completion.realPrimeIndicator P y h) =
      ∑ p ∈ s.biUnion dyadicPrimes,
        (((shortInterval (y / p) (h / p)).filter Nat.Prime).card : ℝ) := by
    rw [Finset.sum_biUnion hdisj]
    apply Finset.sum_congr rfl; intro P _
    apply Finset.sum_congr rfl; intro p _
    simp only [Completion.realPrimeIndicator]
    rw [Finset.sum_boole]
  rw [h1, ← Nat.cast_sum, ← Finset.card_sigma]
  unfold windowedPrimeProductCount intervalCount
  norm_cast
  apply Finset.card_le_card_of_injOn (fun q ↦ q.1 * q.2)
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_biUnion] at hq
    obtain ⟨⟨P, hPs, hpP⟩, hqA⟩ := hq
    rw [Finset.mem_filter] at hqA
    obtain ⟨hqI, hqprime⟩ := hqA
    have hpprime : q.1.Prime := (Finset.mem_filter.mp hpP).2
    have hp0 : (0 : ℝ) < q.1 := by exact_mod_cast hpprime.pos
    rw [shortInterval, mem_natOpenClosedInterval (by positivity) (by positivity)] at hqI
    have hlo : y < (q.1 : ℝ) * q.2 := by
      have := (div_lt_iff₀ hp0).mp hqI.1; linarith
    have hhi : (q.1 : ℝ) * q.2 ≤ y + h := by
      have h' : (q.2 : ℝ) ≤ (y + h) / q.1 := by rw [add_div]; exact hqI.2
      have := (le_div_iff₀ hp0).mp h'; linarith
    simp only [Finset.mem_coe, Finset.mem_filter]
    refine ⟨?_, ⟨q.1, q.2, hpprime, hqprime, rfl, hwin P hPs q.1 hpP⟩⟩
    rw [shortInterval, mem_natOpenClosedInterval (Nat.cast_nonneg m) (by linarith)]
    push_cast
    constructor <;> linarith
  · intro q hq q' hq' heq
    simp only at heq
    rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_biUnion] at hq hq'
    obtain ⟨⟨P, hPs, hpP⟩, hqA⟩ := hq
    obtain ⟨⟨P', hPs', hpP'⟩, hqA'⟩ := hq'
    have hpprime : q.1.Prime := (Finset.mem_filter.mp hpP).2
    have hpprime' : q'.1.Prime := (Finset.mem_filter.mp hpP').2
    have hqprime : q.2.Prime := (Finset.mem_filter.mp hqA).2
    have hqI := (Finset.mem_filter.mp hqA).1
    have hp0 : (0 : ℝ) < q.1 := by exact_mod_cast hpprime.pos
    rw [shortInterval, mem_natOpenClosedInterval (by positivity) (by positivity)] at hqI
    have hlo : Xr < ((q.1 * q.2 : ℕ) : ℝ) := by
      have := (div_lt_iff₀ hp0).mp hqI.1; push_cast; linarith
    have hr : q'.1 = q.1 :=
      Completion.unique_prime_factor_le_cutoff hlo hcut2 hpprime hqprime hpprime' rfl
        (hcut P hPs q.1 hpP) (hcut P' hPs' q'.1 hpP') ⟨q'.2, heq⟩
    have hs : q.2 = q'.2 := by
      rw [hr] at heq
      exact Nat.eq_of_mul_eq_mul_left hpprime.pos heq
    exact Sigma.ext hr.symm (heq_of_eq hs)

end

end Final
end ExactSemiprimes
