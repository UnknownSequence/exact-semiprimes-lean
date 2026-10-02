import ExactSemiprimes.Hybrid.LowerRangeExponents
import ExactSemiprimes.Hybrid.UpperRangeExponents
import ExactSemiprimes.Hybrid.DiscreteToMeasure
import ExactSemiprimes.Hybrid.NormalizeCoefficients

/-! # Hybrid large-value density estimate (paper Lemma 4.3) -/

namespace ExactSemiprimes
namespace Hybrid

noncomputable section

/-! ## Divisor-subpower specialization -/

/-- Fully quantified local target for the standard global estimate
`d(n)^B \ll_{B,ρ} n^ρ`. -/
def GlobalDivisorSubpowerStatement : Prop :=
  ∀ B ρ : ℝ, 0 ≤ B → 0 < ρ →
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ n : ℕ, 0 < n →
        (divisorCount n : ℝ) ^ B ≤ D * (n : ℝ) ^ ρ

/-! ### An elementary square-root divisor bound

The involution `d ↦ n / d` pairs every divisor above `sqrt n` with a
divisor at most `sqrt n`.  We formalize that pairing explicitly rather than
importing any analytic estimate for the divisor function.
-/

/-- The elementary bound `d(n) ≤ 2 ⌊√n⌋` for positive natural `n`.
The proof partitions the divisors at `Nat.sqrt n`; on the upper part,
division into `n` is injective and lands back below the square root. -/
theorem divisorCount_le_two_mul_sqrt (n : ℕ) (hn : 0 < n) :
    divisorCount n ≤ 2 * Nat.sqrt n := by
  classical
  let low := n.divisors.filter fun d ↦ d ≤ Nat.sqrt n
  let high := n.divisors.filter fun d ↦ ¬ d ≤ Nat.sqrt n
  have hlow : low.card ≤ Nat.sqrt n := by
    have hcard : low.card ≤ (Finset.range (Nat.sqrt n)).card := by
      refine Finset.card_le_card_of_injOn (fun d : ℕ ↦ d - 1) ?_ ?_
      · intro d hd
        have hd' := Finset.mem_filter.mp hd
        have hdpos : 0 < d := Nat.pos_of_mem_divisors hd'.1
        simpa using (Finset.mem_range.mpr
          (show d - 1 < Nat.sqrt n by omega))
      · intro d hd e he hde
        have hd' := Finset.mem_filter.mp hd
        have he' := Finset.mem_filter.mp he
        have hdpos : 0 < d := Nat.pos_of_mem_divisors hd'.1
        have hepos : 0 < e := Nat.pos_of_mem_divisors he'.1
        change d - 1 = e - 1 at hde
        omega
    simpa using hcard
  have hhigh : high.card ≤ Nat.sqrt n := by
    have hcard : high.card ≤ (Finset.range (Nat.sqrt n)).card := by
      refine Finset.card_le_card_of_injOn (fun d : ℕ ↦ n / d - 1) ?_ ?_
      · intro d hd
        have hd' := Finset.mem_filter.mp hd
        have hdvd : d ∣ n := (Nat.mem_divisors.mp hd'.1).1
        have hmul : d * (n / d) = n := Nat.mul_div_cancel' hdvd
        have hquotientLe : n / d ≤ Nat.sqrt n := by
          rcases Nat.le_sqrt_of_eq_mul hmul.symm with hsmall | hsmall
          · exact False.elim (hd'.2 hsmall)
          · exact hsmall
        have hquotientPos : 0 < n / d := by
          by_contra h
          have hzero : n / d = 0 := Nat.eq_zero_of_not_pos h
          rw [hzero, mul_zero] at hmul
          omega
        simpa using (Finset.mem_range.mpr
          (show n / d - 1 < Nat.sqrt n by omega))
      · intro d hd e he hde
        have hd' := Finset.mem_filter.mp hd
        have he' := Finset.mem_filter.mp he
        have hdvd : d ∣ n := (Nat.mem_divisors.mp hd'.1).1
        have hevd : e ∣ n := (Nat.mem_divisors.mp he'.1).1
        have hmulD : d * (n / d) = n := Nat.mul_div_cancel' hdvd
        have hmulE : e * (n / e) = n := Nat.mul_div_cancel' hevd
        have hquotientDPos : 0 < n / d := by
          by_contra h
          have hzero : n / d = 0 := Nat.eq_zero_of_not_pos h
          rw [hzero, mul_zero] at hmulD
          omega
        have hquotientEPos : 0 < n / e := by
          by_contra h
          have hzero : n / e = 0 := Nat.eq_zero_of_not_pos h
          rw [hzero, mul_zero] at hmulE
          omega
        change n / d - 1 = n / e - 1 at hde
        have hquotient : n / d = n / e := by omega
        have hproduct : d * (n / d) = e * (n / d) := by
          calc
            d * (n / d) = n := hmulD
            _ = e * (n / e) := hmulE.symm
            _ = e * (n / d) := by rw [hquotient]
        exact mul_right_cancel₀ (ne_of_gt hquotientDPos) hproduct
    simpa using hcard
  have hpartition : low.card + high.card = n.divisors.card := by
    simpa [low, high] using
      (Finset.card_filter_add_card_filter_not
        (s := n.divisors) (p := fun d ↦ d ≤ Nat.sqrt n))
  rw [divisorCount, ← hpartition]
  omega

/-- Real form of the elementary square-root bound. -/
theorem divisorCount_cast_le_two_mul_rpow_half (n : ℕ) (hn : 0 < n) :
    (divisorCount n : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
  have hnat := divisorCount_le_two_mul_sqrt n hn
  have hcast : (divisorCount n : ℝ) ≤ 2 * (Nat.sqrt n : ℝ) := by
    exact_mod_cast hnat
  have hsqrt : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast Nat.sqrt_le' n
  calc
    (divisorCount n : ℝ) ≤ 2 * (Nat.sqrt n : ℝ) := hcast
    _ ≤ 2 * Real.sqrt (n : ℝ) := by gcongr
    _ = 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]

/-! ### Local prime-power estimates for the full subpower argument

For a fixed positive exponent `δ`, Bernoulli's inequality gives one constant
which controls every local divisor factor `k+1` by `p^(δk)`, uniformly for
all primes `p`.  Once `p^δ ≥ 2`, the constant can be removed.  These are the
two local ingredients in the usual finite-small-primes/large-primes proof.
-/

/-- The elementary inequality `k+1 ≤ 2^k`. -/
theorem nat_succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        k.succ + 1 ≤ 2 * (k + 1) := by omega
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ k.succ := by simp [pow_succ, Nat.mul_comm]

/-- A convenient uniform coefficient for the local estimate at the finitely
many small primes. -/
def divisorLocalExponentConstant (δ : ℝ) : ℝ :=
  max 1 (((2 : ℝ) ^ δ - 1)⁻¹)

theorem one_le_divisorLocalExponentConstant (δ : ℝ) :
    1 ≤ divisorLocalExponentConstant δ :=
  le_max_left _ _

/-- Uniform local estimate for every base at least two.  The coefficient
depends only on `δ`, not on the base or on the exponent. -/
theorem succ_cast_le_divisorLocalExponentConstant_mul_rpow
    {δ : ℝ} (hδ : 0 < δ) {p k : ℕ} (hp : 2 ≤ p) :
    ((k + 1 : ℕ) : ℝ) ≤
      divisorLocalExponentConstant δ * (p : ℝ) ^ (δ * (k : ℝ)) := by
  let q : ℝ := (2 : ℝ) ^ δ
  let A : ℝ := divisorLocalExponentConstant δ
  have hq : 1 < q := by
    exact Real.one_lt_rpow (by norm_num) hδ
  have hqsub : 0 < q - 1 := sub_pos.mpr hq
  have hA : 1 ≤ A := one_le_divisorLocalExponentConstant δ
  have hinvA : (q - 1)⁻¹ ≤ A := by
    exact le_max_right _ _
  have hAq : 1 ≤ A * (q - 1) := by
    calc
      1 = (q - 1)⁻¹ * (q - 1) := (inv_mul_cancel₀ hqsub.ne').symm
      _ ≤ A * (q - 1) := mul_le_mul_of_nonneg_right hinvA hqsub.le
  have hbern : 1 + (k : ℝ) * (q - 1) ≤ q ^ k := by
    exact one_add_mul_sub_le_pow (by linarith [hq]) k
  have hlocal : ((k + 1 : ℕ) : ℝ) ≤ A * q ^ k := by
    calc
      ((k + 1 : ℕ) : ℝ) = 1 + (k : ℝ) := by
        push_cast
        ring
      _ ≤ A * (1 + (k : ℝ) * (q - 1)) := by
        nlinarith [show 0 ≤ (k : ℝ) from Nat.cast_nonneg k]
      _ ≤ A * q ^ k :=
        mul_le_mul_of_nonneg_left hbern (le_trans zero_le_one hA)
  have hbase : q ≤ (p : ℝ) ^ δ := by
    exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp) hδ.le
  have hpow : q ^ k ≤ ((p : ℝ) ^ δ) ^ k := by
    exact pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) δ) hbase k
  calc
    ((k + 1 : ℕ) : ℝ) ≤ A * q ^ k := hlocal
    _ ≤ A * ((p : ℝ) ^ δ) ^ k :=
      mul_le_mul_of_nonneg_left hpow (le_trans zero_le_one hA)
    _ = divisorLocalExponentConstant δ *
        (p : ℝ) ^ (δ * (k : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]

/-- At a base whose `δ`-power is at least two, the local coefficient is one. -/
theorem succ_cast_le_rpow_of_two_le_rpow
    {δ : ℝ} {p k : ℕ} (hlarge : (2 : ℝ) ≤ (p : ℝ) ^ δ) :
    ((k + 1 : ℕ) : ℝ) ≤ (p : ℝ) ^ (δ * (k : ℝ)) := by
  have hnat : k + 1 ≤ 2 ^ k := nat_succ_le_two_pow k
  have hcast : ((k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ k := by
    exact_mod_cast hnat
  have hpow : (2 : ℝ) ^ k ≤ ((p : ℝ) ^ δ) ^ k := by
    exact pow_le_pow_left₀ (by norm_num) hlarge k
  calc
    ((k + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ k := hcast
    _ ≤ ((p : ℝ) ^ δ) ^ k := hpow
    _ = (p : ℝ) ^ (δ * (k : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]

/-- The finite-small-primes/large-primes product estimate at a chosen cutoff.
The cutoff hypothesis says precisely that every prime at least `P` has
`δ`-power at least two. -/
theorem divisorCount_cast_le_localConstant_pow_mul_rpow
    {δ : ℝ} (hδ : 0 < δ) {P n : ℕ}
    (hP : (2 : ℝ) ^ (1 / δ) ≤ (P : ℝ)) (hn : 0 < n) :
    (divisorCount n : ℝ) ≤
      divisorLocalExponentConstant δ ^ P * (n : ℝ) ^ δ := by
  classical
  let S : Finset ℕ := n.primeFactors
  let small : Finset ℕ := S.filter fun p ↦ p < P
  let large : Finset ℕ := S.filter fun p ↦ ¬ p < P
  let A : ℝ := divisorLocalExponentConstant δ
  let term : ℕ → ℝ := fun p ↦
    (p : ℝ) ^ (δ * (n.factorization p : ℝ))
  let factor : ℕ → ℝ := fun p ↦ ((n.factorization p + 1 : ℕ) : ℝ)
  have hA : 1 ≤ A := one_le_divisorLocalExponentConstant δ
  have hsmallCard : small.card ≤ P := by
    have hsubset : small ⊆ Finset.range P := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      exact Finset.mem_range.mpr hp'.2
    simpa using Finset.card_le_card hsubset
  have hsmall :
      (∏ p ∈ small, factor p) ≤ ∏ p ∈ small, A * term p := by
    apply Finset.prod_le_prod₀
    · intro p hp
      dsimp [factor]
      positivity
    · intro p hp
      have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
      have hpPrime : p.Prime := by
        exact Nat.prime_of_mem_primeFactors hpS
      exact succ_cast_le_divisorLocalExponentConstant_mul_rpow hδ hpPrime.two_le
  have hlarge :
      (∏ p ∈ large, factor p) ≤ ∏ p ∈ large, term p := by
    apply Finset.prod_le_prod₀
    · intro p hp
      dsimp [factor]
      positivity
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpP : P ≤ p := by omega
      have hbase : (2 : ℝ) ^ (1 / δ) ≤ (p : ℝ) := by
        exact hP.trans (by exact_mod_cast hpP)
      have hlargeBase : (2 : ℝ) ≤ (p : ℝ) ^ δ := by
        calc
          (2 : ℝ) = ((2 : ℝ) ^ (1 / δ)) ^ δ := by
            rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδ.ne',
              Real.rpow_one]
          _ ≤ (p : ℝ) ^ δ :=
            Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) hbase hδ.le
      exact succ_cast_le_rpow_of_two_le_rpow hlargeBase
  have hpartitionFactor :
      (∏ p ∈ small, factor p) * (∏ p ∈ large, factor p) =
        ∏ p ∈ S, factor p := by
    simpa [small, large] using
      (Finset.prod_filter_mul_prod_filter_not S (fun p ↦ p < P) factor)
  have hpartitionTerm :
      (∏ p ∈ small, term p) * (∏ p ∈ large, term p) =
        ∏ p ∈ S, term p := by
    simpa [small, large] using
      (Finset.prod_filter_mul_prod_filter_not S (fun p ↦ p < P) term)
  have hfactorization :
      (∏ p ∈ S, term p) = (n : ℝ) ^ δ := by
    calc
      (∏ p ∈ S, term p) =
          ∏ p ∈ S, ((p : ℝ) ^ n.factorization p) ^ δ := by
        apply Finset.prod_congr rfl
        intro p hp
        dsimp [term]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
        congr 1
        ring
      _ = (∏ p ∈ S, (p : ℝ) ^ n.factorization p) ^ δ := by
        exact Real.finsetProd_rpow S
          (fun p ↦ (p : ℝ) ^ n.factorization p)
          (by intro p hp; positivity) δ
      _ = (n : ℝ) ^ δ := by
        have hreconstruct :
            (n : ℝ) = ∏ p ∈ S, (p : ℝ) ^ n.factorization p := by
          exact_mod_cast Nat.prod_primeFactors_pow_factorization hn.ne'
        rw [← hreconstruct]
  have hdivisorProduct :
      (divisorCount n : ℝ) = ∏ p ∈ S, factor p := by
    have hcard := Nat.card_divisors hn.ne'
    dsimp [S, factor]
    rw [divisorCount]
    exact_mod_cast hcard
  have hsmallExpanded :
      (∏ p ∈ small, A * term p) = A ^ small.card * ∏ p ∈ small, term p := by
    rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hApow : A ^ small.card ≤ A ^ P :=
    pow_le_pow_right₀ hA hsmallCard
  calc
    (divisorCount n : ℝ) = ∏ p ∈ S, factor p := hdivisorProduct
    _ = (∏ p ∈ small, factor p) * (∏ p ∈ large, factor p) :=
      hpartitionFactor.symm
    _ ≤ (∏ p ∈ small, A * term p) * (∏ p ∈ large, term p) := by
      exact mul_le_mul hsmall hlarge
        (Finset.prod_nonneg fun p hp ↦ by positivity)
        (Finset.prod_nonneg fun p hp ↦ by positivity)
    _ = A ^ small.card * ((∏ p ∈ small, term p) *
        (∏ p ∈ large, term p)) := by rw [hsmallExpanded]; ring
    _ = A ^ small.card * (∏ p ∈ S, term p) := by rw [hpartitionTerm]
    _ ≤ A ^ P * (∏ p ∈ S, term p) := by
      exact mul_le_mul_of_nonneg_right hApow
        (Finset.prod_nonneg fun p hp ↦ by positivity)
    _ = divisorLocalExponentConstant δ ^ P * (n : ℝ) ^ δ := by
      rw [hfactorization]

/-- The divisor function itself is subpower: for every `δ>0` there is a
constant, independent of `n`, bounding `d(n)` by that constant times `n^δ`.
This is the standard finite-small-primes/large-primes argument in a form
which can be raised to an arbitrary real power below. -/
theorem divisorCount_cast_subpower {δ : ℝ} (hδ : 0 < δ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ n : ℕ, 0 < n →
      (divisorCount n : ℝ) ≤ D * (n : ℝ) ^ δ := by
  obtain ⟨P, hP⟩ := exists_nat_ge ((2 : ℝ) ^ (1 / δ))
  refine ⟨divisorLocalExponentConstant δ ^ P,
    one_le_pow₀ (one_le_divisorLocalExponentConstant δ), ?_⟩
  intro n hn
  exact divisorCount_cast_le_localConstant_pow_mul_rpow hδ hP hn

/-- The full standard global estimate `d(n)^B \ll_{B,ρ} n^ρ`, including
the edge case `B=0`.  For `B>0`, apply the preceding divisor bound with
`δ=ρ/B` and raise it to the real power `B`. -/
theorem globalDivisorSubpower : GlobalDivisorSubpowerStatement := by
  intro B ρ hB hρ
  rcases hB.eq_or_lt with rfl | hBpos
  · refine ⟨1, le_rfl, ?_⟩
    intro n hn
    have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    simpa using Real.one_le_rpow hnOne hρ.le
  · let δ : ℝ := ρ / B
    have hδ : 0 < δ := div_pos hρ hBpos
    obtain ⟨E, hE, hbound⟩ := divisorCount_cast_subpower hδ
    refine ⟨E ^ B, Real.one_le_rpow hE hB, ?_⟩
    intro n hn
    have hnNonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hdivNonneg : (0 : ℝ) ≤ (divisorCount n : ℝ) := Nat.cast_nonneg _
    have hraise :
        (divisorCount n : ℝ) ^ B ≤ (E * (n : ℝ) ^ δ) ^ B :=
      Real.rpow_le_rpow hdivNonneg (hbound n hn) hB
    calc
      (divisorCount n : ℝ) ^ B ≤ (E * (n : ℝ) ^ δ) ^ B := hraise
      _ = E ^ B * (n : ℝ) ^ (δ * B) := by
        rw [Real.mul_rpow (le_trans zero_le_one hE)
          (Real.rpow_nonneg hnNonneg δ), ← Real.rpow_mul hnNonneg]
      _ = E ^ B * (n : ℝ) ^ ρ := by
        have hδB : δ * B = ρ := by
          dsimp [δ]
          field_simp [hBpos.ne']
        rw [hδB]

/-- The strongest global divisor-subpower range supplied by the elementary
square-root pairing alone: the desired estimate holds with `D = 2^B`
whenever `rho ≥ B/2`.  This includes all `rho>0` when `B=0`, but does not
by itself cover the genuinely subpower range `0 < rho < B/2`; that range is
handled by `globalDivisorSubpower` above. -/
theorem globalDivisorSubpower_of_half_exponent
    {B ρ : ℝ} (hB : 0 ≤ B) (hρ : B / 2 ≤ ρ) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ n : ℕ, 0 < n →
        (divisorCount n : ℝ) ^ B ≤ D * (n : ℝ) ^ ρ := by
  refine ⟨(2 : ℝ) ^ B, Real.one_le_rpow (by norm_num) hB, ?_⟩
  intro n hn
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hdivNonneg : 0 ≤ (divisorCount n : ℝ) := Nat.cast_nonneg _
  have hraise :
      (divisorCount n : ℝ) ^ B ≤
        (2 * (n : ℝ) ^ (1 / 2 : ℝ)) ^ B :=
    Real.rpow_le_rpow hdivNonneg
      (divisorCount_cast_le_two_mul_rpow_half n hn) hB
  have hbase : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  calc
    (divisorCount n : ℝ) ^ B
        ≤ (2 * (n : ℝ) ^ (1 / 2 : ℝ)) ^ B := hraise
    _ = (2 : ℝ) ^ B * (n : ℝ) ^ (B / 2) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (Real.rpow_nonneg hbase _), ← Real.rpow_mul hbase]
      congr 2
      ring
    _ ≤ (2 : ℝ) ^ B * (n : ℝ) ^ ρ := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hnOne hρ)
        (Real.rpow_nonneg (by norm_num) B)

/-- The global divisor-subpower statement supplies one constant `D`,
independent of the dyadic scale `N`, satisfying the explicit dyadic predicate
used in `NormalizeCoefficients`. -/
theorem exists_uniform_hasDyadicDivisorSubpowerBound
    (hglobal : GlobalDivisorSubpowerStatement)
    {B ρ : ℝ} (hB : 0 ≤ B) (hρ : 0 < ρ) :
    ∃ D : ℝ, 1 ≤ D ∧
      ∀ N : ℕ, HasDyadicDivisorSubpowerBound B D ρ N := by
  obtain ⟨D, hD, hglobalD⟩ := hglobal B ρ hB hρ
  refine ⟨D, hD, ?_⟩
  intro N n hnLower hnUpper
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hnLower
  have hnCastUpper : (n : ℝ) ≤ (2 : ℝ) * (N : ℝ) := by
    exact_mod_cast hnUpper
  have hpow : (n : ℝ) ^ ρ ≤ ((2 : ℝ) * (N : ℝ)) ^ ρ :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) hnCastUpper (le_of_lt hρ)
  calc
    (divisorCount n : ℝ) ^ B ≤ D * (n : ℝ) ^ ρ :=
      hglobalD n hnpos
    _ ≤ D * ((2 : ℝ) * (N : ℝ)) ^ ρ :=
      mul_le_mul_of_nonneg_left hpow (by linarith)
    _ = D * (2 : ℝ) ^ ρ * (N : ℝ) ^ ρ := by
      rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg N)]
      ring

/-! ## Absorbing the fixed normalization constant -/

/-- Every fixed real constant is eventually at most `N^ρ` when `ρ>0`.
The statement is along natural-number cutoffs, exactly as needed for the
normalization scale. -/
theorem eventually_const_le_natCast_rpow (K : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ N : ℕ in Filter.atTop, K ≤ (N : ℝ) ^ ρ := by
  exact ((tendsto_rpow_atTop hρ).comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop K

/-- In particular, the fixed paper constant `K=A₀D2^ρ` is absorbed by a
second factor `N^ρ` for all sufficiently large `N`. -/
theorem eventually_guthMaynardK_le_natCast_rpow
    (A₀ D ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      guthMaynardK A₀ D ρ ≤ (N : ℝ) ^ ρ :=
  eventually_const_le_natCast_rpow (guthMaynardK A₀ D ρ) hρ

/-! ## The logarithmic length parameter -/

/-- The exponent `η = log N / log T` used to convert powers of `N` into
powers of `T`. -/
def logarithmicLengthExponent (T N : ℝ) : ℝ :=
  Real.log N / Real.log T

/-- For `T>1` and `N>0`, the logarithmic length exponent satisfies the exact
identity `N=T^η`. -/
theorem eq_rpow_logarithmicLengthExponent {T N : ℝ}
    (hT : 1 < T) (hN : 0 < N) :
    N = T ^ logarithmicLengthExponent T N := by
  have hTpos : 0 < T := lt_trans zero_lt_one hT
  have hlogT : Real.log T ≠ 0 := ne_of_gt (Real.log_pos hT)
  rw [Real.rpow_def_of_pos hTpos, logarithmicLengthExponent]
  have hmul : Real.log T * (Real.log N / Real.log T) = Real.log N := by
    field_simp [hlogT]
  rw [hmul, Real.exp_log hN]

/-- Bounds by powers of `T` become the same bounds on
`η=log N/log T`. -/
theorem logarithmicLengthExponent_bounds
    {T N α β : ℝ} (hT : 1 < T) (hN : 0 < N)
    (hLower : T ^ α ≤ N) (hUpper : N ≤ T ^ β) :
    α ≤ logarithmicLengthExponent T N ∧
      logarithmicLengthExponent T N ≤ β := by
  have hη := eq_rpow_logarithmicLengthExponent hT hN
  constructor
  · apply (Real.rpow_le_rpow_left_iff hT).mp
    rwa [← hη]
  · apply (Real.rpow_le_rpow_left_iff hT).mp
    rwa [← hη]

/-- Exact conversion of an arbitrary power of `N` to a power of `T`. -/
theorem rpow_eq_rpow_logarithmicLengthExponent_mul
    {T N q : ℝ} (hT : 1 < T) (hN : 0 < N) :
    N ^ q = T ^ (logarithmicLengthExponent T N * q) := by
  calc
    N ^ q = (T ^ logarithmicLengthExponent T N) ^ q :=
      congrArg (fun x : ℝ ↦ x ^ q)
        (eq_rpow_logarithmicLengthExponent hT hN)
    _ = T ^ (logarithmicLengthExponent T N * q) :=
      (Real.rpow_mul (le_of_lt (lt_trans zero_lt_one hT))
        (logarithmicLengthExponent T N) q).symm

/-! ## Exact application of the two Guth--Maynard inputs

The next two lemmas contain no exponent comparison.  They verify, in Lean,
that coefficient normalization, phase reflection, and the divisor-subpower
bound put the original Dirichlet polynomial into precisely the hypotheses of
the two cited large-values statements.  Thus their conclusions are the raw
three-term bounds with amplitude `N^(1-σ-2ρ)`.
-/

/-- A fixed-constant slice of the main Guth--Maynard theorem.  Naming this
predicate makes the uniformity of the final constant explicit. -/
def GuthMaynardMainBoundAt (δ C : ℝ) : Prop :=
  ∀ (T V : ℝ) (N : ℕ) (b : ℕ → ℂ) (R : Finset ℝ),
    1 ≤ T → 1 ≤ N → 0 < V →
    (∀ n ∈ closedDyadicInterval N, ‖b n‖ ≤ 1) →
    (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
    IsOneSpaced (↑R : Set ℝ) →
    (∀ t ∈ R, V ≤ ‖oscillatoryDirichletSum b N t‖) →
    (R.card : ℝ) ≤ C * T ^ δ *
      (((N : ℝ) ^ (2 : ℕ)) / V ^ (2 : ℕ) +
        (N : ℝ) ^ (18 / 5 : ℝ) / V ^ (4 : ℕ) +
        T * (N : ℝ) ^ (12 / 5 : ℝ) / V ^ (4 : ℕ))

/-- A fixed-constant slice of the long-polynomial Guth--Maynard theorem. -/
def GuthMaynardLongBoundAt (δ C : ℝ) : Prop :=
  ∀ (T V varrho : ℝ) (N : ℕ) (b : ℕ → ℂ) (R : Finset ℝ),
    1 ≤ T → 1 ≤ N → 0 < V →
    T ^ (5 / 6 : ℝ) ≤ (N : ℝ) → (N : ℝ) ≤ T →
    7 / 10 ≤ varrho → V = (N : ℝ) ^ varrho →
    (∀ n ∈ closedDyadicInterval N, ‖b n‖ ≤ 1) →
    (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
    IsOneSpaced (↑R : Set ℝ) →
    (∀ t ∈ R, V ≤ ‖oscillatoryDirichletSum b N t‖) →
    (R.card : ℝ) ≤ C * T ^ δ *
      ((N : ℝ) ^ (2 - 2 * varrho) +
        T ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 - 4 * varrho) +
        T ^ ((30 * varrho - 21) / 5) *
          (N : ℝ) ^ ((46 - 60 * varrho) / 5))

/-- Fixed-constant version of the normalized main-theorem application. -/
theorem normalized_guthMaynardMain_bound_at
    {δ C T A B D ρ σ : ℝ} {N : ℕ} {a : ℕ → ℂ} {R : Finset ℝ}
    (hGM : GuthMaynardMainBoundAt δ C)
    (hT : 1 ≤ T) (hN : 1 ≤ N) (hA : 0 < A) (hD : 0 < D)
    (ha : IsDivisorBoundedByConstant B A a)
    (hdiv : HasDyadicDivisorSubpowerBound B D ρ N)
    (hR : IsOneSpaced (↑R : Set ℝ))
    (hRT : ∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T)
    (hKle : guthMaynardK A D ρ ≤ (N : ℝ) ^ ρ)
    (hlarge : ∀ t ∈ R,
      (N : ℝ) ^ (-σ) <
        ‖dyadicDirichletPolynomial a (N : ℝ) (onePlusIT t)‖) :
    (R.card : ℝ) ≤ C * T ^ δ *
      (((N : ℝ) ^ (2 : ℕ)) /
          ((N : ℝ) ^ (1 - σ - 2 * ρ)) ^ (2 : ℕ) +
        (N : ℝ) ^ (18 / 5 : ℝ) /
          ((N : ℝ) ^ (1 - σ - 2 * ρ)) ^ (4 : ℕ) +
        T * (N : ℝ) ^ (12 / 5 : ℝ) /
          ((N : ℝ) ^ (1 - σ - 2 * ρ)) ^ (4 : ℕ)) := by
  let b : ℕ → ℂ := phaseReflectedCoefficient
    (guthMaynardNormalizedCoefficient a A D N ρ) T
  let R' : Finset ℝ := reflectedHeightFinset T R
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hVpos : 0 < (N : ℝ) ^ (1 - σ - 2 * ρ) :=
    Real.rpow_pos_of_pos hNpos _
  have hb : ∀ n ∈ closedDyadicInterval N, ‖b n‖ ≤ 1 := by
    intro n hn
    exact norm_phaseReflected_guthMaynardNormalizedCoefficient_le_one
      hN hA hD ha hdiv hn
  have hR'T : ∀ u ∈ R', u ∈ Set.Icc (0 : ℝ) T :=
    mem_reflectedHeightFinset_Icc hRT
  have hR'spaced : IsOneSpaced (↑R' : Set ℝ) :=
    isOneSpaced_reflectedHeightFinset hR
  have hR'large : ∀ u ∈ R',
      (N : ℝ) ^ (1 - σ - 2 * ρ) ≤ ‖oscillatoryDirichletSum b N u‖ := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    exact le_of_lt (largeValue_threshold_of_normalized_phase_reflection
      hN hA hD hKle (hlarge t ht))
  have hbound := hGM T ((N : ℝ) ^ (1 - σ - 2 * ρ)) N b R'
    hT hN hVpos hb hR'T hR'spaced hR'large
  simpa [R', card_reflectedHeightFinset] using hbound

/-- Fixed-constant version of the normalized long-theorem application. -/
theorem normalized_guthMaynardLong_bound_at
    {δ C T A B D ρ σ : ℝ} {N : ℕ} {a : ℕ → ℂ} {R : Finset ℝ}
    (hGM : GuthMaynardLongBoundAt δ C)
    (hT : 1 ≤ T) (hN : 1 ≤ N)
    (hNlower : T ^ (5 / 6 : ℝ) ≤ (N : ℝ))
    (hNupper : (N : ℝ) ≤ T)
    (hamplitude : 7 / 10 ≤ 1 - σ - 2 * ρ)
    (hA : 0 < A) (hD : 0 < D)
    (ha : IsDivisorBoundedByConstant B A a)
    (hdiv : HasDyadicDivisorSubpowerBound B D ρ N)
    (hR : IsOneSpaced (↑R : Set ℝ))
    (hRT : ∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T)
    (hKle : guthMaynardK A D ρ ≤ (N : ℝ) ^ ρ)
    (hlarge : ∀ t ∈ R,
      (N : ℝ) ^ (-σ) <
        ‖dyadicDirichletPolynomial a (N : ℝ) (onePlusIT t)‖) :
    (R.card : ℝ) ≤ C * T ^ δ *
      ((N : ℝ) ^ (2 - 2 * (1 - σ - 2 * ρ)) +
        T ^ (1 / 2 : ℝ) *
          (N : ℝ) ^ (3 - 4 * (1 - σ - 2 * ρ)) +
        T ^ ((30 * (1 - σ - 2 * ρ) - 21) / 5) *
          (N : ℝ) ^ ((46 - 60 * (1 - σ - 2 * ρ)) / 5)) := by
  let b : ℕ → ℂ := phaseReflectedCoefficient
    (guthMaynardNormalizedCoefficient a A D N ρ) T
  let R' : Finset ℝ := reflectedHeightFinset T R
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hVpos : 0 < (N : ℝ) ^ (1 - σ - 2 * ρ) :=
    Real.rpow_pos_of_pos hNpos _
  have hb : ∀ n ∈ closedDyadicInterval N, ‖b n‖ ≤ 1 := by
    intro n hn
    exact norm_phaseReflected_guthMaynardNormalizedCoefficient_le_one
      hN hA hD ha hdiv hn
  have hR'T : ∀ u ∈ R', u ∈ Set.Icc (0 : ℝ) T :=
    mem_reflectedHeightFinset_Icc hRT
  have hR'spaced : IsOneSpaced (↑R' : Set ℝ) :=
    isOneSpaced_reflectedHeightFinset hR
  have hR'large : ∀ u ∈ R',
      (N : ℝ) ^ (1 - σ - 2 * ρ) ≤ ‖oscillatoryDirichletSum b N u‖ := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    exact le_of_lt (largeValue_threshold_of_normalized_phase_reflection
      hN hA hD hKle (hlarge t ht))
  have hbound := hGM T ((N : ℝ) ^ (1 - σ - 2 * ρ))
    (1 - σ - 2 * ρ) N b R' hT hN hVpos hNlower hNupper
    hamplitude rfl hb hR'T hR'spaced hR'large
  simpa [R', card_reflectedHeightFinset] using hbound

/-- The main Guth--Maynard theorem applied to the normalized and reflected
coefficient sequence. -/
theorem normalized_guthMaynardMain_bound
    (hGM : GuthMaynardMainLargeValuesStatement)
    {δ T A B D ρ σ : ℝ} {N : ℕ} {a : ℕ → ℂ} {R : Finset ℝ}
    (hδ : 0 < δ) (hT : 1 ≤ T) (hN : 1 ≤ N)
    (hA : 0 < A) (hD : 0 < D)
    (ha : IsDivisorBoundedByConstant B A a)
    (hdiv : HasDyadicDivisorSubpowerBound B D ρ N)
    (hR : IsOneSpaced (↑R : Set ℝ))
    (hRT : ∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T)
    (hKle : guthMaynardK A D ρ ≤ (N : ℝ) ^ ρ)
    (hlarge : ∀ t ∈ R,
      (N : ℝ) ^ (-σ) <
        ‖dyadicDirichletPolynomial a (N : ℝ) (onePlusIT t)‖) :
    ∃ C : ℝ, 0 < C ∧
      (R.card : ℝ) ≤ C * T ^ δ *
        (((N : ℝ) ^ (2 : ℕ)) /
            ((N : ℝ) ^ (1 - σ - 2 * ρ)) ^ (2 : ℕ) +
          (N : ℝ) ^ (18 / 5 : ℝ) /
            ((N : ℝ) ^ (1 - σ - 2 * ρ)) ^ (4 : ℕ) +
          T * (N : ℝ) ^ (12 / 5 : ℝ) /
            ((N : ℝ) ^ (1 - σ - 2 * ρ)) ^ (4 : ℕ)) := by
  obtain ⟨C, hC, hGMδ⟩ := hGM δ hδ
  let b : ℕ → ℂ := phaseReflectedCoefficient
    (guthMaynardNormalizedCoefficient a A D N ρ) T
  let R' : Finset ℝ := reflectedHeightFinset T R
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hVpos : 0 < (N : ℝ) ^ (1 - σ - 2 * ρ) :=
    Real.rpow_pos_of_pos hNpos _
  have hb : ∀ n ∈ closedDyadicInterval N, ‖b n‖ ≤ 1 := by
    intro n hn
    exact norm_phaseReflected_guthMaynardNormalizedCoefficient_le_one
      hN hA hD ha hdiv hn
  have hR'T : ∀ u ∈ R', u ∈ Set.Icc (0 : ℝ) T := by
    exact mem_reflectedHeightFinset_Icc hRT
  have hR'spaced : IsOneSpaced (↑R' : Set ℝ) := by
    exact isOneSpaced_reflectedHeightFinset hR
  have hR'large : ∀ u ∈ R',
      (N : ℝ) ^ (1 - σ - 2 * ρ) ≤ ‖oscillatoryDirichletSum b N u‖ := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    exact le_of_lt (largeValue_threshold_of_normalized_phase_reflection
      hN hA hD hKle (hlarge t ht))
  refine ⟨C, hC, ?_⟩
  have hbound := hGMδ T ((N : ℝ) ^ (1 - σ - 2 * ρ)) N b R'
    hT hN hVpos hb hR'T hR'spaced hR'large
  simpa [R', card_reflectedHeightFinset] using hbound

/-- The long-polynomial Guth--Maynard estimate applied to the same normalized
and reflected coefficient sequence. -/
theorem normalized_guthMaynardLong_bound
    (hGM : GuthMaynardLongPolynomialStatement)
    {δ T A B D ρ σ : ℝ} {N : ℕ} {a : ℕ → ℂ} {R : Finset ℝ}
    (hδ : 0 < δ) (hT : 1 ≤ T) (hN : 1 ≤ N)
    (hNlower : T ^ (5 / 6 : ℝ) ≤ (N : ℝ))
    (hNupper : (N : ℝ) ≤ T)
    (hamplitude : 7 / 10 ≤ 1 - σ - 2 * ρ)
    (hA : 0 < A) (hD : 0 < D)
    (ha : IsDivisorBoundedByConstant B A a)
    (hdiv : HasDyadicDivisorSubpowerBound B D ρ N)
    (hR : IsOneSpaced (↑R : Set ℝ))
    (hRT : ∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T)
    (hKle : guthMaynardK A D ρ ≤ (N : ℝ) ^ ρ)
    (hlarge : ∀ t ∈ R,
      (N : ℝ) ^ (-σ) <
        ‖dyadicDirichletPolynomial a (N : ℝ) (onePlusIT t)‖) :
    ∃ C : ℝ, 0 < C ∧
      (R.card : ℝ) ≤ C * T ^ δ *
        ((N : ℝ) ^ (2 - 2 * (1 - σ - 2 * ρ)) +
          T ^ (1 / 2 : ℝ) *
            (N : ℝ) ^ (3 - 4 * (1 - σ - 2 * ρ)) +
          T ^ ((30 * (1 - σ - 2 * ρ) - 21) / 5) *
            (N : ℝ) ^ ((46 - 60 * (1 - σ - 2 * ρ)) / 5)) := by
  obtain ⟨C, hC, hGMδ⟩ := hGM δ hδ
  let b : ℕ → ℂ := phaseReflectedCoefficient
    (guthMaynardNormalizedCoefficient a A D N ρ) T
  let R' : Finset ℝ := reflectedHeightFinset T R
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hVpos : 0 < (N : ℝ) ^ (1 - σ - 2 * ρ) :=
    Real.rpow_pos_of_pos hNpos _
  have hb : ∀ n ∈ closedDyadicInterval N, ‖b n‖ ≤ 1 := by
    intro n hn
    exact norm_phaseReflected_guthMaynardNormalizedCoefficient_le_one
      hN hA hD ha hdiv hn
  have hR'T : ∀ u ∈ R', u ∈ Set.Icc (0 : ℝ) T := by
    exact mem_reflectedHeightFinset_Icc hRT
  have hR'spaced : IsOneSpaced (↑R' : Set ℝ) := by
    exact isOneSpaced_reflectedHeightFinset hR
  have hR'large : ∀ u ∈ R',
      (N : ℝ) ^ (1 - σ - 2 * ρ) ≤ ‖oscillatoryDirichletSum b N u‖ := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    exact le_of_lt (largeValue_threshold_of_normalized_phase_reflection
      hN hA hD hKle (hlarge t ht))
  refine ⟨C, hC, ?_⟩
  have hbound := hGMδ T ((N : ℝ) ^ (1 - σ - 2 * ρ))
    (1 - σ - 2 * ρ) N b R' hT hN hVpos hNlower hNupper
    hamplitude rfl hb hR'T hR'spaced hR'large
  simpa [R', card_reflectedHeightFinset] using hbound

/-! ## Algebraic reduction of the raw three-term bounds -/

/-- First term in the main estimate after substituting the normalized
amplitude. -/
theorem main_first_term_identity {x σ ρ : ℝ} (hx : 0 < x) :
    x ^ (2 : ℕ) / (x ^ (1 - σ - 2 * ρ)) ^ (2 : ℕ) =
      x ^ (2 * σ + 4 * ρ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul hx.le, ← Real.rpow_sub hx]
  congr 1
  ring

/-- Second term in the main estimate after substituting the normalized
amplitude. -/
theorem main_second_term_identity {x σ ρ : ℝ} (hx : 0 < x) :
    x ^ (18 / 5 : ℝ) / (x ^ (1 - σ - 2 * ρ)) ^ (4 : ℕ) =
      x ^ (4 * σ - 2 / 5 + 8 * ρ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_sub hx]
  congr 1
  ring

/-- Third `N`-power in the main estimate after substituting the normalized
amplitude. -/
theorem main_third_term_identity {x σ ρ : ℝ} (hx : 0 < x) :
    x ^ (12 / 5 : ℝ) / (x ^ (1 - σ - 2 * ρ)) ^ (4 : ℕ) =
      x ^ (4 * σ - 8 / 5 + 8 * ρ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_sub hx]
  congr 1
  ring

/-- All three `N`-exponents in the long-polynomial estimate simplify to the
forms used in `UpperRangeExponents`. -/
theorem long_exponent_identities (σ ρ : ℝ) :
    2 - 2 * (1 - σ - 2 * ρ) = 2 * σ + 4 * ρ ∧
      3 - 4 * (1 - σ - 2 * ρ) = -1 + 4 * σ + 8 * ρ ∧
      (46 - 60 * (1 - σ - 2 * ρ)) / 5 =
        (-14 + 60 * σ) / 5 + 24 * ρ ∧
      (30 * (1 - σ - 2 * ρ) - 21) / 5 =
        (9 - 30 * σ) / 5 - 12 * ρ := by
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

/-- The main-estimate summand is exactly the sum encoded by the lower-range
exponent functions once `N=T^η`. -/
theorem main_terms_eq_lowerRange_powers
    {T N η σ ρ : ℝ} (hT : 1 < T) (hN : 0 < N)
    (hη : N = T ^ η) :
    N ^ (2 : ℕ) / (N ^ (1 - σ - 2 * ρ)) ^ (2 : ℕ) +
        N ^ (18 / 5 : ℝ) / (N ^ (1 - σ - 2 * ρ)) ^ (4 : ℕ) +
        T * N ^ (12 / 5 : ℝ) /
          (N ^ (1 - σ - 2 * ρ)) ^ (4 : ℕ) =
      T ^ LowerRange.firstExponent η σ ρ +
        T ^ LowerRange.secondExponent η σ ρ +
        T ^ LowerRange.thirdExponent η σ ρ := by
  rw [main_first_term_identity hN, main_second_term_identity hN,
    mul_div_assoc, main_third_term_identity hN, hη]
  rw [← Real.rpow_mul (le_of_lt (lt_trans zero_lt_one hT)),
    ← Real.rpow_mul (le_of_lt (lt_trans zero_lt_one hT)),
    ← Real.rpow_mul (le_of_lt (lt_trans zero_lt_one hT))]
  have hthird :
      T * T ^ (η * (4 * σ - 8 / 5 + 8 * ρ)) =
        T ^ (1 + η * (4 * σ - 8 / 5 + 8 * ρ)) := by
    calc
      T * T ^ (η * (4 * σ - 8 / 5 + 8 * ρ)) =
          T ^ (1 : ℝ) * T ^ (η * (4 * σ - 8 / 5 + 8 * ρ)) := by
            rw [Real.rpow_one]
      _ = T ^ (1 + η * (4 * σ - 8 / 5 + 8 * ρ)) :=
        (Real.rpow_add (lt_trans zero_lt_one hT) _ _).symm
  rw [hthird]
  simp only [LowerRange.firstExponent, LowerRange.secondExponent,
    LowerRange.thirdExponent]

/-- The long-estimate summand is bounded by the sum encoded by the
upper-range exponent functions.  The only loss is the discarded favourable
factor `T^(-12ρ)`. -/
theorem long_terms_le_upperRange_powers
    {T N η σ ρ : ℝ} (hT : 1 ≤ T) (_hN : 0 < N)
    (hη : N = T ^ η) (hρ : 0 ≤ ρ) :
    N ^ (2 - 2 * (1 - σ - 2 * ρ)) +
        T ^ (1 / 2 : ℝ) * N ^ (3 - 4 * (1 - σ - 2 * ρ)) +
        T ^ ((30 * (1 - σ - 2 * ρ) - 21) / 5) *
          N ^ ((46 - 60 * (1 - σ - 2 * ρ)) / 5) ≤
      T ^ UpperRange.firstExponent η σ ρ +
        T ^ UpperRange.secondExponent η σ ρ +
        T ^ UpperRange.thirdExponent η σ ρ := by
  rcases long_exponent_identities σ ρ with ⟨h1, h2, h3, h4⟩
  rw [h1, h2, h3, h4, hη]
  rw [← Real.rpow_mul (by positivity : 0 ≤ T),
    ← Real.rpow_mul (by positivity : 0 ≤ T),
    ← Real.rpow_mul (by positivity : 0 ≤ T)]
  have hdrop :
      T ^ ((9 - 30 * σ) / 5 - 12 * ρ) ≤
        T ^ ((9 - 30 * σ) / 5) := by
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hthirdNonneg :
      0 ≤ T ^ (η * ((-14 + 60 * σ) / 5 + 24 * ρ)) := by positivity
  calc
    T ^ (η * (2 * σ + 4 * ρ)) +
          T ^ (1 / 2 : ℝ) * T ^ (η * (-1 + 4 * σ + 8 * ρ)) +
          T ^ ((9 - 30 * σ) / 5 - 12 * ρ) *
            T ^ (η * ((-14 + 60 * σ) / 5 + 24 * ρ))
        ≤ T ^ (η * (2 * σ + 4 * ρ)) +
          T ^ (1 / 2 : ℝ) * T ^ (η * (-1 + 4 * σ + 8 * ρ)) +
          T ^ ((9 - 30 * σ) / 5) *
            T ^ (η * ((-14 + 60 * σ) / 5 + 24 * ρ)) := by
              gcongr
    _ = T ^ UpperRange.firstExponent η σ ρ +
          T ^ UpperRange.secondExponent η σ ρ +
          T ^ UpperRange.thirdExponent η σ ρ := by
      rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hT),
        ← Real.rpow_add (lt_of_lt_of_le zero_lt_one hT)]
      simp only [UpperRange.firstExponent, UpperRange.secondExponent,
        UpperRange.thirdExponent]

/-- Three power terms, each below a common exponent, are absorbed into one
power with the explicit constant three. -/
theorem three_rpow_terms_le
    {T e₁ e₂ e₃ q : ℝ} (hT : 1 ≤ T)
    (h₁ : e₁ ≤ q) (h₂ : e₂ ≤ q) (h₃ : e₃ ≤ q) :
    T ^ e₁ + T ^ e₂ + T ^ e₃ ≤ 3 * T ^ q := by
  have hpow₁ := Real.rpow_le_rpow_of_exponent_le hT h₁
  have hpow₂ := Real.rpow_le_rpow_of_exponent_le hT h₂
  have hpow₃ := Real.rpow_le_rpow_of_exponent_le hT h₃
  linarith

/-- Absorb the common Guth--Maynard factor `T^δ` after all three exponent
terms save at least `δ+κ` from the target exponent. -/
theorem absorb_three_power_terms
    {C T δ κ q e₁ e₂ e₃ : ℝ}
    (hC : 0 ≤ C) (hT : 1 ≤ T)
    (h₁ : e₁ ≤ q - δ - κ)
    (h₂ : e₂ ≤ q - δ - κ)
    (h₃ : e₃ ≤ q - δ - κ) :
    C * T ^ δ * (T ^ e₁ + T ^ e₂ + T ^ e₃) ≤
      (3 * C) * T ^ (q - κ) := by
  have hsum := three_rpow_terms_le hT h₁ h₂ h₃
  have hfactor : 0 ≤ C * T ^ δ :=
    mul_nonneg hC (Real.rpow_nonneg (by linarith) _)
  calc
    C * T ^ δ * (T ^ e₁ + T ^ e₂ + T ^ e₃)
        ≤ C * T ^ δ * (3 * T ^ (q - δ - κ)) :=
          mul_le_mul_of_nonneg_left hsum hfactor
    _ = (3 * C) * (T ^ δ * T ^ (q - δ - κ)) := by ring
    _ = (3 * C) * T ^ (q - κ) := by
      rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hT)]
      congr 2
      ring

/-! ## Closed lower- and upper-length branches -/

/-- The complete lower-length branch, conditional only on the fully typed
main Guth--Maynard theorem and the explicit normalization hypotheses.  The
choices are `ρ=δ=ε²/4` and `κ=ε²/2`. -/
theorem lowerRange_normalized_density_bound
    (hGM : GuthMaynardMainLargeValuesStatement)
    {ε T A B D σ : ℝ} {N : ℕ} {a : ℕ → ℂ} {R : Finset ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 1000)
    (hT : 1 < T) (hN : 1 ≤ N)
    (hNlower : T ^ (9 / 11 - 10 * ε) ≤ (N : ℝ))
    (hNupper : (N : ℝ) ≤ T ^ (5 / 6 : ℝ))
    (hσlo : 10 * ε ≤ σ) (hσhi : σ ≤ 17 / 70 - 6 * ε)
    (hA : 0 < A) (hD : 0 < D)
    (ha : IsDivisorBoundedByConstant B A a)
    (hdiv : HasDyadicDivisorSubpowerBound B D (ε ^ 2 / 4) N)
    (hR : IsOneSpaced (↑R : Set ℝ))
    (hRT : ∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T)
    (hKle : guthMaynardK A D (ε ^ 2 / 4) ≤
      (N : ℝ) ^ (ε ^ 2 / 4))
    (hlarge : ∀ t ∈ R,
      (N : ℝ) ^ (-σ) <
        ‖dyadicDirichletPolynomial a (N : ℝ) (onePlusIT t)‖) :
    ∃ C : ℝ, 0 < C ∧
      (R.card : ℝ) ≤ C * T ^ (2 * σ - ε ^ 2 / 2) := by
  let ρ : ℝ := ε ^ 2 / 4
  let η : ℝ := logarithmicLengthExponent T (N : ℝ)
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hηeq : (N : ℝ) = T ^ η := by
    exact eq_rpow_logarithmicLengthExponent hT hNpos
  have hηbounds :
      9 / 11 - 10 * ε ≤ η ∧ η ≤ 5 / 6 := by
    exact logarithmicLengthExponent_bounds hT hNpos hNlower hNupper
  have hρle : ρ ≤ ε ^ 2 := by
    dsimp [ρ]
    nlinarith [sq_nonneg ε]
  have hmargins := LowerRange.explicit_lower_range_margins
    hε0 hε hηbounds.1 hηbounds.2 hσlo hσhi hρ0 hρle
  have hepsSubpower : ε ^ 2 ≤ ε / 1000 := by
    have hp : 0 ≤ ε * (1 / 1000 - ε) :=
      mul_nonneg (le_of_lt hε0) (sub_nonneg.mpr hε)
    nlinarith
  have hcommonHalf : 3 * ε ^ 2 / 4 ≤ ε / 2 := by
    nlinarith
  have hcommonFixed : 3 * ε ^ 2 / 4 ≤ 1 / 210 := by
    nlinarith
  have h₁ : LowerRange.firstExponent η σ ρ ≤
      LowerRange.targetExponent σ - ρ - ε ^ 2 / 2 := by
    dsimp [ρ]
    nlinarith [hmargins.1]
  have h₂ : LowerRange.secondExponent η σ ρ ≤
      LowerRange.targetExponent σ - ρ - ε ^ 2 / 2 := by
    dsimp [ρ]
    nlinarith [hmargins.2.1]
  have h₃ : LowerRange.thirdExponent η σ ρ ≤
      LowerRange.targetExponent σ - ρ - ε ^ 2 / 2 := by
    dsimp [ρ]
    nlinarith [hmargins.2.2]
  obtain ⟨C, hC, hraw⟩ := normalized_guthMaynardMain_bound hGM
    hρpos (le_of_lt hT) hN hA hD ha hdiv hR hRT hKle hlarge
  rw [main_terms_eq_lowerRange_powers hT hNpos hηeq] at hraw
  refine ⟨3 * C, mul_pos (by norm_num) hC, hraw.trans ?_⟩
  have habsorb := absorb_three_power_terms (le_of_lt hC) (le_of_lt hT)
    h₁ h₂ h₃
  simpa [ρ, LowerRange.targetExponent] using habsorb

/-- The complete upper-length branch, now using the long-polynomial
Guth--Maynard estimate.  It has the same explicit choices
`ρ=δ=ε²/4`, `κ=ε²/2`. -/
theorem upperRange_normalized_density_bound
    (hGM : GuthMaynardLongPolynomialStatement)
    {ε T A B D σ : ℝ} {N : ℕ} {a : ℕ → ℂ} {R : Finset ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 1000)
    (hT : 1 < T) (hN : 1 ≤ N)
    (hNlower : T ^ (5 / 6 : ℝ) ≤ (N : ℝ))
    (hNupper : (N : ℝ) ≤ T ^ (1 - ε / 10))
    (hσlo : 10 * ε ≤ σ) (hσhi : σ ≤ 17 / 70 - 6 * ε)
    (hA : 0 < A) (hD : 0 < D)
    (ha : IsDivisorBoundedByConstant B A a)
    (hdiv : HasDyadicDivisorSubpowerBound B D (ε ^ 2 / 4) N)
    (hR : IsOneSpaced (↑R : Set ℝ))
    (hRT : ∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T)
    (hKle : guthMaynardK A D (ε ^ 2 / 4) ≤
      (N : ℝ) ^ (ε ^ 2 / 4))
    (hlarge : ∀ t ∈ R,
      (N : ℝ) ^ (-σ) <
        ‖dyadicDirichletPolynomial a (N : ℝ) (onePlusIT t)‖) :
    ∃ C : ℝ, 0 < C ∧
      (R.card : ℝ) ≤ C * T ^ (2 * σ - ε ^ 2 / 2) := by
  let ρ : ℝ := ε ^ 2 / 4
  let η : ℝ := logarithmicLengthExponent T (N : ℝ)
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hηeq : (N : ℝ) = T ^ η := by
    exact eq_rpow_logarithmicLengthExponent hT hNpos
  have hηbounds : 5 / 6 ≤ η ∧ η ≤ 1 - ε / 10 := by
    exact logarithmicLengthExponent_bounds hT hNpos hNlower hNupper
  have hεhundred : ε ≤ 1 / 100 := by linarith
  have hσzero : σ ≤ UpperRange.sigmaZero := by
    dsimp [UpperRange.sigmaZero]
    linarith
  have hamplitude : 7 / 10 ≤ 1 - σ - 2 * ρ := by
    exact UpperRange.legal_amplitude_exponent (le_of_lt hε0)
      hεhundred hσzero (by dsimp [ρ]; exact le_rfl)
  have hmargins := UpperRange.explicit_upper_range_margins
    hε0 hεhundred hηbounds.1 hηbounds.2 hσlo hσzero hρ0
      (by dsimp [ρ]; exact le_rfl)
  have hepsSubpower : ε ^ 2 ≤ ε / 1000 := by
    have hp : 0 ≤ ε * (1 / 1000 - ε) :=
      mul_nonneg (le_of_lt hε0) (sub_nonneg.mpr hε)
    nlinarith
  have hcommonFixed : 3 * ε ^ 2 / 4 ≤ 1 / 210 := by
    nlinarith
  have h₁ : UpperRange.firstExponent η σ ρ ≤
      UpperRange.targetExponent σ - ρ - ε ^ 2 / 2 := by
    dsimp [ρ]
    nlinarith [hmargins.1]
  have h₂ : UpperRange.secondExponent η σ ρ ≤
      UpperRange.targetExponent σ - ρ - ε ^ 2 / 2 := by
    dsimp [ρ]
    nlinarith [hmargins.2.1]
  have h₃ : UpperRange.thirdExponent η σ ρ ≤
      UpperRange.targetExponent σ - ρ - ε ^ 2 / 2 := by
    dsimp [ρ]
    nlinarith [hmargins.2.2]
  have hNleT : (N : ℝ) ≤ T := by
    have hexponent : T ^ (1 - ε / 10) ≤ T ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hT) (by linarith)
    simpa using hNupper.trans hexponent
  obtain ⟨C, hC, hraw⟩ := normalized_guthMaynardLong_bound hGM
    hρpos (le_of_lt hT) hN hNlower hNleT hamplitude hA hD ha hdiv
      hR hRT hKle hlarge
  have hterms := long_terms_le_upperRange_powers
    (σ := σ) (le_of_lt hT) hNpos hηeq hρ0
  have hfactor : 0 ≤ C * T ^ ρ := by positivity
  have hconverted :
      (R.card : ℝ) ≤ C * T ^ ρ *
        (T ^ UpperRange.firstExponent η σ ρ +
          T ^ UpperRange.secondExponent η σ ρ +
          T ^ UpperRange.thirdExponent η σ ρ) :=
    hraw.trans (mul_le_mul_of_nonneg_left hterms hfactor)
  refine ⟨3 * C, mul_pos (by norm_num) hC, hconverted.trans ?_⟩
  have habsorb := absorb_three_power_terms (le_of_lt hC) (le_of_lt hT)
    h₁ h₂ h₃
  simpa [ρ, UpperRange.targetExponent] using habsorb

/-- Fixed-constant lower branch.  This is the uniform form used to assemble
the quantifier order of `HybridDiscreteDensityStatement`. -/
theorem lowerRange_normalized_density_bound_at
    {ε T A B D σ C : ℝ} {N : ℕ} {a : ℕ → ℂ} {R : Finset ℝ}
    (hGM : GuthMaynardMainBoundAt (ε ^ 2 / 4) C)
    (hC : 0 < C)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 1000)
    (hT : 1 < T) (hN : 1 ≤ N)
    (hNlower : T ^ (9 / 11 - 10 * ε) ≤ (N : ℝ))
    (hNupper : (N : ℝ) ≤ T ^ (5 / 6 : ℝ))
    (hσlo : 10 * ε ≤ σ) (hσhi : σ ≤ 17 / 70 - 6 * ε)
    (hA : 0 < A) (hD : 0 < D)
    (ha : IsDivisorBoundedByConstant B A a)
    (hdiv : HasDyadicDivisorSubpowerBound B D (ε ^ 2 / 4) N)
    (hR : IsOneSpaced (↑R : Set ℝ))
    (hRT : ∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T)
    (hKle : guthMaynardK A D (ε ^ 2 / 4) ≤
      (N : ℝ) ^ (ε ^ 2 / 4))
    (hlarge : ∀ t ∈ R,
      (N : ℝ) ^ (-σ) <
        ‖dyadicDirichletPolynomial a (N : ℝ) (onePlusIT t)‖) :
    (R.card : ℝ) ≤ (3 * C) * T ^ (2 * σ - ε ^ 2 / 2) := by
  let ρ : ℝ := ε ^ 2 / 4
  let η : ℝ := logarithmicLengthExponent T (N : ℝ)
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hηeq : (N : ℝ) = T ^ η :=
    eq_rpow_logarithmicLengthExponent hT hNpos
  have hηbounds : 9 / 11 - 10 * ε ≤ η ∧ η ≤ 5 / 6 :=
    logarithmicLengthExponent_bounds hT hNpos hNlower hNupper
  have hρle : ρ ≤ ε ^ 2 := by dsimp [ρ]; nlinarith [sq_nonneg ε]
  have hmargins := LowerRange.explicit_lower_range_margins
    hε0 hε hηbounds.1 hηbounds.2 hσlo hσhi hρ0 hρle
  have hepsSubpower : ε ^ 2 ≤ ε / 1000 := by
    have hp : 0 ≤ ε * (1 / 1000 - ε) :=
      mul_nonneg (le_of_lt hε0) (sub_nonneg.mpr hε)
    nlinarith
  have hcommonHalf : 3 * ε ^ 2 / 4 ≤ ε / 2 := by nlinarith
  have hcommonFixed : 3 * ε ^ 2 / 4 ≤ 1 / 210 := by nlinarith
  have h₁ : LowerRange.firstExponent η σ ρ ≤
      LowerRange.targetExponent σ - ρ - ε ^ 2 / 2 := by
    dsimp [ρ]; nlinarith [hmargins.1]
  have h₂ : LowerRange.secondExponent η σ ρ ≤
      LowerRange.targetExponent σ - ρ - ε ^ 2 / 2 := by
    dsimp [ρ]; nlinarith [hmargins.2.1]
  have h₃ : LowerRange.thirdExponent η σ ρ ≤
      LowerRange.targetExponent σ - ρ - ε ^ 2 / 2 := by
    dsimp [ρ]; nlinarith [hmargins.2.2]
  have hraw := normalized_guthMaynardMain_bound_at hGM
    (le_of_lt hT) hN hA hD ha hdiv hR hRT hKle hlarge
  rw [main_terms_eq_lowerRange_powers hT hNpos hηeq] at hraw
  exact hraw.trans (by
    have habsorb := absorb_three_power_terms (le_of_lt hC)
      (le_of_lt hT) h₁ h₂ h₃
    simpa [ρ, LowerRange.targetExponent] using habsorb)

/-- Fixed-constant upper branch, in the corresponding uniform form. -/
theorem upperRange_normalized_density_bound_at
    {ε T A B D σ C : ℝ} {N : ℕ} {a : ℕ → ℂ} {R : Finset ℝ}
    (hGM : GuthMaynardLongBoundAt (ε ^ 2 / 4) C)
    (hC : 0 < C)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 1000)
    (hT : 1 < T) (hN : 1 ≤ N)
    (hNlower : T ^ (5 / 6 : ℝ) ≤ (N : ℝ))
    (hNupper : (N : ℝ) ≤ T ^ (1 - ε / 10))
    (hσlo : 10 * ε ≤ σ) (hσhi : σ ≤ 17 / 70 - 6 * ε)
    (hA : 0 < A) (hD : 0 < D)
    (ha : IsDivisorBoundedByConstant B A a)
    (hdiv : HasDyadicDivisorSubpowerBound B D (ε ^ 2 / 4) N)
    (hR : IsOneSpaced (↑R : Set ℝ))
    (hRT : ∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T)
    (hKle : guthMaynardK A D (ε ^ 2 / 4) ≤
      (N : ℝ) ^ (ε ^ 2 / 4))
    (hlarge : ∀ t ∈ R,
      (N : ℝ) ^ (-σ) <
        ‖dyadicDirichletPolynomial a (N : ℝ) (onePlusIT t)‖) :
    (R.card : ℝ) ≤ (3 * C) * T ^ (2 * σ - ε ^ 2 / 2) := by
  let ρ : ℝ := ε ^ 2 / 4
  let η : ℝ := logarithmicLengthExponent T (N : ℝ)
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hηeq : (N : ℝ) = T ^ η :=
    eq_rpow_logarithmicLengthExponent hT hNpos
  have hηbounds : 5 / 6 ≤ η ∧ η ≤ 1 - ε / 10 :=
    logarithmicLengthExponent_bounds hT hNpos hNlower hNupper
  have hεhundred : ε ≤ 1 / 100 := by linarith
  have hσzero : σ ≤ UpperRange.sigmaZero := by
    dsimp [UpperRange.sigmaZero]; linarith
  have hamplitude : 7 / 10 ≤ 1 - σ - 2 * ρ :=
    UpperRange.legal_amplitude_exponent (le_of_lt hε0)
      hεhundred hσzero (by dsimp [ρ]; exact le_rfl)
  have hmargins := UpperRange.explicit_upper_range_margins
    hε0 hεhundred hηbounds.1 hηbounds.2 hσlo hσzero hρ0
      (by dsimp [ρ]; exact le_rfl)
  have hepsSubpower : ε ^ 2 ≤ ε / 1000 := by
    have hp : 0 ≤ ε * (1 / 1000 - ε) :=
      mul_nonneg (le_of_lt hε0) (sub_nonneg.mpr hε)
    nlinarith
  have hcommonFixed : 3 * ε ^ 2 / 4 ≤ 1 / 210 := by nlinarith
  have h₁ : UpperRange.firstExponent η σ ρ ≤
      UpperRange.targetExponent σ - ρ - ε ^ 2 / 2 := by
    dsimp [ρ]; nlinarith [hmargins.1]
  have h₂ : UpperRange.secondExponent η σ ρ ≤
      UpperRange.targetExponent σ - ρ - ε ^ 2 / 2 := by
    dsimp [ρ]; nlinarith [hmargins.2.1]
  have h₃ : UpperRange.thirdExponent η σ ρ ≤
      UpperRange.targetExponent σ - ρ - ε ^ 2 / 2 := by
    dsimp [ρ]; nlinarith [hmargins.2.2]
  have hNleT : (N : ℝ) ≤ T := by
    have hexponent : T ^ (1 - ε / 10) ≤ T ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hT) (by linarith)
    simpa using hNupper.trans hexponent
  have hraw := normalized_guthMaynardLong_bound_at hGM
    (le_of_lt hT) hN hNlower hNleT hamplitude hA hD ha hdiv hR hRT
      hKle hlarge
  have hterms := long_terms_le_upperRange_powers
    (σ := σ) (le_of_lt hT) hNpos hηeq hρ0
  have hconverted := hraw.trans
    (mul_le_mul_of_nonneg_left hterms (by positivity : 0 ≤ C * T ^ ρ))
  exact hconverted.trans (by
    have habsorb := absorb_three_power_terms (le_of_lt hC) (le_of_lt hT)
      h₁ h₂ h₃
    simpa [ρ, UpperRange.targetExponent] using habsorb)

/-- Fully quantified discrete form of the new hybrid density lemma.  It is a
target definition, not an assumption: the proof must be assembled from the
two cited Guth--Maynard fields, coefficient normalization, and the exponent
lemmas in this directory. -/
def HybridDiscreteDensityStatement : Prop :=
  ∃ thresholdLoss : ℝ, 0 < thresholdLoss ∧
    ∀ B : ℝ, 0 ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 1000 →
        ∃ κ : ℝ, 0 < κ ∧
          ∀ A : ℝ, 1 ≤ A →
            ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
              ∀ (T : ℝ) (N : ℕ) (σ : ℝ) (a : ℕ → ℂ)
                  (R : Finset ℝ),
                T₀ ≤ T → 1 ≤ N →
                T ^ (9 / 11 - 10 * ε) ≤ (N : ℝ) →
                (N : ℝ) ≤ T ^ (1 - ε / 10) →
                10 * ε ≤ σ →
                σ ≤ 17 / 70 - thresholdLoss * ε →
                IsDivisorBoundedByConstant B A a →
                IsOneSpaced (↑R : Set ℝ) →
                (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
                (∀ t ∈ R,
                  (N : ℝ) ^ (-σ) <
                    ‖dyadicDirichletPolynomial a (N : ℝ)
                      (onePlusIT t)‖) →
                (R.card : ℝ) ≤ C * T ^ (2 * σ - κ)

/-- Measurable-set companion to `HybridDiscreteDensityStatement`.  The
quantifier order is deliberate: `κ` may depend on `ε` and `B`, but not on
the coefficient scale `A`.  The latter may affect the implied constant and
the starting height, exactly as in the repaired paper. -/
def HybridMeasureDensityStatement : Prop :=
  ∃ thresholdLoss : ℝ, 0 < thresholdLoss ∧
    ∀ B : ℝ, 0 ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 1000 →
        ∃ κ : ℝ, 0 < κ ∧
          ∀ A : ℝ, 1 ≤ A →
            ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
              ∀ (T : ℝ) (N : ℕ) (σ : ℝ) (a : ℕ → ℂ),
                T₀ ≤ T → 1 ≤ N →
                T ^ (9 / 11 - 10 * ε) ≤ (N : ℝ) →
                (N : ℝ) ≤ T ^ (1 - ε / 10) →
                10 * ε ≤ σ →
                σ ≤ 17 / 70 - thresholdLoss * ε →
                IsDivisorBoundedByConstant B A a →
                MeasureTheory.volume
                    (largeValueSet
                      (dyadicDirichletPolynomial a (N : ℝ)) T
                      ((N : ℝ) ^ (-σ))) ≤
                  ENNReal.ofReal (C * T ^ (2 * σ - κ))

/-- The complete formal target of paper Lemma 4.3. -/
def HybridDensityStatement : Prop :=
  HybridDiscreteDensityStatement ∧ HybridMeasureDensityStatement

/-! ## Uniform assembly -/

/-- The fully quantified discrete density statement follows from the two
typed Guth--Maynard inputs.  The proof chooses the two literature constants
before `T,N,σ,a,R`, and chooses one uniform starting height which absorbs the
fixed coefficient-normalization constant. -/
theorem hybridDiscreteDensity_of_guthMaynard
    (hMain : GuthMaynardMainLargeValuesStatement)
    (hLong : GuthMaynardLongPolynomialStatement) :
    HybridDiscreteDensityStatement := by
  refine ⟨6, by norm_num, ?_⟩
  intro B hB ε hε0 hε
  let ρ : ℝ := ε ^ 2 / 4
  have hρpos : 0 < ρ := by dsimp [ρ]; positivity
  refine ⟨ε ^ 2 / 2, by positivity, ?_⟩
  intro A hA
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  obtain ⟨D, hD, hdiv⟩ :=
    exists_uniform_hasDyadicDivisorSubpowerBound globalDivisorSubpower
      hB hρpos
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  obtain ⟨Cmain, hCmain, hMainρ⟩ := hMain ρ hρpos
  obtain ⟨Clong, hClong, hLongρ⟩ := hLong ρ hρpos
  have hMainAt : GuthMaynardMainBoundAt ρ Cmain := by
    exact hMainρ
  have hLongAt : GuthMaynardLongBoundAt ρ Clong := by
    exact hLongρ
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    (eventually_guthMaynardK_le_natCast_rpow A D ρ hρpos)
  let α : ℝ := 9 / 11 - 10 * ε
  have hα : 0 < α := by
    dsimp [α]
    norm_num at hε ⊢
    linarith
  have hTeventual : ∀ᶠ T : ℝ in Filter.atTop,
      (N₀ : ℝ) ≤ T ^ α :=
    (tendsto_rpow_atTop hα).eventually_ge_atTop (N₀ : ℝ)
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.1 hTeventual
  refine ⟨3 * (Cmain + Clong), max 2 T₁, ?_, ?_, ?_⟩
  · positivity
  · exact le_trans (by norm_num) (le_max_left 2 T₁)
  intro T N σ a R hT hN hNlower hNupper hσlo hσhi ha hR hRT hlarge
  have hTone : 1 < T := by
    have htwo : (2 : ℝ) ≤ T := (le_max_left 2 T₁).trans hT
    linarith
  have hT₁T : T₁ ≤ T := (le_max_right 2 T₁).trans hT
  have hN₀cast : (N₀ : ℝ) ≤ (N : ℝ) := by
    calc
      (N₀ : ℝ) ≤ T ^ α := hT₁ T hT₁T
      _ ≤ (N : ℝ) := by simpa [α] using hNlower
  have hN₀nat : N₀ ≤ N := by exact_mod_cast hN₀cast
  have hKle : guthMaynardK A D ρ ≤ (N : ℝ) ^ ρ := hN₀ N hN₀nat
  by_cases hlower : (N : ℝ) ≤ T ^ (5 / 6 : ℝ)
  · have hbound := lowerRange_normalized_density_bound_at
      (by simpa [ρ] using hMainAt) hCmain hε0 hε hTone hN hNlower
      hlower hσlo hσhi hApos hDpos ha (by simpa [ρ] using hdiv N)
      hR hRT (by simpa [ρ] using hKle) hlarge
    have hconst : 3 * Cmain ≤ 3 * (Cmain + Clong) := by
      nlinarith [hClong]
    exact hbound.trans (mul_le_mul_of_nonneg_right hconst
      (Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hTone)) _))
  · have hbranch : T ^ (5 / 6 : ℝ) ≤ (N : ℝ) :=
      le_of_not_ge hlower
    have hbound := upperRange_normalized_density_bound_at
      (by simpa [ρ] using hLongAt) hClong hε0 hε hTone hN hbranch
      hNupper hσlo hσhi hApos hDpos ha (by simpa [ρ] using hdiv N)
      hR hRT (by simpa [ρ] using hKle) hlarge
    have hconst : 3 * Clong ≤ 3 * (Cmain + Clong) := by
      nlinarith [hCmain]
    exact hbound.trans (mul_le_mul_of_nonneg_right hconst
      (Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hTone)) _))

/-- The same-threshold maximal one-spaced selection theorem converts the
uniform discrete estimate into the measurable-set estimate, with only a
factor two in the constant. -/
theorem hybridMeasureDensity_of_discrete
    (hDiscrete : HybridDiscreteDensityStatement) :
    HybridMeasureDensityStatement := by
  obtain ⟨thresholdLoss, hthreshold, hDiscrete⟩ := hDiscrete
  refine ⟨thresholdLoss, hthreshold, ?_⟩
  intro B hB ε hε0 hε
  obtain ⟨κ, hκ, hDiscrete⟩ := hDiscrete B hB ε hε0 hε
  refine ⟨κ, hκ, ?_⟩
  intro A hA
  obtain ⟨C, T₀, hC, hT₀, hDiscrete⟩ := hDiscrete A hA
  refine ⟨2 * C, T₀, mul_pos (by norm_num) hC, hT₀, ?_⟩
  intro T N σ a hT hN hNlower hNupper hσlo hσhi ha
  have hvolume := volume_largeValueSet_le_of_uniform_card_bound
    (A := dyadicDirichletPolynomial a (N : ℝ))
    (T := T) (V := (N : ℝ) ^ (-σ))
    (C := C * T ^ (2 * σ - κ)) (fun R hR hRT hlarge ↦
      hDiscrete T N σ a R hT hN hNlower hNupper hσlo hσhi ha
        hR hRT hlarge)
  simpa [mul_assoc] using hvolume

/-- Conditional closure of both formulations of the hybrid density lemma. -/
theorem hybridDensity_of_guthMaynard
    (hMain : GuthMaynardMainLargeValuesStatement)
    (hLong : GuthMaynardLongPolynomialStatement) :
    HybridDensityStatement := by
  have hDiscrete := hybridDiscreteDensity_of_guthMaynard hMain hLong
  exact ⟨hDiscrete, hybridMeasureDensity_of_discrete hDiscrete⟩

def hybridDensityModule : ProofModule :=
  { name := "Hybrid.HybridDensity"
    paperLocation := "Lemma 4.3"
    purpose := "Assemble both polynomial-length ranges and obtain |R| ≪ T^(2σ-κ)."
    dependsOn :=
      [ "Hybrid.LowerRangeExponents",
        "Hybrid.UpperRangeExponents",
        "Hybrid.DiscreteToMeasure" ]
    status := .proved }

end

end Hybrid
end ExactSemiprimes
