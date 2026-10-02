import ExactSemiprimes.Definitions

/-!
# Polynomial-length consequences in the Type-II range

This file formalizes the elementary length bookkeeping in the proof of
Proposition 5.1.  In particular, it supplies the integer power used when the
shorter polynomial has the larger value, checks the complementary length, and
makes precise the absorption of the fixed support-expansion factor produced by
that power.

The analytic statement that a logarithmic factor is eventually between
`T ^ (-ε / 30)` and `T ^ (ε / 30)` belongs with the later asymptotic setup.
Here that absorption is exposed as the two explicit product hypotheses of
`complementaryLengthBounds`; no asymptotic assertion is hidden in this file.
-/

namespace ExactSemiprimes
namespace TypeII

open Filter Asymptotics

/-! ## Choosing the powering exponent -/

/--
For the short Type-II factor, an integral power has exponent in
`[5/6 - ε, 1 - ε/2]`.

The paper only asks for sufficiently small positive `ε`; the explicit
condition `ε ≤ 2/121` is convenient and more informative.  The proof chooses
`ℓ = ⌈(5/6 - ε)/θ⌉`.  The case `ℓ = 5` uses the upper endpoint
`θ ≤ 2/11 + ε`; for `ℓ ≥ 6`, consecutive admissible exponent intervals
overlap.
-/
theorem existsPoweringExponent {ε θ : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 2 / 121)
    (hθlower : ε / 5 ≤ θ) (hθupper : θ ≤ 2 / 11 + ε) :
    ∃ ℓ : ℕ, 5 ≤ ℓ ∧
      5 / 6 - ε ≤ (ℓ : ℝ) * θ ∧
      (ℓ : ℝ) * θ ≤ 1 - ε / 2 := by
  have hθ : 0 < θ := lt_of_lt_of_le (by positivity) hθlower
  have hA : 0 < 5 / 6 - ε := by nlinarith
  let ℓ : ℕ := ⌈(5 / 6 - ε) / θ⌉₊
  have hℓpos : 0 < ℓ := by
    rw [show ℓ = ⌈(5 / 6 - ε) / θ⌉₊ by rfl, Nat.ceil_pos]
    positivity
  have hfour : (4 : ℕ) < ℓ := by
    rw [show ℓ = ⌈(5 / 6 - ε) / θ⌉₊ by rfl, Nat.lt_ceil]
    rw [lt_div_iff₀ hθ]
    nlinarith
  have hfive : 5 ≤ ℓ := by omega
  have hlower : 5 / 6 - ε ≤ (ℓ : ℝ) * θ := by
    rw [← div_le_iff₀ hθ]
    exact Nat.le_ceil _
  have hprevious : ((ℓ - 1 : ℕ) : ℝ) * θ < 5 / 6 - ε := by
    have hceil := (Nat.ceil_eq_iff (Nat.ne_of_gt hℓpos)).mp
      (show ⌈(5 / 6 - ε) / θ⌉₊ = ℓ by rfl)
    rw [lt_div_iff₀ hθ] at hceil
    exact hceil.1
  have hupper : (ℓ : ℝ) * θ ≤ 1 - ε / 2 := by
    rcases eq_or_lt_of_le hfive with heq | hsix
    · rw [← heq]
      norm_num at hθupper ⊢
      nlinarith
    · have hsix' : (6 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hsix
      have hcast : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ ℓ)]
        norm_num
      rw [hcast] at hprevious
      have hnonneg : 0 ≤ ((ℓ : ℝ) - 6) * θ :=
        mul_nonneg (by linarith) (le_of_lt hθ)
      nlinarith
  exact ⟨ℓ, hfive, hlower, hupper⟩

/--
The exponent choice translates into bounds for the actual length `T ^ θ`;
the outer power on `(T ^ θ) ^ ℓ` is the ordinary natural-number power.
-/
theorem existsPoweredLengthInRange {T ε θ : ℝ}
    (hT : 1 ≤ T)
    (hε : 0 < ε) (hεsmall : ε ≤ 2 / 121)
    (hθlower : ε / 5 ≤ θ) (hθupper : θ ≤ 2 / 11 + ε) :
    ∃ ℓ : ℕ, 5 ≤ ℓ ∧
      T ^ (5 / 6 - ε) ≤ (T ^ θ) ^ ℓ ∧
      (T ^ θ) ^ ℓ ≤ T ^ (1 - ε / 2) := by
  obtain ⟨ℓ, hℓ, hlower, hupper⟩ :=
    existsPoweringExponent hε hεsmall hθlower hθupper
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hpow : T ^ ((ℓ : ℝ) * θ) = (T ^ θ) ^ ℓ := by
    rw [mul_comm, Real.rpow_mul hT0, Real.rpow_natCast]
  refine ⟨ℓ, hℓ, ?_, ?_⟩
  · rw [← hpow]
    exact Real.rpow_le_rpow_of_exponent_le hT hlower
  · rw [← hpow]
    exact Real.rpow_le_rpow_of_exponent_le hT hupper

/-! ## The complementary polynomial -/

/-- Every fixed power of `log T` is eventually bounded by an arbitrarily
small positive power of `T`.  This is the quantified absorption hidden by
the paper's notation `(log T)^{O(1)}`. -/
theorem eventually_log_rpow_le_rpow (L : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, (Real.log T) ^ L ≤ T ^ δ := by
  have hsmall :=
    isLittleO_iff.1 (isLittleO_log_rpow_rpow_atTop L hδ) zero_lt_one
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with T hT hTone
  have hleft : 0 ≤ (Real.log T) ^ L :=
    Real.rpow_nonneg (Real.log_nonneg hTone.le) _
  have hright : 0 ≤ T ^ δ := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg hleft, Real.norm_of_nonneg hright, one_mul] at hT
  exact hT

/-- Reciprocal form of `eventually_log_rpow_le_rpow`. -/
theorem eventually_rpow_neg_le_log_rpow_neg (L : ℝ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, T ^ (-δ) ≤ (Real.log T) ^ (-L) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_log_rpow_le_rpow L hδ] with T hT hupper
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hlogpos : 0 < Real.log T := Real.log_pos hT
  rw [Real.rpow_neg hTpos.le, Real.rpow_neg hlogpos.le]
  simpa only [one_div] using
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos hlogpos L) hupper

/-- The repaired two-sided logarithmic product hypothesis implies the
power-sized product bounds used by `complementaryLengthBounds`, once `T` is
sufficiently large. -/
theorem eventually_product_power_bounds (L : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ M₁ M₂ : ℝ,
      0 < M₁ →
      (Real.log T) ^ (-L) ≤ M₁ * M₂ / T →
      M₁ * M₂ / T ≤ (Real.log T) ^ L →
      T ^ (1 - δ) ≤ M₁ * M₂ ∧ M₁ * M₂ ≤ T ^ (1 + δ) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    eventually_log_rpow_le_rpow L hδ,
    eventually_rpow_neg_le_log_rpow_neg L hδ] with T hT hlogUpper hlogLower
  intro M₁ M₂ _hM₁ hprodLower hprodUpper
  have hTpos : 0 < T := zero_lt_one.trans hT
  have hTnonneg : 0 ≤ T := hTpos.le
  constructor
  · have hratio : T ^ (-δ) ≤ M₁ * M₂ / T :=
      hlogLower.trans hprodLower
    have hmul := mul_le_mul_of_nonneg_left hratio hTnonneg
    calc
      T ^ (1 - δ) = T ^ (1 + (-δ)) := by ring_nf
      _ = T ^ (1 : ℝ) * T ^ (-δ) := Real.rpow_add hTpos 1 (-δ)
      _ = T * T ^ (-δ) := by rw [Real.rpow_one]
      _ ≤ T * (M₁ * M₂ / T) := hmul
      _ = M₁ * M₂ := by field_simp [ne_of_gt hTpos]
  · have hratio : M₁ * M₂ / T ≤ T ^ δ :=
      hprodUpper.trans hlogUpper
    have hmul := mul_le_mul_of_nonneg_left hratio hTnonneg
    calc
      M₁ * M₂ = T * (M₁ * M₂ / T) := by
        field_simp [ne_of_gt hTpos]
      _ ≤ T * T ^ δ := hmul
      _ = T ^ (1 : ℝ) * T ^ δ := by rw [Real.rpow_one]
      _ = T ^ (1 + δ) := (Real.rpow_add hTpos 1 δ).symm

/--
Once the logarithmic error in `M₁ M₂ = T (log T)^{O(1)}` has been
absorbed between `T ^ (1 - ε/30)` and `T ^ (1 + ε/30)`, the complementary
factor has the two concrete length bounds displayed in the paper.
-/
theorem complementaryLengthBounds {T M₁ M₂ ε : ℝ}
    (hT : 1 ≤ T) (hε : 0 ≤ ε) (hM₁ : 0 < M₁)
    (hproductLower : T ^ (1 - ε / 30) ≤ M₁ * M₂)
    (hproductUpper : M₁ * M₂ ≤ T ^ (1 + ε / 30))
    (hM₁lower : T ^ (ε / 5) ≤ M₁)
    (hM₁upper : M₁ ≤ T ^ (2 / 11 + ε)) :
    T ^ (9 / 11 - 2 * ε) ≤ M₂ ∧ M₂ ≤ T ^ (1 - ε / 6) := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hT0 : 0 ≤ T := le_of_lt hTpos
  constructor
  · apply le_of_mul_le_mul_left _ hM₁
    calc
      M₁ * T ^ (9 / 11 - 2 * ε) =
          T ^ (9 / 11 - 2 * ε) * M₁ := by ring
      _ ≤ T ^ (9 / 11 - 2 * ε) * T ^ (2 / 11 + ε) :=
        mul_le_mul_of_nonneg_left hM₁upper (Real.rpow_nonneg hT0 _)
      _ = T ^ (1 - ε) := by
        rw [← Real.rpow_add hTpos]
        congr 1
        ring
      _ ≤ T ^ (1 - ε / 30) := by
        apply Real.rpow_le_rpow_of_exponent_le hT
        nlinarith
      _ ≤ M₁ * M₂ := hproductLower
  · apply le_of_mul_le_mul_left _ hM₁
    calc
      M₁ * M₂ ≤ T ^ (1 + ε / 30) := hproductUpper
      _ = T ^ (ε / 5) * T ^ (1 - ε / 6) := by
        rw [← Real.rpow_add hTpos]
        congr 1
        ring
      _ ≤ M₁ * T ^ (1 - ε / 6) :=
        mul_le_mul_of_nonneg_right hM₁lower (Real.rpow_nonneg hT0 _)

/--
The concrete complementary-factor interval is contained in the slightly
wider interval accepted by the hybrid density lemma.
-/
theorem complementaryLengthFitsHybridRange {T M₂ ε : ℝ}
    (hT : 1 ≤ T) (hε : 0 ≤ ε)
    (hM₂lower : T ^ (9 / 11 - 2 * ε) ≤ M₂)
    (hM₂upper : M₂ ≤ T ^ (1 - ε / 6)) :
    T ^ (9 / 11 - 10 * ε) ≤ M₂ ∧
      M₂ ≤ T ^ (1 - ε / 10) := by
  constructor
  · exact (Real.rpow_le_rpow_of_exponent_le hT (by nlinarith)).trans hM₂lower
  · exact hM₂upper.trans (Real.rpow_le_rpow_of_exponent_le hT (by nlinarith))

/--
The exponent interval selected for the powered short factor is itself inside
the hybrid lemma's admissible interval.
-/
theorem poweredLengthFitsHybridRange {T M ε : ℝ}
    (hT : 1 ≤ T) (hε : 0 ≤ ε)
    (hMlower : T ^ (5 / 6 - ε) ≤ M)
    (hMupper : M ≤ T ^ (1 - ε / 2)) :
    T ^ (9 / 11 - 10 * ε) ≤ M ∧
      M ≤ T ^ (1 - ε / 10) := by
  constructor
  · exact (Real.rpow_le_rpow_of_exponent_le hT (by nlinarith)).trans hMlower
  · exact hMupper.trans (Real.rpow_le_rpow_of_exponent_le hT (by nlinarith))

/-! ## Support expansion under powering -/

/--
Products of integers from `(M,2M]` are supported between `M^ℓ` and
`(2M)^ℓ` (with a weak lower inequality, which is enough for length
bookkeeping).
-/
theorem productOfDyadicFactorsBounds {M : ℝ} (hM : 0 ≤ M)
    (xs : List ℕ)
    (hxs : ∀ n ∈ xs, InDyadicRange M n) :
    M ^ xs.length ≤ (xs.prod : ℝ) ∧
      (xs.prod : ℝ) ≤ (2 * M) ^ xs.length := by
  induction xs with
  | nil => simp
  | cons n xs ih =>
      have hn := hxs n (by simp)
      have htail : ∀ m ∈ xs, InDyadicRange M m := by
        intro m hm
        exact hxs m (by simp [hm])
      have hi := ih htail
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      have h2M : 0 ≤ 2 * M := by positivity
      constructor
      · simp only [List.length_cons, List.prod_cons, Nat.cast_mul, pow_succ]
        calc
          M ^ xs.length * M ≤ M ^ xs.length * (n : ℝ) :=
            mul_le_mul_of_nonneg_left hn.1.le (pow_nonneg hM _)
          _ ≤ (xs.prod : ℝ) * (n : ℝ) :=
            mul_le_mul_of_nonneg_right hi.1 hn0
          _ = (n : ℝ) * (xs.prod : ℝ) := by ring
      · simp only [List.length_cons, List.prod_cons, Nat.cast_mul, pow_succ]
        calc
          (n : ℝ) * (xs.prod : ℝ) ≤ (2 * M) * (xs.prod : ℝ) :=
            mul_le_mul_of_nonneg_right hn.2 (by positivity)
          _ ≤ (2 * M) * (2 * M) ^ xs.length :=
            mul_le_mul_of_nonneg_left hi.2 h2M
          _ = (2 * M) ^ xs.length * (2 * M) := by ring

/--
A fixed dyadic support-expansion factor `2^ℓ` is eventually swallowed by
`T ^ (2ε/5)`.  This makes precise the paper's use of the reserved exponent
margin for the boundedly many dyadic pieces.
-/
theorem eventuallyTwoPowLeRpow (ℓ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop, (2 : ℝ) ^ ℓ ≤ T ^ (2 * ε / 5) := by
  have hexponent : 0 < 2 * ε / 5 := by positivity
  exact ((tendsto_rpow_atTop hexponent).eventually_gt_atTop
    ((2 : ℝ) ^ ℓ)).mono fun _ hT ↦ hT.le

/--
If a base length has the stronger upper bound `T ^ (1-ε/2)`, the fixed
factor generated by an `ℓ`-fold product remains below `T ^ (1-ε/10)` once
that factor has been absorbed.
-/
theorem dyadicExpansionPreservesUpperRange {T M ε : ℝ} {ℓ : ℕ}
    (hT : 0 < T) (hM : 0 ≤ M)
    (hbase : M ≤ T ^ (1 - ε / 2))
    (hfactor : (2 : ℝ) ^ ℓ ≤ T ^ (2 * ε / 5)) :
    (2 : ℝ) ^ ℓ * M ≤ T ^ (1 - ε / 10) := by
  calc
    (2 : ℝ) ^ ℓ * M ≤ T ^ (2 * ε / 5) * T ^ (1 - ε / 2) :=
      mul_le_mul hfactor hbase hM (Real.rpow_nonneg hT.le _)
    _ = T ^ (1 - ε / 10) := by
      rw [← Real.rpow_add hT]
      congr 1
      ring

def polynomialLengthRangesModule : ProofModule :=
  { name := "TypeII.PolynomialLengthRanges"
    paperLocation :=
      "Proof of Proposition 5.1, length checks for M₁, M₂, and M₁^ℓ"
    purpose :=
      "Choose the powering exponent and prove the elementary base, complementary, and support-expansion length bounds."
    dependsOn := ["Definitions", "Mathlib real powers and ordered arithmetic"]
    status := .proved }

end TypeII
end ExactSemiprimes
