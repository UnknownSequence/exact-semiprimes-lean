import ExactSemiprimes.Definitions

/-!
# Partition into extreme and medium large-value regimes

This file makes the set-theoretic reduction in the proof of Proposition 5.1
literal.  The paper says to cover a one-spaced set `R` by `R₁`, `R₂`, and
`R₃`, "allocating overlaps arbitrarily".  We remove that ambiguity by giving
`R₁` priority over `R₃`; `R₂` is then the complement of the two selected
pieces inside `R`.  The resulting pieces are disjoint and have union `R`.

The second part defines the logarithmic magnitude bins used on `R₂`.  A bin
of index `k : ℤ` is the half-open interval

`k ≤ -log ‖M(1+it)‖ < k+1`.

Thus a nonzero value in that bin lies between `exp (-(k+1))` and
`exp (-k)`, so the notation `‖M(1+it)‖ ≍ M⁻ᵗ` in the paper has a precise,
fixed-factor interpretation.  The floor function supplies a unique bin for
every value, including zero (whose logarithm is Mathlib's totalized value);
the exponential comparison is stated only under the mathematically necessary
positivity hypothesis.

Measurability is never inferred merely from the notation `M(1+it)`: the
measurability lemmas below explicitly assume that the two magnitude functions
are measurable.
-/

namespace ExactSemiprimes
namespace TypeII

noncomputable section

/-! ## Pointwise magnitudes and the three regimes -/

/-- The magnitude of a Dirichlet polynomial on the line `Re(s) = 1`. -/
def typeIIMagnitude (M : ℂ → ℂ) (t : ℝ) : ℝ :=
  ‖M (onePlusIT t)‖

/-- The raw `R₁` condition from the paper: at least one factor is extremely
large relative to its length. -/
def extremeLargeValueSet (M₁ M₂ : ℂ → ℂ) (N₁ N₂ ε : ℝ) : Set ℝ :=
  {t | N₁ ^ (-10 * ε) ≤ typeIIMagnitude M₁ t ∨
       N₂ ^ (-10 * ε) ≤ typeIIMagnitude M₂ t}

/-- The raw `R₃` condition from the paper: at least one factor is smaller
than `T⁻¹`. -/
def tinyValueSet (M₁ M₂ : ℂ → ℂ) (T : ℝ) : Set ℝ :=
  {t | typeIIMagnitude M₁ t < T⁻¹ ∨ typeIIMagnitude M₂ t < T⁻¹}

/-- The extreme-large piece. -/
def largeValueR1 (R : Set ℝ) (M₁ M₂ : ℂ → ℂ) (N₁ N₂ ε : ℝ) : Set ℝ :=
  R ∩ extremeLargeValueSet M₁ M₂ N₁ N₂ ε

/-- The tiny-value piece, after points already assigned to `R₁` are removed. -/
def largeValueR3 (R : Set ℝ) (M₁ M₂ : ℂ → ℂ)
    (N₁ N₂ T ε : ℝ) : Set ℝ :=
  (R \ largeValueR1 R M₁ M₂ N₁ N₂ ε) ∩ tinyValueSet M₁ M₂ T

/-- The medium piece: the points of `R` assigned to neither `R₁` nor `R₃`. -/
def largeValueR2 (R : Set ℝ) (M₁ M₂ : ℂ → ℂ)
    (N₁ N₂ T ε : ℝ) : Set ℝ :=
  R \ (largeValueR1 R M₁ M₂ N₁ N₂ ε ∪
    largeValueR3 R M₁ M₂ N₁ N₂ T ε)

@[simp]
theorem mem_largeValueR1_iff {R : Set ℝ} {M₁ M₂ : ℂ → ℂ}
    {N₁ N₂ ε t : ℝ} :
    t ∈ largeValueR1 R M₁ M₂ N₁ N₂ ε ↔
      t ∈ R ∧ (N₁ ^ (-10 * ε) ≤ typeIIMagnitude M₁ t ∨
        N₂ ^ (-10 * ε) ≤ typeIIMagnitude M₂ t) := by
  rfl

@[simp]
theorem mem_largeValueR3_iff {R : Set ℝ} {M₁ M₂ : ℂ → ℂ}
    {N₁ N₂ T ε t : ℝ} :
    t ∈ largeValueR3 R M₁ M₂ N₁ N₂ T ε ↔
      t ∈ R ∧
      ¬(N₁ ^ (-10 * ε) ≤ typeIIMagnitude M₁ t ∨
        N₂ ^ (-10 * ε) ≤ typeIIMagnitude M₂ t) ∧
      (typeIIMagnitude M₁ t < T⁻¹ ∨ typeIIMagnitude M₂ t < T⁻¹) := by
  simp [largeValueR3, largeValueR1, extremeLargeValueSet, tinyValueSet]
  tauto

@[simp]
theorem mem_largeValueR2_iff {R : Set ℝ} {M₁ M₂ : ℂ → ℂ}
    {N₁ N₂ T ε t : ℝ} :
    t ∈ largeValueR2 R M₁ M₂ N₁ N₂ T ε ↔
      t ∈ R ∧
      typeIIMagnitude M₁ t < N₁ ^ (-10 * ε) ∧
      typeIIMagnitude M₂ t < N₂ ^ (-10 * ε) ∧
      T⁻¹ ≤ typeIIMagnitude M₁ t ∧
      T⁻¹ ≤ typeIIMagnitude M₂ t := by
  simp [largeValueR2, largeValueR3, largeValueR1,
    extremeLargeValueSet, tinyValueSet]
  tauto

/-- The deterministic allocation really covers the original set. -/
theorem largeValue_partition (R : Set ℝ) (M₁ M₂ : ℂ → ℂ)
    (N₁ N₂ T ε : ℝ) :
    largeValueR1 R M₁ M₂ N₁ N₂ ε ∪
      largeValueR2 R M₁ M₂ N₁ N₂ T ε ∪
      largeValueR3 R M₁ M₂ N₁ N₂ T ε = R := by
  ext t
  by_cases h₁ : t ∈ largeValueR1 R M₁ M₂ N₁ N₂ ε
  · simp [h₁, h₁.1]
  by_cases h₃ : t ∈ largeValueR3 R M₁ M₂ N₁ N₂ T ε
  · simp [h₁, h₃]
    exact h₃.1.1
  · simp [h₁, h₃, largeValueR2]

theorem largeValueR1_disjoint_R2 (R : Set ℝ) (M₁ M₂ : ℂ → ℂ)
    (N₁ N₂ T ε : ℝ) :
    Disjoint (largeValueR1 R M₁ M₂ N₁ N₂ ε)
      (largeValueR2 R M₁ M₂ N₁ N₂ T ε) := by
  rw [Set.disjoint_left]
  intro t ht₁ ht₂
  exact ht₂.2 (Or.inl ht₁)

theorem largeValueR1_disjoint_R3 (R : Set ℝ) (M₁ M₂ : ℂ → ℂ)
    (N₁ N₂ T ε : ℝ) :
    Disjoint (largeValueR1 R M₁ M₂ N₁ N₂ ε)
      (largeValueR3 R M₁ M₂ N₁ N₂ T ε) := by
  rw [Set.disjoint_left]
  intro t ht₁ ht₃
  exact ht₃.1.2 ht₁

theorem largeValueR2_disjoint_R3 (R : Set ℝ) (M₁ M₂ : ℂ → ℂ)
    (N₁ N₂ T ε : ℝ) :
    Disjoint (largeValueR2 R M₁ M₂ N₁ N₂ T ε)
      (largeValueR3 R M₁ M₂ N₁ N₂ T ε) := by
  rw [Set.disjoint_left]
  intro t ht₂ ht₃
  exact ht₂.2 (Or.inr ht₃)

private theorem largeValueR1_subset (R : Set ℝ) (M₁ M₂ : ℂ → ℂ)
    (N₁ N₂ ε : ℝ) : largeValueR1 R M₁ M₂ N₁ N₂ ε ⊆ R :=
  Set.inter_subset_left

private theorem largeValueR2_subset (R : Set ℝ) (M₁ M₂ : ℂ → ℂ)
    (N₁ N₂ T ε : ℝ) : largeValueR2 R M₁ M₂ N₁ N₂ T ε ⊆ R :=
  Set.sdiff_subset

private theorem largeValueR3_subset (R : Set ℝ) (M₁ M₂ : ℂ → ℂ)
    (N₁ N₂ T ε : ℝ) : largeValueR3 R M₁ M₂ N₁ N₂ T ε ⊆ R := by
  intro t ht
  exact ht.1.1

/-- Each selected piece of a finite one-spaced set remains finite and
one-spaced. -/
theorem finiteOneSpaced_largeValueR1 {R : Set ℝ} (hR : IsFiniteOneSpaced R)
    (M₁ M₂ : ℂ → ℂ) (N₁ N₂ ε : ℝ) :
    IsFiniteOneSpaced (largeValueR1 R M₁ M₂ N₁ N₂ ε) :=
  ⟨hR.1.subset (largeValueR1_subset R M₁ M₂ N₁ N₂ ε),
    hR.2.mono (largeValueR1_subset R M₁ M₂ N₁ N₂ ε)⟩

theorem finiteOneSpaced_largeValueR2 {R : Set ℝ} (hR : IsFiniteOneSpaced R)
    (M₁ M₂ : ℂ → ℂ) (N₁ N₂ T ε : ℝ) :
    IsFiniteOneSpaced (largeValueR2 R M₁ M₂ N₁ N₂ T ε) :=
  ⟨hR.1.subset (largeValueR2_subset R M₁ M₂ N₁ N₂ T ε),
    hR.2.mono (largeValueR2_subset R M₁ M₂ N₁ N₂ T ε)⟩

theorem finiteOneSpaced_largeValueR3 {R : Set ℝ} (hR : IsFiniteOneSpaced R)
    (M₁ M₂ : ℂ → ℂ) (N₁ N₂ T ε : ℝ) :
    IsFiniteOneSpaced (largeValueR3 R M₁ M₂ N₁ N₂ T ε) :=
  ⟨hR.1.subset (largeValueR3_subset R M₁ M₂ N₁ N₂ T ε),
    hR.2.mono (largeValueR3_subset R M₁ M₂ N₁ N₂ T ε)⟩

/-! ## Measurability, with explicit analytic hypotheses -/

theorem measurableSet_extremeLargeValueSet {M₁ M₂ : ℂ → ℂ}
    {N₁ N₂ ε : ℝ}
    (hM₁ : Measurable (typeIIMagnitude M₁))
    (hM₂ : Measurable (typeIIMagnitude M₂)) :
    MeasurableSet (extremeLargeValueSet M₁ M₂ N₁ N₂ ε) := by
  exact (measurableSet_le measurable_const hM₁).union
    (measurableSet_le measurable_const hM₂)

theorem measurableSet_tinyValueSet {M₁ M₂ : ℂ → ℂ} {T : ℝ}
    (hM₁ : Measurable (typeIIMagnitude M₁))
    (hM₂ : Measurable (typeIIMagnitude M₂)) :
    MeasurableSet (tinyValueSet M₁ M₂ T) := by
  exact (measurableSet_lt hM₁ measurable_const).union
    (measurableSet_lt hM₂ measurable_const)

theorem measurableSet_largeValueR1 {R : Set ℝ} {M₁ M₂ : ℂ → ℂ}
    {N₁ N₂ ε : ℝ} (hR : MeasurableSet R)
    (hM₁ : Measurable (typeIIMagnitude M₁))
    (hM₂ : Measurable (typeIIMagnitude M₂)) :
    MeasurableSet (largeValueR1 R M₁ M₂ N₁ N₂ ε) :=
  hR.inter (measurableSet_extremeLargeValueSet hM₁ hM₂)

theorem measurableSet_largeValueR3 {R : Set ℝ} {M₁ M₂ : ℂ → ℂ}
    {N₁ N₂ T ε : ℝ} (hR : MeasurableSet R)
    (hM₁ : Measurable (typeIIMagnitude M₁))
    (hM₂ : Measurable (typeIIMagnitude M₂)) :
    MeasurableSet (largeValueR3 R M₁ M₂ N₁ N₂ T ε) := by
  exact (hR.diff (measurableSet_largeValueR1 hR hM₁ hM₂)).inter
    (measurableSet_tinyValueSet hM₁ hM₂)

theorem measurableSet_largeValueR2 {R : Set ℝ} {M₁ M₂ : ℂ → ℂ}
    {N₁ N₂ T ε : ℝ} (hR : MeasurableSet R)
    (hM₁ : Measurable (typeIIMagnitude M₁))
    (hM₂ : Measurable (typeIIMagnitude M₂)) :
    MeasurableSet (largeValueR2 R M₁ M₂ N₁ N₂ T ε) := by
  exact hR.diff ((measurableSet_largeValueR1 hR hM₁ hM₂).union
    (measurableSet_largeValueR3 hR hM₁ hM₂))

/-! ## Logarithmic magnitude bins -/

/-- The unnormalised logarithmic size `-log ‖M(1+it)‖`. -/
def logMagnitude (M : ℂ → ℂ) (t : ℝ) : ℝ :=
  -Real.log (typeIIMagnitude M t)

/-- A unit-width, half-open logarithmic magnitude bin. -/
def logMagnitudeBin (M : ℂ → ℂ) (k : ℤ) : Set ℝ :=
  {t | (k : ℝ) ≤ logMagnitude M t ∧ logMagnitude M t < (k : ℝ) + 1}

/-- The simultaneous bin for the two Type-II factors. -/
def logMagnitudePairBin (M₁ M₂ : ℂ → ℂ) (k₁ k₂ : ℤ) : Set ℝ :=
  logMagnitudeBin M₁ k₁ ∩ logMagnitudeBin M₂ k₂

@[simp]
theorem mem_logMagnitudeBin_iff {M : ℂ → ℂ} {k : ℤ} {t : ℝ} :
    t ∈ logMagnitudeBin M k ↔
      (k : ℝ) ≤ logMagnitude M t ∧ logMagnitude M t < (k : ℝ) + 1 :=
  Iff.rfl

/-- Every point has its canonical logarithmic bin. -/
theorem mem_logMagnitudeBin_floor (M : ℂ → ℂ) (t : ℝ) :
    t ∈ logMagnitudeBin M ⌊logMagnitude M t⌋ :=
  ⟨Int.floor_le _, Int.lt_floor_add_one _⟩

/-- Logarithmic bins are genuinely disjoint: a point determines its index. -/
theorem logMagnitudeBin_index_unique {M : ℂ → ℂ} {t : ℝ} {k l : ℤ}
    (hk : t ∈ logMagnitudeBin M k) (hl : t ∈ logMagnitudeBin M l) : k = l := by
  have hk' : ⌊logMagnitude M t⌋ = k := Int.floor_eq_iff.mpr hk
  have hl' : ⌊logMagnitude M t⌋ = l := Int.floor_eq_iff.mpr hl
  exact hk'.symm.trans hl'

theorem logMagnitudePairBin_index_unique {M₁ M₂ : ℂ → ℂ} {t : ℝ}
    {k₁ k₂ l₁ l₂ : ℤ}
    (hk : t ∈ logMagnitudePairBin M₁ M₂ k₁ k₂)
    (hl : t ∈ logMagnitudePairBin M₁ M₂ l₁ l₂) :
    k₁ = l₁ ∧ k₂ = l₂ :=
  ⟨logMagnitudeBin_index_unique hk.1 hl.1,
    logMagnitudeBin_index_unique hk.2 hl.2⟩

/-- Every point of `R₂` belongs to a unique simultaneous magnitude bin. -/
theorem existsUnique_logMagnitudePairBin_of_mem_R2
    {R : Set ℝ} {M₁ M₂ : ℂ → ℂ} {N₁ N₂ T ε t : ℝ}
    (ht : t ∈ largeValueR2 R M₁ M₂ N₁ N₂ T ε) :
    ∃! k : ℤ × ℤ,
      t ∈ largeValueR2 R M₁ M₂ N₁ N₂ T ε ∩
        logMagnitudePairBin M₁ M₂ k.1 k.2 := by
  let k : ℤ × ℤ := (⌊logMagnitude M₁ t⌋, ⌊logMagnitude M₂ t⌋)
  refine ⟨k, ⟨ht, mem_logMagnitudeBin_floor M₁ t,
    mem_logMagnitudeBin_floor M₂ t⟩, ?_⟩
  intro l hl
  apply Prod.ext
  · exact (logMagnitudeBin_index_unique
      (mem_logMagnitudeBin_floor M₁ t) hl.2.1).symm
  · exact (logMagnitudeBin_index_unique
      (mem_logMagnitudeBin_floor M₂ t) hl.2.2).symm

/-- Membership in a logarithmic bin gives the fixed-factor comparison that
the paper denotes by `≍`.  Positivity is essential because `Real.log` is
totalized at zero. -/
theorem magnitude_bounds_of_mem_logMagnitudeBin {M : ℂ → ℂ}
    {k : ℤ} {t : ℝ} (ht : t ∈ logMagnitudeBin M k)
    (hpos : 0 < typeIIMagnitude M t) :
    Real.exp (-((k : ℝ) + 1)) < typeIIMagnitude M t ∧
      typeIIMagnitude M t ≤ Real.exp (-(k : ℝ)) := by
  constructor
  · rw [← Real.exp_log hpos, Real.exp_lt_exp]
    simpa [logMagnitude] using (neg_lt_neg ht.2)
  · rw [← Real.exp_log hpos, Real.exp_le_exp]
    simpa [logMagnitude] using (neg_le_neg ht.1)

/-- The exponent represented by a bin when the polynomial length is `N`.
The bin width in this normalization is exactly `1 / log N`. -/
def binExponent (N : ℝ) (k : ℤ) : ℝ :=
  (k : ℝ) / Real.log N

/-- The actual exponent `τ` defined by `‖M(1+it)‖ = M⁻ᵗ`. -/
def normalizedMagnitudeExponent (N : ℝ) (M : ℂ → ℂ) (t : ℝ) : ℝ :=
  logMagnitude M t / Real.log N

theorem normalizedMagnitudeExponent_mem_bin {N : ℝ} {M : ℂ → ℂ}
    {k : ℤ} {t : ℝ} (hN : 1 < N) (ht : t ∈ logMagnitudeBin M k) :
    binExponent N k ≤ normalizedMagnitudeExponent N M t ∧
      normalizedMagnitudeExponent N M t < binExponent N k + 1 / Real.log N := by
  have hlog : 0 < Real.log N := Real.log_pos hN
  constructor
  · exact (div_le_div_iff_of_pos_right hlog).2 ht.1
  · rw [binExponent, normalizedMagnitudeExponent, ← add_div]
    exact (div_lt_div_iff_of_pos_right hlog).2 (by simpa using ht.2)

theorem measurableSet_logMagnitudeBin {M : ℂ → ℂ} {k : ℤ}
    (hM : Measurable (typeIIMagnitude M)) :
    MeasurableSet (logMagnitudeBin M k) := by
  have hlog : Measurable (logMagnitude M) := hM.log.neg
  exact (measurableSet_le measurable_const hlog).inter
    (measurableSet_lt hlog measurable_const)

theorem measurableSet_logMagnitudePairBin {M₁ M₂ : ℂ → ℂ} {k₁ k₂ : ℤ}
    (hM₁ : Measurable (typeIIMagnitude M₁))
    (hM₂ : Measurable (typeIIMagnitude M₂)) :
    MeasurableSet (logMagnitudePairBin M₁ M₂ k₁ k₂) :=
  (measurableSet_logMagnitudeBin hM₁).inter
    (measurableSet_logMagnitudeBin hM₂)

/-! ## The finite number of relevant bin pairs

On `R₂`, each magnitude lies in `[T⁻¹, 1]` (the upper bound uses
`Nᵢ ≥ 1` and `ε ≥ 0`).  Consequently its logarithmic magnitude lies in
`[0, log T]`, and its canonical floor index belongs to

`{0, 1, …, ⌊log T⌋}`.

The definitions and theorems below turn the often-written
`O((log T)²)` bin count into the exact finite bound

`(⌊log T⌋ + 1).toNat²`.

This convention also covers vacuous parameter ranges: if `log T < 0`, the
integer interval is empty.  No asymptotic notation or hidden rounding
convention is used in the formal statement.
-/

/-- The canonical pair of unit logarithmic-bin indices at a point. -/
def canonicalLogMagnitudePair (M₁ M₂ : ℂ → ℂ) (t : ℝ) : ℤ × ℤ :=
  (⌊logMagnitude M₁ t⌋, ⌊logMagnitude M₂ t⌋)

/-- The integer indices which can occur for a magnitude in `[T⁻¹, 1]`. -/
def logMagnitudeIndexRange (T : ℝ) : Finset ℤ :=
  Finset.Icc 0 ⌊Real.log T⌋

/-- The square of the one-factor index range. -/
def logMagnitudePairIndexRange (T : ℝ) : Finset (ℤ × ℤ) :=
  logMagnitudeIndexRange T ×ˢ logMagnitudeIndexRange T

/-- The points of a finite set which the deterministic partition assigns to
`R₂`.  The ambient set in `largeValueR2` is exactly the coercion of `R`. -/
def finiteLargeValueR2 (R : Finset ℝ) (M₁ M₂ : ℂ → ℂ)
    (N₁ N₂ T ε : ℝ) : Finset ℝ :=
  by
    classical
    exact R.filter fun t =>
      t ∈ largeValueR2 (R : Set ℝ) M₁ M₂ N₁ N₂ T ε

/-- The set of bin pairs actually occupied by the finite medium-value set. -/
def occupiedMediumLogMagnitudePairs (R : Finset ℝ) (M₁ M₂ : ℂ → ℂ)
    (N₁ N₂ T ε : ℝ) : Finset (ℤ × ℤ) :=
  (finiteLargeValueR2 R M₁ M₂ N₁ N₂ T ε).image
    (canonicalLogMagnitudePair M₁ M₂)

/-- A magnitude in `[T⁻¹, 1]` has logarithmic magnitude in
`[0, log T]`. -/
theorem logMagnitude_bounds_of_inv_le_of_le_one {M : ℂ → ℂ}
    {T t : ℝ} (hT : 0 < T)
    (hlower : T⁻¹ ≤ typeIIMagnitude M t)
    (hupper : typeIIMagnitude M t ≤ 1) :
    0 ≤ logMagnitude M t ∧ logMagnitude M t ≤ Real.log T := by
  have hinvpos : 0 < T⁻¹ := inv_pos.mpr hT
  have hmagpos : 0 < typeIIMagnitude M t := lt_of_lt_of_le hinvpos hlower
  constructor
  · exact neg_nonneg.mpr (Real.log_nonpos (le_of_lt hmagpos) hupper)
  · have hlog : Real.log T⁻¹ ≤ Real.log (typeIIMagnitude M t) :=
      Real.log_le_log hinvpos hlower
    rw [Real.log_inv] at hlog
    simpa [logMagnitude] using (neg_le_neg hlog)

/-- The two `R₂` magnitudes satisfy the common logarithmic bounds.  All
parameter hypotheses used to obtain the upper bound `‖Mᵢ‖ ≤ 1` are explicit. -/
theorem logMagnitude_bounds_of_mem_largeValueR2
    {R : Set ℝ} {M₁ M₂ : ℂ → ℂ} {N₁ N₂ T ε t : ℝ}
    (hT : 0 < T) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂) (hε : 0 ≤ ε)
    (ht : t ∈ largeValueR2 R M₁ M₂ N₁ N₂ T ε) :
    (0 ≤ logMagnitude M₁ t ∧ logMagnitude M₁ t ≤ Real.log T) ∧
      (0 ≤ logMagnitude M₂ t ∧ logMagnitude M₂ t ≤ Real.log T) := by
  rcases (mem_largeValueR2_iff.mp ht) with
    ⟨-, hupper₁, hupper₂, hlower₁, hlower₂⟩
  have hexponent : -10 * ε ≤ 0 := by nlinarith
  have hpow₁ : N₁ ^ (-10 * ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN₁ hexponent
  have hpow₂ : N₂ ^ (-10 * ε) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN₂ hexponent
  exact ⟨logMagnitude_bounds_of_inv_le_of_le_one hT hlower₁
      (le_trans (le_of_lt hupper₁) hpow₁),
    logMagnitude_bounds_of_inv_le_of_le_one hT hlower₂
      (le_trans (le_of_lt hupper₂) hpow₂)⟩

/-- Taking floors sends the closed real interval `[0, log T]` into the
explicit finite integer interval. -/
theorem floor_logMagnitude_mem_indexRange {M : ℂ → ℂ} {T t : ℝ}
    (hbounds : 0 ≤ logMagnitude M t ∧
      logMagnitude M t ≤ Real.log T) :
    ⌊logMagnitude M t⌋ ∈ logMagnitudeIndexRange T := by
  exact Finset.mem_Icc.mpr
    ⟨Int.le_floor.mpr (by simpa using hbounds.1),
      Int.floor_le_floor hbounds.2⟩

/-- Exact number of possible indices for one factor. -/
theorem card_logMagnitudeIndexRange (T : ℝ) :
    (logMagnitudeIndexRange T).card = (⌊Real.log T⌋ + 1).toNat := by
  simp [logMagnitudeIndexRange]

/-- Exact number of possible simultaneous bin pairs.  This is the precise
finite form of the paper's `O((log T)²)` count. -/
theorem card_logMagnitudePairIndexRange (T : ℝ) :
    (logMagnitudePairIndexRange T).card =
      ((⌊Real.log T⌋ + 1).toNat) ^ 2 := by
  simp [logMagnitudePairIndexRange, card_logMagnitudeIndexRange, pow_two]

/-- Every pair occupied on `R₂` lies in the explicit square index range. -/
theorem occupiedMediumLogMagnitudePairs_subset
    (R : Finset ℝ) (M₁ M₂ : ℂ → ℂ) (N₁ N₂ T ε : ℝ)
    (hT : 0 < T) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂) (hε : 0 ≤ ε) :
    occupiedMediumLogMagnitudePairs R M₁ M₂ N₁ N₂ T ε ⊆
      logMagnitudePairIndexRange T := by
  classical
  intro k hk
  rcases Finset.mem_image.mp hk with ⟨t, ht, rfl⟩
  have htR₂ :
      t ∈ largeValueR2 (R : Set ℝ) M₁ M₂ N₁ N₂ T ε :=
    (Finset.mem_filter.mp ht).2
  have hbounds :=
    logMagnitude_bounds_of_mem_largeValueR2 hT hN₁ hN₂ hε htR₂
  exact Finset.mem_product.mpr
    ⟨floor_logMagnitude_mem_indexRange hbounds.1,
      floor_logMagnitude_mem_indexRange hbounds.2⟩

/-- The number of occupied medium-value bin pairs is at most the exact
square of the rounded logarithmic length. -/
theorem card_occupiedMediumLogMagnitudePairs_le
    (R : Finset ℝ) (M₁ M₂ : ℂ → ℂ) (N₁ N₂ T ε : ℝ)
    (hT : 0 < T) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂) (hε : 0 ≤ ε) :
    (occupiedMediumLogMagnitudePairs R M₁ M₂ N₁ N₂ T ε).card ≤
      ((⌊Real.log T⌋ + 1).toNat) ^ 2 := by
  calc
    (occupiedMediumLogMagnitudePairs R M₁ M₂ N₁ N₂ T ε).card ≤
        (logMagnitudePairIndexRange T).card :=
      Finset.card_le_card
        (occupiedMediumLogMagnitudePairs_subset R M₁ M₂ N₁ N₂ T ε
          hT hN₁ hN₂ hε)
    _ = ((⌊Real.log T⌋ + 1).toNat) ^ 2 :=
      card_logMagnitudePairIndexRange T

def largeValuePartitionModule : ProofModule :=
  { name := "TypeII.LargeValuePartition"
    paperLocation := "Proof of Proposition 5.1, sets R₁, R₂, R₃ and logarithmic bins"
    purpose := "Make the measurable partition and size discretization precise."
    dependsOn := ["Definitions", "Mathlib measure theory and floor API"]
    status := .proved }

end
end TypeII
end ExactSemiprimes
