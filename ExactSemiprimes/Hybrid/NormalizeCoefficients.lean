import ExactSemiprimes.Assumptions

/-! # Coefficient normalization for the Guth--Maynard bounds -/

namespace ExactSemiprimes
namespace Hybrid

noncomputable section

/-- Divide a complex coefficient sequence by a positive real scale. -/
def normalizeCoefficient (a : ℕ → ℂ) (scale : ℝ) (n : ℕ) : ℂ :=
  a n / (scale : ℂ)

/-- Normalizing a coefficient whose norm is bounded by `scale` produces a
coefficient of norm at most one. -/
theorem norm_normalizeCoefficient_le_one {a : ℕ → ℂ} {scale : ℝ} {n : ℕ}
    (hscale : 0 < scale) (ha : ‖a n‖ ≤ scale) :
    ‖normalizeCoefficient a scale n‖ ≤ 1 := by
  rw [normalizeCoefficient, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hscale, div_le_one₀ hscale]
  exact ha

/-! ## The exact normalization used in the repaired paper -/

/-- The dyadic form of the standard divisor-subpower estimate needed by the
normalization argument.  This predicate is the local interface consumed by
the normalization lemmas.  `HybridDensity.globalDivisorSubpower` proves the
global estimate `d(n)^B \ll_{B,ρ} n^ρ`, and
`HybridDensity.exists_uniform_hasDyadicDivisorSubpowerBound` supplies this
predicate uniformly in `N` without adding an assumption. -/
def HasDyadicDivisorSubpowerBound (B D ρ : ℝ) (N : ℕ) : Prop :=
  ∀ n : ℕ, N < n → n ≤ 2 * N →
    (divisorCount n : ℝ) ^ B ≤
      D * (2 : ℝ) ^ ρ * (N : ℝ) ^ ρ

/-- The fixed coefficient scale `K = A₀ D 2^ρ` in the repaired paper. -/
def guthMaynardK (A₀ D ρ : ℝ) : ℝ :=
  A₀ * D * (2 : ℝ) ^ ρ

theorem guthMaynardK_pos {A₀ D ρ : ℝ} (hA₀ : 0 < A₀) (hD : 0 < D) :
    0 < guthMaynardK A₀ D ρ := by
  exact mul_pos (mul_pos hA₀ hD) (Real.rpow_pos_of_pos zero_lt_two ρ)

/-- The full normalization scale `K N^ρ`. -/
def guthMaynardNormalizationScale (A₀ D : ℝ) (N : ℕ) (ρ : ℝ) : ℝ :=
  guthMaynardK A₀ D ρ * (N : ℝ) ^ ρ

theorem guthMaynardNormalizationScale_pos {A₀ D ρ : ℝ} {N : ℕ}
    (hA₀ : 0 < A₀) (hD : 0 < D) (hN : 0 < N) :
    0 < guthMaynardNormalizationScale A₀ D N ρ := by
  exact mul_pos (guthMaynardK_pos hA₀ hD)
    (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) ρ)

/-- The coefficient used to turn
`∑_{N<n≤2N} aₙ n⁻¹⁻ⁱᵗ` into a Guth--Maynard exponential sum on the
*closed* support `[N,2N]`.  The value at `n=N` is zero, as are all values
outside `(N,2N]`; on the open-closed support this is

`(N/n) aₙ / (A₀ D 2^ρ N^ρ)`.
-/
def guthMaynardNormalizedCoefficient (a : ℕ → ℂ) (A₀ D : ℝ)
    (N : ℕ) (ρ : ℝ) (n : ℕ) : ℂ :=
  if N < n ∧ n ≤ 2 * N then
    ((((N : ℝ) / (n : ℝ) : ℝ) : ℂ) * a n) /
      (guthMaynardNormalizationScale A₀ D N ρ : ℂ)
  else
    0

@[simp]
theorem guthMaynardNormalizedCoefficient_at_left_endpoint
    (a : ℕ → ℂ) (A₀ D : ℝ) (N : ℕ) (ρ : ℝ) :
    guthMaynardNormalizedCoefficient a A₀ D N ρ N = 0 := by
  simp [guthMaynardNormalizedCoefficient]

theorem guthMaynardNormalizedCoefficient_eq_zero_of_outside
    {a : ℕ → ℂ} {A₀ D : ℝ} {N n : ℕ} {ρ : ℝ}
    (hn : ¬ (N < n ∧ n ≤ 2 * N)) :
    guthMaynardNormalizedCoefficient a A₀ D N ρ n = 0 := by
  simp [guthMaynardNormalizedCoefficient, hn]

/-- The published closed support is obtained from the paper's half-open
dyadic support by adjoining the left endpoint. -/
theorem closedDyadicInterval_eq_insert_dyadicInterval (N : ℕ) :
    closedDyadicInterval N =
      insert N (dyadicInterval (N : ℝ)) := by
  have htwo : (2 : ℝ) * (N : ℝ) = ((2 * N : ℕ) : ℝ) := by norm_num
  unfold closedDyadicInterval dyadicInterval
  rw [Nat.floor_natCast, htwo, Nat.floor_natCast]
  exact (Finset.Ioc_insert_left (by omega)).symm

/-- The explicit dyadic divisor estimate and the `(A₀,B)` coefficient bound
give the scale bound used in the normalization. -/
theorem norm_coefficient_le_guthMaynardNormalizationScale
    {a : ℕ → ℂ} {A₀ B D ρ : ℝ} {N n : ℕ}
    (hA₀ : 0 < A₀) (ha : IsDivisorBoundedByConstant B A₀ a)
    (hdiv : HasDyadicDivisorSubpowerBound B D ρ N)
    (hnLower : N < n) (hnUpper : n ≤ 2 * N) :
    ‖a n‖ ≤ guthMaynardNormalizationScale A₀ D N ρ := by
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hnLower
  calc
    ‖a n‖ ≤ A₀ * (divisorCount n : ℝ) ^ B := ha.2.2 n hnpos
    _ ≤ A₀ * (D * (2 : ℝ) ^ ρ * (N : ℝ) ^ ρ) :=
      mul_le_mul_of_nonneg_left (hdiv n hnLower hnUpper) (le_of_lt hA₀)
    _ = guthMaynardNormalizationScale A₀ D N ρ := by
      simp [guthMaynardNormalizationScale, guthMaynardK, mul_assoc]

/-- On the closed Guth--Maynard support `[N,2N]`, the repaired coefficient
has norm at most one.  The endpoint `N` is handled by its explicit zero
value; the remaining values use only the displayed dyadic divisor-subpower
hypothesis. -/
theorem norm_guthMaynardNormalizedCoefficient_le_one
    {a : ℕ → ℂ} {A₀ B D ρ : ℝ} {N n : ℕ}
    (hN : 1 ≤ N) (hA₀ : 0 < A₀) (hD : 0 < D)
    (ha : IsDivisorBoundedByConstant B A₀ a)
    (hdiv : HasDyadicDivisorSubpowerBound B D ρ N)
    (hn : n ∈ closedDyadicInterval N) :
    ‖guthMaynardNormalizedCoefficient a A₀ D N ρ n‖ ≤ 1 := by
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hnBounds : N ≤ n ∧ n ≤ 2 * N := Finset.mem_Icc.mp hn
  by_cases hleft : n = N
  · subst n
    simp
  · have hnLower : N < n := lt_of_le_of_ne hnBounds.1 (Ne.symm hleft)
    have hnposNat : 0 < n := lt_trans hNpos hnLower
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hnposNat
    have hscalePos : 0 < guthMaynardNormalizationScale A₀ D N ρ :=
      guthMaynardNormalizationScale_pos hA₀ hD hNpos
    have hratioNonneg : 0 ≤ (N : ℝ) / (n : ℝ) := by positivity
    have hcoeff := norm_coefficient_le_guthMaynardNormalizationScale
      hA₀ ha hdiv hnLower hnBounds.2
    simp only [guthMaynardNormalizedCoefficient, hnLower, hnBounds.2,
      and_self, ↓reduceIte]
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hratioNonneg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hscalePos]
    calc
      ((N : ℝ) / (n : ℝ) * ‖a n‖) /
          guthMaynardNormalizationScale A₀ D N ρ
          ≤ ((N : ℝ) / (n : ℝ) *
              guthMaynardNormalizationScale A₀ D N ρ) /
              guthMaynardNormalizationScale A₀ D N ρ := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcoeff hratioNonneg)
              (le_of_lt hscalePos)
      _ = (N : ℝ) / (n : ℝ) := by
        field_simp [ne_of_gt hscalePos]
      _ ≤ 1 := (div_le_one₀ hnpos).2 (by exact_mod_cast hnBounds.1)

/-- Termwise, the normalized negative-frequency sum is exactly the original
Dirichlet polynomial multiplied by `N/(K N^ρ)`. -/
theorem guthMaynardNormalizedCoefficient_term_identity
    {a : ℕ → ℂ} {A₀ D ρ t : ℝ} {N n : ℕ}
    (hN : 0 < N) (hA₀ : 0 < A₀) (hD : 0 < D)
    (hnLower : N < n) (hnUpper : n ≤ 2 * N) :
    guthMaynardNormalizedCoefficient a A₀ D N ρ n *
        (n : ℂ) ^ (((-t : ℝ) : ℂ) * Complex.I) =
      ((N : ℂ) / (guthMaynardNormalizationScale A₀ D N ρ : ℂ)) *
        (a n * (n : ℂ) ^ (-(onePlusIT t))) := by
  have hnpos : 0 < n := lt_trans hN hnLower
  have hnzero : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hnpos)
  have hscalePos : 0 < guthMaynardNormalizationScale A₀ D N ρ :=
    guthMaynardNormalizationScale_pos hA₀ hD hN
  have hscaleZero : (guthMaynardNormalizationScale A₀ D N ρ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hscalePos)
  have hexponent :
      -(onePlusIT t) =
        (-1 : ℂ) + (((-t : ℝ) : ℂ) * Complex.I) := by
    simp only [onePlusIT]
    push_cast
    ring
  simp only [guthMaynardNormalizedCoefficient, hnLower, hnUpper,
    and_self, ↓reduceIte]
  rw [hexponent, Complex.cpow_add _ _ hnzero, Complex.cpow_neg_one]
  push_cast
  field_simp [hnzero, hscaleZero]

/-- Summing the termwise identity, with the zero coefficient at the newly
adjoined endpoint, gives the exact normalization formula used before applying
the Guth--Maynard theorem. -/
theorem oscillatoryDirichletSum_normalized_negative
    (a : ℕ → ℂ) (A₀ D ρ t : ℝ) (N : ℕ)
    (hN : 0 < N) (hA₀ : 0 < A₀) (hD : 0 < D) :
    oscillatoryDirichletSum
        (guthMaynardNormalizedCoefficient a A₀ D N ρ) N (-t) =
      ((N : ℂ) / (guthMaynardNormalizationScale A₀ D N ρ : ℂ)) *
        dyadicDirichletPolynomial a (N : ℝ) (onePlusIT t) := by
  rw [oscillatoryDirichletSum,
    closedDyadicInterval_eq_insert_dyadicInterval]
  have hNnot : N ∉ dyadicInterval (N : ℝ) := by
    rw [mem_dyadicInterval (Nat.cast_nonneg N)]
    exact fun h ↦ (lt_irrefl (N : ℝ)) h.1
  rw [Finset.sum_insert hNnot]
  simp only [guthMaynardNormalizedCoefficient_at_left_endpoint,
    zero_mul, zero_add, dyadicDirichletPolynomial, dirichletPolynomial,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnRange : InDyadicRange (N : ℝ) n :=
    (mem_dyadicInterval (N := (N : ℝ)) (Nat.cast_nonneg N)).mp hn
  have hnLower : N < n := by exact_mod_cast hnRange.1
  have hnUpper : n ≤ 2 * N := by exact_mod_cast hnRange.2
  exact guthMaynardNormalizedCoefficient_term_identity
    hN hA₀ hD hnLower hnUpper

/-! ## Reflection from negative to positive frequency -/

/-- Reflect a height in `[0,T]`. -/
def reflectedHeight (T t : ℝ) : ℝ := T - t

/-- Multiply a coefficient by the unit phase `n^{-iT}`. -/
def phaseReflectedCoefficient (b : ℕ → ℂ) (T : ℝ) (n : ℕ) : ℂ :=
  b n * (n : ℂ) ^ (-((T : ℂ) * Complex.I))

theorem reflectedHeight_mem_Icc {T t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    reflectedHeight T t ∈ Set.Icc (0 : ℝ) T := by
  constructor <;> simp only [reflectedHeight] <;> linarith [ht.1, ht.2]

theorem reflectedHeight_injective (T : ℝ) :
    Function.Injective (reflectedHeight T) := by
  intro t u h
  simp only [reflectedHeight] at h
  linarith

/-- Reflect every point of a finite height set. -/
def reflectedHeightFinset (T : ℝ) (R : Finset ℝ) : Finset ℝ :=
  R.image (reflectedHeight T)

@[simp]
theorem card_reflectedHeightFinset (T : ℝ) (R : Finset ℝ) :
    (reflectedHeightFinset T R).card = R.card := by
  exact Finset.card_image_of_injective R (reflectedHeight_injective T)

theorem mem_reflectedHeightFinset_Icc {T : ℝ} {R : Finset ℝ}
    (hR : ∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) :
    ∀ u ∈ reflectedHeightFinset T R, u ∈ Set.Icc (0 : ℝ) T := by
  intro u hu
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
  exact reflectedHeight_mem_Icc (hR t ht)

@[simp]
theorem abs_reflectedHeight_sub_reflectedHeight (T t u : ℝ) :
    |reflectedHeight T t - reflectedHeight T u| = |t - u| := by
  rw [abs_sub_comm]
  congr 1
  simp [reflectedHeight]

/-- Reflection preserves one-spacing as well as cardinality and the height
interval. -/
theorem isOneSpaced_reflectedHeightFinset {T : ℝ} {R : Finset ℝ}
    (hR : IsOneSpaced (↑R : Set ℝ)) :
    IsOneSpaced (↑(reflectedHeightFinset T R) : Set ℝ) := by
  intro x hx y hy hxy
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hy
  rw [abs_reflectedHeight_sub_reflectedHeight]
  apply hR ht hu
  intro htu
  apply hxy
  simp [htu]

/-- The phase change does not alter coefficient norms. -/
@[simp]
theorem norm_phaseReflectedCoefficient {b : ℕ → ℂ} {T : ℝ} {n : ℕ}
    (hn : 0 < n) :
    ‖phaseReflectedCoefficient b T n‖ = ‖b n‖ := by
  rw [phaseReflectedCoefficient, norm_mul,
    Complex.norm_natCast_cpow_of_pos hn]
  simp

/-- Reflection preserves the exact Dirichlet-polynomial value after changing
the sign of the height.  This is the precise identity behind the paper's
replacement `t ↦ T-t`, `bₙ ↦ bₙ n^{-iT}`. -/
theorem oscillatoryDirichletSum_phase_reflection
    (b : ℕ → ℂ) (N : ℕ) (T t : ℝ) (hN : 1 ≤ N) :
    oscillatoryDirichletSum (phaseReflectedCoefficient b T) N
        (reflectedHeight T t) =
      oscillatoryDirichletSum b N (-t) := by
  apply Finset.sum_congr rfl
  intro n hn
  have hnLower : N ≤ n := (Finset.mem_Icc.mp hn).1
  have hnpos : 0 < n := lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hN) hnLower
  have hnzero : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hnpos)
  simp only [phaseReflectedCoefficient, reflectedHeight]
  rw [mul_assoc, ← Complex.cpow_add _ _ hnzero]
  congr 1
  push_cast
  ring_nf

/-- Combining normalization and phase reflection gives the exact transformed
sum at the positive reflected height. -/
theorem oscillatoryDirichletSum_normalized_phase_reflection
    (a : ℕ → ℂ) (A₀ D ρ T t : ℝ) (N : ℕ)
    (hN : 1 ≤ N) (hA₀ : 0 < A₀) (hD : 0 < D) :
    oscillatoryDirichletSum
        (phaseReflectedCoefficient
          (guthMaynardNormalizedCoefficient a A₀ D N ρ) T)
        N (reflectedHeight T t) =
      ((N : ℂ) / (guthMaynardNormalizationScale A₀ D N ρ : ℂ)) *
        dyadicDirichletPolynomial a (N : ℝ) (onePlusIT t) := by
  rw [oscillatoryDirichletSum_phase_reflection _ _ _ _ hN]
  exact oscillatoryDirichletSum_normalized_negative a A₀ D ρ t N
    (lt_of_lt_of_le Nat.zero_lt_one hN) hA₀ hD

/-- Norm form of the exact transformed-sum identity. -/
theorem norm_oscillatoryDirichletSum_normalized_phase_reflection
    (a : ℕ → ℂ) (A₀ D ρ T t : ℝ) (N : ℕ)
    (hN : 1 ≤ N) (hA₀ : 0 < A₀) (hD : 0 < D) :
    ‖oscillatoryDirichletSum
        (phaseReflectedCoefficient
          (guthMaynardNormalizedCoefficient a A₀ D N ρ) T)
        N (reflectedHeight T t)‖ =
      ((N : ℝ) / guthMaynardNormalizationScale A₀ D N ρ) *
        ‖dyadicDirichletPolynomial a (N : ℝ) (onePlusIT t)‖ := by
  rw [oscillatoryDirichletSum_normalized_phase_reflection
    a A₀ D ρ T t N hN hA₀ hD, norm_mul, norm_div]
  have hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hscalePos : 0 < guthMaynardNormalizationScale A₀ D N ρ :=
    guthMaynardNormalizationScale_pos hA₀ hD hNpos
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscalePos]

/-- A large value of the original polynomial gives the correspondingly
rescaled large value of the reflected Guth--Maynard sum.  Rewriting the
left-hand side as `K⁻¹ N^(1-σ-ρ)` is a separate elementary real-power step. -/
theorem largeValue_of_normalized_phase_reflection
    {a : ℕ → ℂ} {A₀ D ρ T t σ : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hA₀ : 0 < A₀) (hD : 0 < D)
    (hlarge : (N : ℝ) ^ (-σ) <
      ‖dyadicDirichletPolynomial a (N : ℝ) (onePlusIT t)‖) :
    ((N : ℝ) / guthMaynardNormalizationScale A₀ D N ρ) *
        (N : ℝ) ^ (-σ) <
      ‖oscillatoryDirichletSum
        (phaseReflectedCoefficient
          (guthMaynardNormalizedCoefficient a A₀ D N ρ) T)
        N (reflectedHeight T t)‖ := by
  rw [norm_oscillatoryDirichletSum_normalized_phase_reflection
    a A₀ D ρ T t N hN hA₀ hD]
  apply mul_lt_mul_of_pos_left hlarge
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr
    (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hscalePos : 0 < guthMaynardNormalizationScale A₀ D N ρ :=
    guthMaynardNormalizationScale_pos hA₀ hD
      (lt_of_lt_of_le Nat.zero_lt_one hN)
  positivity

/-! ## Elementary amplitude algebra -/

/-- Exact real-power identity for the normalized large-value threshold:

`N / (K N^ρ) · N^{-σ} = K⁻¹ N^{1-σ-ρ}`.
-/
theorem normalizationAmplitude_identity {x K ρ σ : ℝ}
    (hx : 0 < x) (hK : 0 < K) :
    x / (K * x ^ ρ) * x ^ (-σ) =
      K⁻¹ * x ^ (1 - σ - ρ) := by
  rw [show 1 - σ - ρ = 1 + (-σ + -ρ) by ring,
    Real.rpow_add hx, Real.rpow_one, Real.rpow_add hx,
    Real.rpow_neg hx.le, Real.rpow_neg hx.le]
  have hxρ : x ^ ρ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx ρ)
  field_simp [ne_of_gt hx, ne_of_gt hK, hxρ]

/-- The preceding identity with the paper's explicit
`K = A₀ D 2^ρ`. -/
theorem guthMaynardNormalizationAmplitude_identity
    {A₀ D ρ σ : ℝ} {N : ℕ}
    (hN : 0 < N) (hA₀ : 0 < A₀) (hD : 0 < D) :
    (N : ℝ) / guthMaynardNormalizationScale A₀ D N ρ *
        (N : ℝ) ^ (-σ) =
      (guthMaynardK A₀ D ρ)⁻¹ * (N : ℝ) ^ (1 - σ - ρ) := by
  rw [guthMaynardNormalizationScale]
  exact normalizationAmplitude_identity (Nat.cast_pos.mpr hN)
    (guthMaynardK_pos hA₀ hD)

/-- If the fixed factor `K` has been absorbed into `N^ρ`, then the normalized
threshold is at least `N^(1-σ-2ρ)`. -/
theorem rpow_threshold_le_normalizationAmplitude
    {x K ρ σ : ℝ} (hx : 0 < x) (hK : 0 < K)
    (hKle : K ≤ x ^ ρ) :
    x ^ (1 - σ - 2 * ρ) ≤ K⁻¹ * x ^ (1 - σ - ρ) := by
  have hxρpos : 0 < x ^ ρ := Real.rpow_pos_of_pos hx ρ
  have hinv : (x ^ ρ)⁻¹ ≤ K⁻¹ :=
    (inv_le_inv₀ hxρpos hK).2 hKle
  have hsplit :
      x ^ (-ρ) * x ^ (1 - σ - ρ) = x ^ (1 - σ - 2 * ρ) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  calc
    x ^ (1 - σ - 2 * ρ)
        = (x ^ ρ)⁻¹ * x ^ (1 - σ - ρ) := by
          rw [← Real.rpow_neg hx.le]
          exact hsplit.symm
    _ ≤ K⁻¹ * x ^ (1 - σ - ρ) :=
      mul_le_mul_of_nonneg_right hinv
        (Real.rpow_nonneg (le_of_lt hx) (1 - σ - ρ))

/-- Corollary in the exact form used by the repaired proof: after the
eventual inequality `K ≤ N^ρ`, a large value of `A(1+it)` produces a
Guth--Maynard sum larger than `N^(1-σ-2ρ)`. -/
theorem largeValue_threshold_of_normalized_phase_reflection
    {a : ℕ → ℂ} {A₀ D ρ T t σ : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hA₀ : 0 < A₀) (hD : 0 < D)
    (hKle : guthMaynardK A₀ D ρ ≤ (N : ℝ) ^ ρ)
    (hlarge : (N : ℝ) ^ (-σ) <
      ‖dyadicDirichletPolynomial a (N : ℝ) (onePlusIT t)‖) :
    (N : ℝ) ^ (1 - σ - 2 * ρ) <
      ‖oscillatoryDirichletSum
        (phaseReflectedCoefficient
          (guthMaynardNormalizedCoefficient a A₀ D N ρ) T)
        N (reflectedHeight T t)‖ := by
  have hNposNat : 0 < N := lt_of_lt_of_le Nat.zero_lt_one hN
  have hNpos : 0 < (N : ℝ) := Nat.cast_pos.mpr hNposNat
  have hlargeNormalized := largeValue_of_normalized_phase_reflection
    (a := a) (A₀ := A₀) (D := D) (ρ := ρ) (T := T) (t := t)
    (σ := σ) hN hA₀ hD hlarge
  rw [guthMaynardNormalizationAmplitude_identity
    hNposNat hA₀ hD] at hlargeNormalized
  exact (rpow_threshold_le_normalizationAmplitude hNpos
    (guthMaynardK_pos hA₀ hD) hKle).trans_lt hlargeNormalized

/-- The transformed coefficients retain the unit bound on the published
closed support. -/
theorem norm_phaseReflected_guthMaynardNormalizedCoefficient_le_one
    {a : ℕ → ℂ} {A₀ B D ρ T : ℝ} {N n : ℕ}
    (hN : 1 ≤ N) (hA₀ : 0 < A₀) (hD : 0 < D)
    (ha : IsDivisorBoundedByConstant B A₀ a)
    (hdiv : HasDyadicDivisorSubpowerBound B D ρ N)
    (hn : n ∈ closedDyadicInterval N) :
    ‖phaseReflectedCoefficient
        (guthMaynardNormalizedCoefficient a A₀ D N ρ) T n‖ ≤ 1 := by
  have hnLower : N ≤ n := (Finset.mem_Icc.mp hn).1
  have hnpos : 0 < n :=
    lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hN) hnLower
  rw [norm_phaseReflectedCoefficient hnpos]
  exact norm_guthMaynardNormalizedCoefficient_le_one
    hN hA₀ hD ha hdiv hn

def normalizeCoefficientsModule : ProofModule :=
  { name := "Hybrid.NormalizeCoefficients"
    paperLocation := "Proof of Lemma 4.3, coefficient-normalization paragraph"
    purpose :=
      "Formalize the A₀,D,K normalization, phase reflection, unit coefficient bound, and exact amplitude rescaling."
    dependsOn := ["Definitions", "Mathlib/local divisor-bound estimate"]
    status := .proved }

end

end Hybrid
end ExactSemiprimes
