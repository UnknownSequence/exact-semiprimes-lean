import ExactSemiprimes.Definitions

/-!
# Naturalizing real dyadic scales

The decomposition theorem of Matomäki--Teräväinen uses positive real
scales, while `TypeIIEstimateStatement` is stated at natural-number scales.
A real dyadic interval is not, in general, a dyadic interval at one natural
scale.  This file gives the exact replacement: it is the disjoint union of
the interval at `floor M` and at most one boundary point, and that boundary
point can be represented by a coefficient mask at the natural scale
`2 * floor M`.

Thus no rounding equality is assumed.  Every real-scale polynomial is
exactly a sum of two natural-scale polynomials, the divisor-bound witnesses
are unchanged, and both natural scales stay within a factor two of the
original scale.
-/

namespace ExactSemiprimes
namespace TypeII

open scoped BigOperators

noncomputable section

/-- The principal natural scale attached to a nonnegative real scale. -/
def naturalDyadicCoreScale (M : ℝ) : ℕ := ⌊M⌋₊

/-- The second natural scale used to hold the possible upper endpoint left
over after replacing `M` by `floor M`. -/
def naturalDyadicBoundaryScale (M : ℝ) : ℕ :=
  2 * naturalDyadicCoreScale M

/-- The part of the real dyadic interval not already present at the core
natural scale.  It has cardinality at most one, although the exact
two-polynomial bridge below only needs its support inclusion. -/
def dyadicRoundingBoundary (M : ℝ) : Finset ℕ :=
  dyadicInterval M \ dyadicInterval (naturalDyadicCoreScale M : ℝ)

/-- Mask a coefficient sequence to the possible rounding boundary. -/
def dyadicBoundaryCoefficient (a : ℕ → ℂ) (M : ℝ) (n : ℕ) : ℂ :=
  if n ∈ dyadicRoundingBoundary M then a n else 0

/-- Rounding down the scale only removes elements from the upper endpoint;
it never introduces a new integer into the dyadic interval. -/
theorem dyadicInterval_floor_subset {M : ℝ} (hM : 0 ≤ M) :
    dyadicInterval (naturalDyadicCoreScale M : ℝ) ⊆ dyadicInterval M := by
  intro n hn
  have hfloor : (naturalDyadicCoreScale M : ℝ) ≤ M := by
    exact Nat.floor_le hM
  have hceil : M < (naturalDyadicCoreScale M : ℝ) + 1 := by
    exact Nat.lt_floor_add_one M
  have hnrange :=
    (mem_dyadicInterval (Nat.cast_nonneg (naturalDyadicCoreScale M))).mp hn
  apply (mem_dyadicInterval hM).mpr
  constructor
  · have hnstep : (naturalDyadicCoreScale M : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast hnrange.1
    exact hceil.trans_le hnstep
  · calc
      (n : ℝ) ≤ 2 * (naturalDyadicCoreScale M : ℝ) := hnrange.2
      _ ≤ 2 * M := by linarith

/-- Once `M ≥ 1`, every integer lost at the upper endpoint belongs to the
dyadic interval at the doubled floor scale. -/
theorem dyadicRoundingBoundary_subset_boundaryInterval
    {M : ℝ} (hM : 1 ≤ M) :
    dyadicRoundingBoundary M ⊆
      dyadicInterval (naturalDyadicBoundaryScale M : ℝ) := by
  intro n hn
  have hM0 : 0 ≤ M := by positivity
  have hN1 : 1 ≤ naturalDyadicCoreScale M := by
    apply (Nat.le_floor_iff hM0).mpr
    exact_mod_cast hM
  have hMupper : M < (naturalDyadicCoreScale M : ℝ) + 1 :=
    Nat.lt_floor_add_one M
  have hnM := (mem_dyadicInterval hM0).mp (Finset.mem_sdiff.mp hn).1
  have hnnot := (Finset.mem_sdiff.mp hn).2
  have hnLowerCore :
      (naturalDyadicCoreScale M : ℝ) < (n : ℝ) := by
    exact (Nat.floor_le hM0).trans_lt hnM.1
  have hnAboveCore :
      2 * (naturalDyadicCoreScale M : ℝ) < (n : ℝ) := by
    by_contra h
    apply hnnot
    exact (mem_dyadicInterval
      (Nat.cast_nonneg (naturalDyadicCoreScale M))).mpr
        ⟨hnLowerCore, le_of_not_gt h⟩
  have hnUpperStrict :
      (n : ℝ) < 2 * (naturalDyadicCoreScale M : ℝ) + 2 := by
    calc
      (n : ℝ) ≤ 2 * M := hnM.2
      _ < 2 * (naturalDyadicCoreScale M : ℝ) + 2 := by linarith
  have hnUpperStep :
      n ≤ 2 * naturalDyadicCoreScale M + 1 := by
    have hnUpperNatStrict :
        n < 2 * naturalDyadicCoreScale M + 2 := by
      exact_mod_cast hnUpperStrict
    omega
  have hnUpper :
      (n : ℝ) ≤ 2 * (naturalDyadicBoundaryScale M : ℝ) := by
    have hnat :
        2 * naturalDyadicCoreScale M + 1 ≤
          2 * naturalDyadicBoundaryScale M := by
      simp only [naturalDyadicBoundaryScale]
      omega
    exact_mod_cast hnUpperStep.trans hnat
  apply (mem_dyadicInterval
    (Nat.cast_nonneg (naturalDyadicBoundaryScale M))).mpr
  constructor
  · simpa only [naturalDyadicBoundaryScale, Nat.cast_mul,
      Nat.cast_ofNat] using hnAboveCore
  · exact hnUpper

/-- More precisely, the rounding boundary contains at most the single
integer `2 * floor M + 1`. -/
theorem dyadicRoundingBoundary_subset_singleton
    {M : ℝ} (hM : 0 ≤ M) :
    dyadicRoundingBoundary M ⊆
      {2 * naturalDyadicCoreScale M + 1} := by
  intro n hn
  have hnM := (mem_dyadicInterval hM).mp (Finset.mem_sdiff.mp hn).1
  have hnnot := (Finset.mem_sdiff.mp hn).2
  have hMupper : M < (naturalDyadicCoreScale M : ℝ) + 1 :=
    Nat.lt_floor_add_one M
  have hnLowerCore :
      (naturalDyadicCoreScale M : ℝ) < (n : ℝ) :=
    (Nat.floor_le hM).trans_lt hnM.1
  have hnAboveCore :
      2 * naturalDyadicCoreScale M < n := by
    by_contra h
    apply hnnot
    apply (mem_dyadicInterval
      (Nat.cast_nonneg (naturalDyadicCoreScale M))).mpr
    constructor
    · exact hnLowerCore
    · exact_mod_cast le_of_not_gt h
  have hnUpperStrict :
      (n : ℝ) < 2 * (naturalDyadicCoreScale M : ℝ) + 2 := by
    calc
      (n : ℝ) ≤ 2 * M := hnM.2
      _ < 2 * (naturalDyadicCoreScale M : ℝ) + 2 := by linarith
  have hnUpperNat : n < 2 * naturalDyadicCoreScale M + 2 := by
    exact_mod_cast hnUpperStrict
  have hnEq : n = 2 * naturalDyadicCoreScale M + 1 := by omega
  exact Finset.mem_singleton.mpr hnEq

/-- In particular, a real dyadic interval differs from its floor-scale
natural interval by at most one endpoint. -/
theorem card_dyadicRoundingBoundary_le_one {M : ℝ} (hM : 0 ≤ M) :
    (dyadicRoundingBoundary M).card ≤ 1 := by
  calc
    (dyadicRoundingBoundary M).card ≤
        ({2 * naturalDyadicCoreScale M + 1} : Finset ℕ).card :=
      Finset.card_le_card (dyadicRoundingBoundary_subset_singleton hM)
    _ = 1 := by simp

/-- The exact two-block polynomial bridge.  The second summand is zero when
rounding creates no upper boundary point. -/
theorem dyadicDirichletPolynomial_realScale_eq_two_naturalScales
    {M : ℝ} (hM : 1 ≤ M) (a : ℕ → ℂ) (s : ℂ) :
    dyadicDirichletPolynomial a M s =
      dyadicDirichletPolynomial a (naturalDyadicCoreScale M : ℝ) s +
        dyadicDirichletPolynomial (dyadicBoundaryCoefficient a M)
          (naturalDyadicBoundaryScale M : ℝ) s := by
  classical
  have hcore := dyadicInterval_floor_subset (M := M) (by positivity)
  have hboundary :=
    dyadicRoundingBoundary_subset_boundaryInterval (M := M) hM
  unfold dyadicDirichletPolynomial
  have hsplit :
      dirichletPolynomial a (dyadicRoundingBoundary M) s +
          dirichletPolynomial a
            (dyadicInterval (naturalDyadicCoreScale M : ℝ)) s =
        dirichletPolynomial a (dyadicInterval M) s := by
    unfold dirichletPolynomial dyadicRoundingBoundary
    exact Finset.sum_sdiff hcore
  have hboundaryPolynomial :
      dirichletPolynomial a (dyadicRoundingBoundary M) s =
        dirichletPolynomial (dyadicBoundaryCoefficient a M)
          (dyadicInterval (naturalDyadicBoundaryScale M : ℝ)) s := by
    unfold dirichletPolynomial
    apply Finset.sum_subset_zero_on_sdiff hboundary
    · intro n hn
      have hnnot : n ∉ dyadicRoundingBoundary M :=
        (Finset.mem_sdiff.mp hn).2
      simp [dyadicBoundaryCoefficient, hnnot]
    · intro n hn
      simp [dyadicBoundaryCoefficient, hn]
  rw [← hsplit, hboundaryPolynomial]
  ring

/-- Applying the two-block identity to both factors gives the exact four
natural-scale products to which `TypeIIEstimateStatement` can be applied.
There is no endpoint error term. -/
theorem realScale_typeII_product_eq_four_naturalScale_products
    {M₁ M₂ : ℝ} (hM₁ : 1 ≤ M₁) (hM₂ : 1 ≤ M₂)
    (a₁ a₂ : ℕ → ℂ) (s : ℂ) :
    dyadicDirichletPolynomial a₁ M₁ s *
        dyadicDirichletPolynomial a₂ M₂ s =
      dyadicDirichletPolynomial a₁
          (naturalDyadicCoreScale M₁ : ℝ) s *
        dyadicDirichletPolynomial a₂
          (naturalDyadicCoreScale M₂ : ℝ) s +
      dyadicDirichletPolynomial a₁
          (naturalDyadicCoreScale M₁ : ℝ) s *
        dyadicDirichletPolynomial (dyadicBoundaryCoefficient a₂ M₂)
          (naturalDyadicBoundaryScale M₂ : ℝ) s +
      dyadicDirichletPolynomial (dyadicBoundaryCoefficient a₁ M₁)
          (naturalDyadicBoundaryScale M₁ : ℝ) s *
        dyadicDirichletPolynomial a₂
          (naturalDyadicCoreScale M₂ : ℝ) s +
      dyadicDirichletPolynomial (dyadicBoundaryCoefficient a₁ M₁)
          (naturalDyadicBoundaryScale M₁ : ℝ) s *
        dyadicDirichletPolynomial (dyadicBoundaryCoefficient a₂ M₂)
          (naturalDyadicBoundaryScale M₂ : ℝ) s := by
  rw [dyadicDirichletPolynomial_realScale_eq_two_naturalScales hM₁,
    dyadicDirichletPolynomial_realScale_eq_two_naturalScales hM₂]
  ring

/-- Coefficient masking does not enlarge the divisor-bound constant or
exponent. -/
theorem dyadicBoundaryCoefficient_isDivisorBoundedByConstant
    {B A M : ℝ} {a : ℕ → ℂ}
    (ha : IsDivisorBoundedByConstant B A a) :
    IsDivisorBoundedByConstant B A (dyadicBoundaryCoefficient a M) := by
  refine ⟨ha.1, ha.2.1, ?_⟩
  intro n hn
  by_cases hboundary : n ∈ dyadicRoundingBoundary M
  · simpa [dyadicBoundaryCoefficient, hboundary] using ha.2.2 n hn
  · simp only [dyadicBoundaryCoefficient, hboundary, ite_false, norm_zero]
    exact mul_nonneg ha.2.1.le
      (Real.rpow_nonneg (Nat.cast_nonneg (divisorCount n)) B)

/-- For `M ≥ 2`, its floor loses at most a factor two. -/
theorem half_le_naturalDyadicCoreScale {M : ℝ} (hM : 2 ≤ M) :
    M / 2 ≤ (naturalDyadicCoreScale M : ℝ) := by
  have hfloor : M - 1 < (naturalDyadicCoreScale M : ℝ) :=
    Nat.sub_one_lt_floor M
  linarith

/-- Both natural scales in the exact bridge remain between `M/2` and
`2M`. -/
theorem naturalDyadicScale_comparable
    {M : ℝ} (hM : 2 ≤ M) {N : ℕ}
    (hN : N = naturalDyadicCoreScale M ∨
      N = naturalDyadicBoundaryScale M) :
    M / 2 ≤ (N : ℝ) ∧ (N : ℝ) ≤ 2 * M := by
  have hcoreLower := half_le_naturalDyadicCoreScale hM
  have hcoreUpper : (naturalDyadicCoreScale M : ℝ) ≤ M :=
    Nat.floor_le (by positivity)
  rcases hN with rfl | rfl
  · exact ⟨hcoreLower, hcoreUpper.trans (by linarith)⟩
  · constructor
    · simp only [naturalDyadicBoundaryScale, Nat.cast_mul,
        Nat.cast_ofNat]
      linarith
    · simp only [naturalDyadicBoundaryScale, Nat.cast_mul,
        Nat.cast_ofNat]
      linarith

/-- Consequently, choosing either natural block for each of two real
scales changes their product length by at most a factor four. -/
theorem naturalDyadicScale_product_comparable
    {M₁ M₂ : ℝ} (hM₁ : 2 ≤ M₁) (hM₂ : 2 ≤ M₂)
    {N₁ N₂ : ℕ}
    (hN₁ : N₁ = naturalDyadicCoreScale M₁ ∨
      N₁ = naturalDyadicBoundaryScale M₁)
    (hN₂ : N₂ = naturalDyadicCoreScale M₂ ∨
      N₂ = naturalDyadicBoundaryScale M₂) :
    M₁ * M₂ / 4 ≤ (N₁ : ℝ) * (N₂ : ℝ) ∧
      (N₁ : ℝ) * (N₂ : ℝ) ≤ 4 * (M₁ * M₂) := by
  obtain ⟨hN₁lower, hN₁upper⟩ :=
    naturalDyadicScale_comparable hM₁ hN₁
  obtain ⟨hN₂lower, hN₂upper⟩ :=
    naturalDyadicScale_comparable hM₂ hN₂
  have hM₁nonneg : 0 ≤ M₁ := by positivity
  have hM₂nonneg : 0 ≤ M₂ := by positivity
  constructor
  · calc
      M₁ * M₂ / 4 = (M₁ / 2) * (M₂ / 2) := by ring
      _ ≤ (N₁ : ℝ) * (N₂ : ℝ) :=
        mul_le_mul hN₁lower hN₂lower (by positivity) (by positivity)
  · calc
      (N₁ : ℝ) * (N₂ : ℝ) ≤ (2 * M₁) * (2 * M₂) :=
        mul_le_mul hN₁upper hN₂upper (Nat.cast_nonneg N₂)
          (by positivity)
      _ = 4 * (M₁ * M₂) := by ring

/-- The same product comparison after normalization by a positive Perron
height.  This is the form directly used by the logarithmic product-length
hypotheses of `TypeIIEstimateStatement`. -/
theorem naturalDyadicScale_product_ratio_comparable
    {M₁ M₂ T : ℝ} (hM₁ : 2 ≤ M₁) (hM₂ : 2 ≤ M₂)
    (hT : 0 < T) {N₁ N₂ : ℕ}
    (hN₁ : N₁ = naturalDyadicCoreScale M₁ ∨
      N₁ = naturalDyadicBoundaryScale M₁)
    (hN₂ : N₂ = naturalDyadicCoreScale M₂ ∨
      N₂ = naturalDyadicBoundaryScale M₂) :
    (M₁ * M₂ / T) / 4 ≤ ((N₁ : ℝ) * (N₂ : ℝ)) / T ∧
      ((N₁ : ℝ) * (N₂ : ℝ)) / T ≤ 4 * (M₁ * M₂ / T) := by
  obtain ⟨hlower, hupper⟩ :=
    naturalDyadicScale_product_comparable hM₁ hM₂ hN₁ hN₂
  constructor
  · calc
      (M₁ * M₂ / T) / 4 = (M₁ * M₂ / 4) / T := by ring
      _ ≤ ((N₁ : ℝ) * (N₂ : ℝ)) / T :=
        div_le_div_of_nonneg_right hlower hT.le
  · calc
      ((N₁ : ℝ) * (N₂ : ℝ)) / T ≤
          (4 * (M₁ * M₂)) / T :=
        div_le_div_of_nonneg_right hupper hT.le
      _ = 4 * (M₁ * M₂ / T) := by ring

/-- A single exact natural scale cannot replace an arbitrary real scale.
The scale `3/2` is the smallest concrete obstruction: its interval is
`{2,3}`, whereas any natural dyadic interval containing `2` starts at scale
at most `1` and therefore cannot contain `3`. -/
theorem no_single_natural_scale_for_three_halves :
    ¬ ∃ N : ℕ,
      dyadicInterval (3 / 2 : ℝ) = dyadicInterval (N : ℝ) := by
  rintro ⟨N, hN⟩
  have htwo : 2 ∈ dyadicInterval (3 / 2 : ℝ) := by
    norm_num [dyadicInterval]
  have hthree : 3 ∈ dyadicInterval (3 / 2 : ℝ) := by
    norm_num [dyadicInterval]
  rw [hN] at htwo hthree
  have htwoRange :=
    (mem_dyadicInterval (Nat.cast_nonneg N)).mp htwo
  have hthreeRange :=
    (mem_dyadicInterval (Nat.cast_nonneg N)).mp hthree
  have hNlt : N < 2 := by
    exact_mod_cast htwoRange.1
  have hNlarge : 3 ≤ 2 * N := by
    exact_mod_cast hthreeRange.2
  omega

/-- Registry entry for the real-to-natural dyadic bridge. -/
def realScaleNaturalizationModule : ProofModule :=
  { name := "TypeII.RealScaleNaturalization"
    paperLocation :=
      "Interface between MT23 Proposition 2.2(iii) and Proposition 5.1"
    purpose :=
      "Replace each positive real dyadic scale exactly by two natural dyadic blocks, preserve divisor bounds, and control both individual and product scale distortion by absolute factors."
    dependsOn := ["Definitions"]
    status := .proved }

end
end TypeII
end ExactSemiprimes
