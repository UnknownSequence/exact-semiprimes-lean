import ExactSemiprimes.Hybrid.DiscreteToMeasure

/-!
# Unit-cell discretization of nonnegative integrals

This module proves the deterministic bridge used after the discrete Type-II
large-value estimates.  It selects one representative from every positive-
measure unit cell, splits the cells by parity, and thereby converts a uniform
bound for finite one-spaced samples into an integral bound with factor two.
-/

namespace ExactSemiprimes.Hybrid

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

def unitCell (U : Set ℝ) (k : ℤ) : Set ℝ :=
  U ∩ Set.Ico (k : ℝ) ((k : ℝ) + 1)

theorem measurableSet_unitCell {U : Set ℝ} (hU : MeasurableSet U) (k : ℤ) :
    MeasurableSet (unitCell U k) :=
  hU.inter measurableSet_Ico

theorem volume_unitCell_le_one (U : Set ℝ) (k : ℤ) :
    volume (unitCell U k) ≤ 1 := by
  calc
    volume (unitCell U k) ≤ volume (Set.Ico (k : ℝ) ((k : ℝ) + 1)) :=
      measure_mono Set.inter_subset_right
    _ = 1 := by simp

theorem exists_unitCell_point_integral_le
    {U : Set ℝ} {f : ℝ → ℝ} (hU : MeasurableSet U)
    (hf : IntegrableOn f U) (hnonneg : ∀ t ∈ U, 0 ≤ f t)
    (k : ℤ) (hvol : volume (unitCell U k) ≠ 0) :
    ∃ t ∈ unitCell U k, (∫ x in unitCell U k, f x) ≤ f t := by
  have hvoltop : volume (unitCell U k) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (volume_unitCell_le_one U k)
  have hfcell : IntegrableOn f (unitCell U k) :=
    hf.mono_set Set.inter_subset_left
  obtain ⟨t, ht, havg⟩ := exists_setAverage_le hvol hvoltop hfcell
  refine ⟨t, ht, ?_⟩
  have hintnonneg : 0 ≤ ∫ x in unitCell U k, f x := by
    exact setIntegral_nonneg (measurableSet_unitCell hU k)
      (fun x hx ↦ hnonneg x hx.1)
  have hrealpos : 0 < (volume (unitCell U k)).toReal :=
    ENNReal.toReal_pos hvol hvoltop
  have hreal_le : (volume (unitCell U k)).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top
      (volume_unitCell_le_one U k)
  have hinv : 1 ≤ ((volume (unitCell U k)).toReal)⁻¹ := by
    exact (one_le_inv₀ hrealpos).mpr hreal_le
  calc
    (∫ x in unitCell U k, f x) ≤
        ((volume (unitCell U k)).toReal)⁻¹ *
          (∫ x in unitCell U k, f x) :=
      (le_mul_of_one_le_left hintnonneg hinv)
    _ = ⨍ x in unitCell U k, f x := by
      rw [setAverage_eq]
      rfl
    _ ≤ f t := havg

def boundedUnitCellIndices (T : ℝ) : Finset ℤ :=
  Finset.Icc 0 ⌊T⌋

theorem iUnion_unitCell_bounded_eq
    {U : Set ℝ} {T : ℝ} (hU : U ⊆ Set.Icc 0 T) :
    (⋃ k ∈ boundedUnitCellIndices T, unitCell U k) = U := by
  ext t
  constructor
  · intro ht
    simp only [Set.mem_iUnion] at ht
    rcases ht with ⟨k, _hk, htcell⟩
    exact htcell.1
  · intro ht
    have htIcc := hU ht
    let k : ℤ := ⌊t⌋
    have hk : k ∈ boundedUnitCellIndices T := by
      rw [boundedUnitCellIndices, Finset.mem_Icc]
      exact ⟨Int.floor_nonneg.mpr htIcc.1, Int.floor_le_floor htIcc.2⟩
    simp only [Set.mem_iUnion]
    refine ⟨k, hk, ht, ?_, ?_⟩
    · exact Int.floor_le t
    · exact Int.lt_floor_add_one t

theorem unitCell_disjoint {U : Set ℝ} {k l : ℤ} (hkl : k ≠ l) :
    Disjoint (unitCell U k) (unitCell U l) := by
  rw [Set.disjoint_left]
  intro t htk htl
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hsucc : (k : ℝ) + 1 ≤ (l : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hlt)
    linarith [htk.2.2, htl.2.1]
  · have hsucc : (l : ℝ) + 1 ≤ (k : ℝ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hgt)
    linarith [htl.2.2, htk.2.1]

theorem integral_bounded_eq_sum_unitCells
    {U : Set ℝ} {T : ℝ} {f : ℝ → ℝ}
    (hUmeas : MeasurableSet U) (hU : U ⊆ Set.Icc 0 T)
    (hf : IntegrableOn f U) :
    ∫ t in U, f t =
      ∑ k ∈ boundedUnitCellIndices T, ∫ t in unitCell U k, f t := by
  calc
    ∫ t in U, f t =
        ∫ t in (⋃ k ∈ boundedUnitCellIndices T, unitCell U k), f t := by
      rw [iUnion_unitCell_bounded_eq hU]
    _ = ∑ k ∈ boundedUnitCellIndices T, ∫ t in unitCell U k, f t := by
      exact integral_biUnion_finset (boundedUnitCellIndices T)
        (fun k _ ↦ measurableSet_unitCell hUmeas k)
        (by
          intro k hk l hl hkl
          exact unitCell_disjoint hkl)
        (fun k _ ↦ hf.mono_set Set.inter_subset_left)

theorem unitCell_sample_injectiveOn
    {U : Set ℝ} {K : Finset ℤ} {p : ℤ → ℝ}
    (hp : ∀ k ∈ K, p k ∈ unitCell U k) :
    Set.InjOn p (K : Set ℤ) := by
  intro k hk l hl hkl
  have hkfloor : ⌊p k⌋ = k :=
    Int.floor_eq_on_Ico k (p k) (hp k hk).2
  have hlfloor : ⌊p l⌋ = l :=
    Int.floor_eq_on_Ico l (p l) (hp l hl).2
  rw [← hkfloor, ← hlfloor, hkl]

theorem isOneSpaced_image_unitCell_samples_of_same_mod_two
    {U : Set ℝ} {K : Finset ℤ} {p : ℤ → ℝ} {r : ℤ}
    (hp : ∀ k ∈ K, p k ∈ unitCell U k)
    (hmod : ∀ k ∈ K, k % 2 = r) :
    IsOneSpaced ((K.image p : Finset ℝ) : Set ℝ) := by
  intro x hx y hy hxy
  rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨l, hl, rfl⟩
  have hkl : k ≠ l := by
    intro heq
    apply hxy
    rw [heq]
  rcases lt_or_gt_of_ne hkl with hlt | hgt
  · have hgap : k + 2 ≤ l := by
      have hmk := hmod k hk
      have hml := hmod l hl
      omega
    have hgapReal : (k : ℝ) + 2 ≤ (l : ℝ) := by
      exact_mod_cast hgap
    have hpk := (hp k hk).2
    have hpl := (hp l hl).2
    rw [abs_of_nonpos (by linarith [hpk.2, hpl.1] : p k - p l ≤ 0)]
    linarith [hpk.2, hpl.1]
  · have hgap : l + 2 ≤ k := by
      have hmk := hmod k hk
      have hml := hmod l hl
      omega
    have hgapReal : (l : ℝ) + 2 ≤ (k : ℝ) := by
      exact_mod_cast hgap
    have hpk := (hp k hk).2
    have hpl := (hp l hl).2
    rw [abs_of_nonneg (by linarith [hpk.1, hpl.2] : 0 ≤ p k - p l)]
    linarith [hpk.1, hpl.2]

/-- Unit-cell/parity discretization.  A uniform weighted estimate on every
finite one-spaced subset controls the whole nonnegative integral, with the
absolute factor two coming from the even and odd unit cells. -/
theorem integral_le_two_mul_of_uniform_oneSpaced_sum_bound
    {U : Set ℝ} {T E : ℝ} {f : ℝ → ℝ}
    (hUmeas : MeasurableSet U) (hU : U ⊆ Set.Icc 0 T)
    (hf : IntegrableOn f U) (hnonneg : ∀ t ∈ U, 0 ≤ f t)
    (hsum : ∀ R : Finset ℝ,
      (R : Set ℝ) ⊆ U → IsOneSpaced (R : Set ℝ) →
        (∑ t ∈ R, f t) ≤ E) :
    (∫ t in U, f t) ≤ 2 * E := by
  classical
  let K : Finset ℤ := boundedUnitCellIndices T
  let Kactive : Finset ℤ :=
    K.filter fun k ↦ volume (unitCell U k) ≠ 0
  have hexists : ∀ k : ℤ, ∃ t : ℝ,
      volume (unitCell U k) ≠ 0 →
        t ∈ unitCell U k ∧ (∫ x in unitCell U k, f x) ≤ f t := by
    intro k
    by_cases hk : volume (unitCell U k) ≠ 0
    · obtain ⟨t, ht, htbound⟩ :=
        exists_unitCell_point_integral_le hUmeas hf hnonneg k hk
      exact ⟨t, fun _ ↦ ⟨ht, htbound⟩⟩
    · exact ⟨0, fun hk' ↦ (hk hk').elim⟩
  choose p hp using hexists
  let Kzero : Finset ℤ := Kactive.filter fun k ↦ k % 2 = 0
  let Kone : Finset ℤ := Kactive.filter fun k ↦ k % 2 = 1
  have hKunion : Kzero ∪ Kone = Kactive := by
    ext k
    simp only [Kzero, Kone, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hk, -⟩ | ⟨hk, -⟩) <;> exact hk
    · intro hk
      rcases Int.emod_two_eq_zero_or_one k with hkmod | hkmod
      · exact Or.inl ⟨hk, hkmod⟩
      · exact Or.inr ⟨hk, hkmod⟩
  have hKdisjoint : Disjoint Kzero Kone := by
    rw [Finset.disjoint_left]
    intro k hkzero hkone
    have hz := (Finset.mem_filter.mp hkzero).2
    have ho := (Finset.mem_filter.mp hkone).2
    omega
  have hpactive : ∀ k ∈ Kactive, p k ∈ unitCell U k := by
    intro k hk
    have hkvol : volume (unitCell U k) ≠ 0 :=
      (Finset.mem_filter.mp hk).2
    exact (hp k hkvol).1
  have hpbound : ∀ k ∈ Kactive,
      (∫ x in unitCell U k, f x) ≤ f (p k) := by
    intro k hk
    have hkvol : volume (unitCell U k) ≠ 0 :=
      (Finset.mem_filter.mp hk).2
    exact (hp k hkvol).2
  have hparityBound : ∀ (Kr : Finset ℤ) (r : ℤ),
      Kr ⊆ Kactive → (∀ k ∈ Kr, k % 2 = r) →
        (∑ k ∈ Kr, ∫ x in unitCell U k, f x) ≤ E := by
    intro Kr r hKr hmod
    have hpKr : ∀ k ∈ Kr, p k ∈ unitCell U k := by
      intro k hk
      exact hpactive k (hKr hk)
    have hpointSum : (∑ k ∈ Kr, f (p k)) ≤ E := by
      have himageSub : ((Kr.image p : Finset ℝ) : Set ℝ) ⊆ U := by
        intro t ht
        rcases Finset.mem_image.mp ht with ⟨k, hk, rfl⟩
        exact (hpKr k hk).1
      have himageSpace : IsOneSpaced ((Kr.image p : Finset ℝ) : Set ℝ) :=
        isOneSpaced_image_unitCell_samples_of_same_mod_two hpKr hmod
      have himageBound := hsum (Kr.image p) himageSub himageSpace
      rw [Finset.sum_image (unitCell_sample_injectiveOn hpKr)] at himageBound
      exact himageBound
    exact (Finset.sum_le_sum fun k hk ↦ hpbound k (hKr hk)).trans hpointSum
  have hzero :
      (∑ k ∈ Kzero, ∫ x in unitCell U k, f x) ≤ E := by
    apply hparityBound Kzero 0
    · intro k hk
      exact (Finset.mem_filter.mp hk).1
    · intro k hk
      exact (Finset.mem_filter.mp hk).2
  have hone :
      (∑ k ∈ Kone, ∫ x in unitCell U k, f x) ≤ E := by
    apply hparityBound Kone 1
    · intro k hk
      exact (Finset.mem_filter.mp hk).1
    · intro k hk
      exact (Finset.mem_filter.mp hk).2
  have hsumActive :
      (∑ k ∈ K, ∫ x in unitCell U k, f x) =
        ∑ k ∈ Kactive, ∫ x in unitCell U k, f x := by
    simp only [Kactive, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkvol : volume (unitCell U k) ≠ 0
    · simp [hkvol]
    · simp [hkvol, MeasureTheory.setIntegral_measure_zero f
        (not_ne_iff.mp hkvol)]
  rw [integral_bounded_eq_sum_unitCells hUmeas hU hf]
  rw [hsumActive]
  calc
    (∑ k ∈ Kactive, ∫ x in unitCell U k, f x) =
        (∑ k ∈ Kzero, ∫ x in unitCell U k, f x) +
          ∑ k ∈ Kone, ∫ x in unitCell U k, f x := by
      rw [← Finset.sum_union hKdisjoint, hKunion]
    _ ≤ E + E := add_le_add hzero hone
    _ = 2 * E := by ring

/-! ## Discharging the analytic side conditions for the Type-II weight -/

theorem continuous_dyadicDirichletPolynomial_onePlusIT
    {a : ℕ → ℂ} {N : ℝ} (hN : 0 ≤ N) :
    Continuous (fun t : ℝ ↦
      dyadicDirichletPolynomial a N (onePlusIT t)) :=
  (lipschitzWith_dyadicDirichletPolynomial_onePlusIT (a := a) hN).continuous

/-- The precise nonnegative weight in Proposition 5.1 is integrable on
every measurable subset of a bounded height interval. -/
theorem integrableOn_typeII_weight
    {U : Set ℝ} {T N₁ N₂ : ℝ} {a₁ a₂ : ℕ → ℂ}
    (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂) (hU : U ⊆ Set.Icc 0 T) :
    IntegrableOn
      (fun t : ℝ ↦
        ‖dyadicDirichletPolynomial a₁ N₁ (onePlusIT t)‖ ^ 2 *
        ‖dyadicDirichletPolynomial a₂ N₂ (onePlusIT t)‖ ^ 2) U := by
  have hc₁ : Continuous (fun t : ℝ ↦
      ‖dyadicDirichletPolynomial a₁ N₁ (onePlusIT t)‖ ^ 2) :=
    (continuous_dyadicDirichletPolynomial_onePlusIT hN₁).norm.pow 2
  have hc₂ : Continuous (fun t : ℝ ↦
      ‖dyadicDirichletPolynomial a₂ N₂ (onePlusIT t)‖ ^ 2) :=
    (continuous_dyadicDirichletPolynomial_onePlusIT hN₂).norm.pow 2
  exact (hc₁.mul hc₂).integrableOn_Icc.mono_set hU

theorem typeII_weight_nonneg
    (a₁ a₂ : ℕ → ℂ) (N₁ N₂ t : ℝ) :
    0 ≤
      ‖dyadicDirichletPolynomial a₁ N₁ (onePlusIT t)‖ ^ 2 *
      ‖dyadicDirichletPolynomial a₂ N₂ (onePlusIT t)‖ ^ 2 := by
  positivity

/-- Metadata for the unit-cell/parity discrete-to-integral bridge. -/
def integralDiscretizationModule : ProofModule :=
  { name := "Hybrid.IntegralDiscretization"
    paperLocation :=
      "Proof of Proposition 5.1, passage from one-spaced sums to the integral"
    purpose :=
      "Partition a bounded measurable set into unit cells, select cell representatives, split them by parity into two one-spaced sets, and deduce the integral bound with an explicit factor two."
    dependsOn := ["Hybrid.DiscreteToMeasure"]
    status := .proved }

end

end ExactSemiprimes.Hybrid
