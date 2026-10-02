import ExactSemiprimes.Completion.ChebyshevPassage

/-! # Converting a measure bound into a count of exceptional integers -/

namespace ExactSemiprimes
namespace Completion

/-- The half-length interval based at a point of the unit cell of `m` is
contained in the full-length interval based at `m`.  This is the elementary
geometric fact behind the `h / 2` argument in the paper. -/
theorem halfInterval_subset_fullInterval {m : ℕ} {y h : ℝ}
    (hy : y ∈ Set.Ico (m : ℝ) ((m : ℝ) + 1)) (hh : 2 < h) :
    Set.Ioc y (y + h / 2) ⊆ Set.Ioc (m : ℝ) ((m : ℝ) + h) := by
  intro z hz
  constructor <;> linarith [hy.1, hy.2, hz.1, hz.2]

/-- Distinct natural numbers determine disjoint half-open unit intervals. -/
theorem pairwiseDisjoint_natUnitIntervals (s : Finset ℕ) :
    Set.Pairwise (↑s : Set ℕ)
      (fun m n ↦ Disjoint
        (Set.Ico (m : ℝ) ((m : ℝ) + 1))
        (Set.Ico (n : ℝ) ((n : ℝ) + 1))) := by
  intro m _hm n _hn hmn
  rw [Set.disjoint_left]
  intro y hym hyn
  rcases Nat.lt_or_gt_of_ne hmn with hlt | hgt
  · have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hlt
    linarith [hym.2, hyn.1]
  · have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hgt
    linarith [hyn.2, hym.1]

/-- If every half-open unit interval attached to a member of a finite set of
natural numbers lies in `bad`, then the cardinality of that finite set is at
most the Lebesgue measure of `bad`.

No measurability hypothesis on `bad` is needed: monotonicity of the outer
measure induced by Lebesgue measure suffices. -/
theorem card_le_volume_of_unitIntervals_subset (s : Finset ℕ) (bad : Set ℝ)
    (hsub : ∀ m ∈ s,
      Set.Ico (m : ℝ) ((m : ℝ) + 1) ⊆ bad) :
    (s.card : ENNReal) ≤ MeasureTheory.volume bad := by
  let cells : Set ℝ := ⋃ m ∈ s, Set.Ico (m : ℝ) ((m : ℝ) + 1)
  have hcells : cells ⊆ bad := by
    intro y hy
    simp only [cells, Set.mem_iUnion] at hy
    obtain ⟨m, hm⟩ := hy
    obtain ⟨hms, hym⟩ := hm
    exact hsub m hms hym
  have hmeasure : MeasureTheory.volume cells = (s.card : ENNReal) := by
    rw [show cells = ⋃ m ∈ s, Set.Ico (m : ℝ) ((m : ℝ) + 1) by rfl]
    rw [MeasureTheory.measure_biUnion_finset
      (pairwiseDisjoint_natUnitIntervals s)
      (fun _m _hm ↦ measurableSet_Ico)]
    simp [Real.volume_Ico]
  rw [← hmeasure]
  exact MeasureTheory.measure_mono hcells

/-- Counting form of the unit-interval transfer.  `integerBad m` need only
imply `realBad y` throughout the unit cell `[m,m+1)`; a measure bound for the
real exceptional set then bounds the number of exceptional integers in any
finite ambient set. -/
theorem card_filter_le_volume_of_unitInterval_transfer
    (s : Finset ℕ) (integerBad : ℕ → Prop) (realBad : ℝ → Prop)
    [DecidablePred integerBad]
    (htransfer : ∀ m ∈ s, integerBad m →
      Set.Ico (m : ℝ) ((m : ℝ) + 1) ⊆ {y | realBad y}) :
    (((s.filter integerBad).card : ℕ) : ENNReal) ≤
      MeasureTheory.volume {y | realBad y} := by
  apply card_le_volume_of_unitIntervals_subset (s.filter integerBad)
    {y | realBad y}
  intro m hm
  rw [Finset.mem_filter] at hm
  exact htransfer m hm.1 hm.2

def realToIntegerExceptionsModule : ProofModule :=
  { name := "Completion.RealToIntegerExceptions"
    paperLocation := "Section 7.2, h/2 unit-interval argument"
    purpose := "Prove the h/2 interval inclusion and the disjoint-unit-cell measure-to-cardinality transfer."
    dependsOn := ["Completion.ChebyshevPassage"]
    status := .proved }

end Completion
end ExactSemiprimes
