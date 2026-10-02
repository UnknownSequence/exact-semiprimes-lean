import ExactSemiprimes.TypeII.WeightedExtremeRange
import ExactSemiprimes.TypeII.ExtremeSmallAssembly
import ExactSemiprimes.TypeII.MediumLogBinBridge
import ExactSemiprimes.TypeII.OuterParameterReserve
import ExactSemiprimes.TypeII.OuterLengthGeometry
import ExactSemiprimes.Hybrid.IntegralDiscretization

/-! # Type II with threshold 17/70 (paper Proposition 5.1) -/

namespace ExactSemiprimes
namespace TypeII

open MeasureTheory
open scoped BigOperators

noncomputable section

/-!
## Deterministic assembly of the three Type-II regimes

The analytic inputs for Proposition 5.1 act separately on `R₁`, `R₂`, and
`R₃`.  This section records the bookkeeping needed to put those estimates
back together.  In particular, neither the finite-sum nor the integral
identity below loses a constant.
-/

/-- The points of a finite set assigned to the extreme-large regime `R₁`. -/
def finiteLargeValueR1 (R : Finset ℝ) (M₁ M₂ : ℂ → ℂ)
    (N₁ N₂ ε : ℝ) : Finset ℝ :=
  by
    classical
    exact R.filter fun t ↦
      t ∈ largeValueR1 (R : Set ℝ) M₁ M₂ N₁ N₂ ε

/-- The points of a finite set assigned to the tiny-value regime `R₃`. -/
def finiteLargeValueR3 (R : Finset ℝ) (M₁ M₂ : ℂ → ℂ)
    (N₁ N₂ T ε : ℝ) : Finset ℝ :=
  by
    classical
    exact R.filter fun t ↦
      t ∈ largeValueR3 (R : Set ℝ) M₁ M₂ N₁ N₂ T ε

@[simp]
theorem mem_finiteLargeValueR1_iff {R : Finset ℝ} {M₁ M₂ : ℂ → ℂ}
    {N₁ N₂ ε t : ℝ} :
    t ∈ finiteLargeValueR1 R M₁ M₂ N₁ N₂ ε ↔
      t ∈ R ∧
        t ∈ largeValueR1 (R : Set ℝ) M₁ M₂ N₁ N₂ ε := by
  simp [finiteLargeValueR1]

/-- For the two actual dyadic Dirichlet polynomials, the deterministic
`R₁` piece used by the final Type-II partition is literally the
`extremePairPoints` set controlled by `ExtremeLargeAbsorption`. -/
theorem finiteLargeValueR1_dyadic_eq_extremePairPoints
    (R : Finset ℝ) (a₁ a₂ : ℕ → ℂ) (M₁ M₂ eps : ℝ) :
    finiteLargeValueR1 R
        (dyadicDirichletPolynomial a₁ M₁)
        (dyadicDirichletPolynomial a₂ M₂) M₁ M₂ eps =
      extremePairPoints R a₁ a₂ M₁ M₂ eps := by
  ext t
  simp [finiteLargeValueR1, largeValueR1, extremeLargeValueSet,
    typeIIMagnitude, extremePairPoints]

@[simp]
theorem mem_finiteLargeValueR2_iff {R : Finset ℝ} {M₁ M₂ : ℂ → ℂ}
    {N₁ N₂ T ε t : ℝ} :
    t ∈ finiteLargeValueR2 R M₁ M₂ N₁ N₂ T ε ↔
      t ∈ R ∧
        t ∈ largeValueR2 (R : Set ℝ) M₁ M₂ N₁ N₂ T ε := by
  simp [finiteLargeValueR2]

@[simp]
theorem mem_finiteLargeValueR3_iff {R : Finset ℝ} {M₁ M₂ : ℂ → ℂ}
    {N₁ N₂ T ε t : ℝ} :
    t ∈ finiteLargeValueR3 R M₁ M₂ N₁ N₂ T ε ↔
      t ∈ R ∧
        t ∈ largeValueR3 (R : Set ℝ) M₁ M₂ N₁ N₂ T ε := by
  simp [finiteLargeValueR3]

/-- The finite versions of `R₁`, `R₂`, and `R₃` are an exact
partition of the original finite set. -/
theorem finiteLargeValue_partition (R : Finset ℝ) (M₁ M₂ : ℂ → ℂ)
    (N₁ N₂ T ε : ℝ) :
    finiteLargeValueR1 R M₁ M₂ N₁ N₂ ε ∪
        finiteLargeValueR2 R M₁ M₂ N₁ N₂ T ε ∪
        finiteLargeValueR3 R M₁ M₂ N₁ N₂ T ε = R := by
  classical
  ext t
  simp only [Finset.mem_union, mem_finiteLargeValueR1_iff,
    mem_finiteLargeValueR2_iff, mem_finiteLargeValueR3_iff]
  have hpartition := Set.ext_iff.mp
    (largeValue_partition (R : Set ℝ) M₁ M₂ N₁ N₂ T ε) t
  simp only [Set.mem_union] at hpartition
  tauto

theorem finiteLargeValueR1_disjoint_R2 (R : Finset ℝ)
    (M₁ M₂ : ℂ → ℂ) (N₁ N₂ T ε : ℝ) :
    Disjoint (finiteLargeValueR1 R M₁ M₂ N₁ N₂ ε)
      (finiteLargeValueR2 R M₁ M₂ N₁ N₂ T ε) := by
  classical
  rw [Finset.disjoint_left]
  intro t ht₁ ht₂
  exact Set.disjoint_left.mp
    (largeValueR1_disjoint_R2 (R : Set ℝ) M₁ M₂ N₁ N₂ T ε)
    (mem_finiteLargeValueR1_iff.mp ht₁).2
    (mem_finiteLargeValueR2_iff.mp ht₂).2

theorem finiteLargeValueR1_disjoint_R3 (R : Finset ℝ)
    (M₁ M₂ : ℂ → ℂ) (N₁ N₂ T ε : ℝ) :
    Disjoint (finiteLargeValueR1 R M₁ M₂ N₁ N₂ ε)
      (finiteLargeValueR3 R M₁ M₂ N₁ N₂ T ε) := by
  classical
  rw [Finset.disjoint_left]
  intro t ht₁ ht₃
  exact Set.disjoint_left.mp
    (largeValueR1_disjoint_R3 (R : Set ℝ) M₁ M₂ N₁ N₂ T ε)
    (mem_finiteLargeValueR1_iff.mp ht₁).2
    (mem_finiteLargeValueR3_iff.mp ht₃).2

theorem finiteLargeValueR2_disjoint_R3 (R : Finset ℝ)
    (M₁ M₂ : ℂ → ℂ) (N₁ N₂ T ε : ℝ) :
    Disjoint (finiteLargeValueR2 R M₁ M₂ N₁ N₂ T ε)
      (finiteLargeValueR3 R M₁ M₂ N₁ N₂ T ε) := by
  classical
  rw [Finset.disjoint_left]
  intro t ht₂ ht₃
  exact Set.disjoint_left.mp
    (largeValueR2_disjoint_R3 (R : Set ℝ) M₁ M₂ N₁ N₂ T ε)
    (mem_finiteLargeValueR2_iff.mp ht₂).2
    (mem_finiteLargeValueR3_iff.mp ht₃).2

/-- Exact finite-sum decomposition into the three deterministic regimes. -/
theorem sum_finiteLargeValue_partition (R : Finset ℝ)
    (M₁ M₂ : ℂ → ℂ) (N₁ N₂ T ε : ℝ) (f : ℝ → ℝ) :
    ∑ t ∈ R, f t =
      ∑ t ∈ finiteLargeValueR1 R M₁ M₂ N₁ N₂ ε, f t +
      ∑ t ∈ finiteLargeValueR2 R M₁ M₂ N₁ N₂ T ε, f t +
      ∑ t ∈ finiteLargeValueR3 R M₁ M₂ N₁ N₂ T ε, f t := by
  classical
  let R₁ := finiteLargeValueR1 R M₁ M₂ N₁ N₂ ε
  let R₂ := finiteLargeValueR2 R M₁ M₂ N₁ N₂ T ε
  let R₃ := finiteLargeValueR3 R M₁ M₂ N₁ N₂ T ε
  have hpartition : R₁ ∪ R₂ ∪ R₃ = R :=
    finiteLargeValue_partition R M₁ M₂ N₁ N₂ T ε
  have h₁₂ : Disjoint R₁ R₂ :=
    finiteLargeValueR1_disjoint_R2 R M₁ M₂ N₁ N₂ T ε
  have h₁₃ : Disjoint R₁ R₃ :=
    finiteLargeValueR1_disjoint_R3 R M₁ M₂ N₁ N₂ T ε
  have h₂₃ : Disjoint R₂ R₃ :=
    finiteLargeValueR2_disjoint_R3 R M₁ M₂ N₁ N₂ T ε
  have h₁₂₃ : Disjoint (R₁ ∪ R₂) R₃ := by
    rw [Finset.disjoint_left]
    intro t ht ht₃
    rcases Finset.mem_union.mp ht with ht₁ | ht₂
    · exact Finset.disjoint_left.mp h₁₃ ht₁ ht₃
    · exact Finset.disjoint_left.mp h₂₃ ht₂ ht₃
  calc
    ∑ t ∈ R, f t = ∑ t ∈ R₁ ∪ R₂ ∪ R₃, f t := by rw [hpartition]
    _ = (∑ t ∈ R₁ ∪ R₂, f t) + ∑ t ∈ R₃, f t := by
      rw [Finset.sum_union h₁₂₃]
    _ = (∑ t ∈ R₁, f t) + (∑ t ∈ R₂, f t) +
        ∑ t ∈ R₃, f t := by
      rw [Finset.sum_union h₁₂]

/-- Three separate finite-sum estimates combine without any hidden loss. -/
theorem sum_finiteLargeValue_partition_le (R : Finset ℝ)
    (M₁ M₂ : ℂ → ℂ) (N₁ N₂ T ε : ℝ) (f : ℝ → ℝ)
    {E₁ E₂ E₃ : ℝ}
    (h₁ : (∑ t ∈ finiteLargeValueR1 R M₁ M₂ N₁ N₂ ε, f t) ≤ E₁)
    (h₂ : (∑ t ∈ finiteLargeValueR2 R M₁ M₂ N₁ N₂ T ε, f t) ≤ E₂)
    (h₃ : (∑ t ∈ finiteLargeValueR3 R M₁ M₂ N₁ N₂ T ε, f t) ≤ E₃) :
    ∑ t ∈ R, f t ≤ E₁ + E₂ + E₃ := by
  rw [sum_finiteLargeValue_partition R M₁ M₂ N₁ N₂ T ε f]
  linarith

/-- Variant adapted to the analytic endpoints used below: the weighted
extreme theorem controls `R₁` and `R₃` together, while the hybrid theorem
controls `R₂`. -/
theorem sum_finiteLargeValue_partition_le_of_extremes_combined
    (R : Finset ℝ) (M₁ M₂ : ℂ → ℂ) (N₁ N₂ T ε : ℝ)
    (f : ℝ → ℝ) {E₁₃ E₂ : ℝ}
    (h₁₃ :
      (∑ t ∈ finiteLargeValueR1 R M₁ M₂ N₁ N₂ ε, f t) +
        (∑ t ∈ finiteLargeValueR3 R M₁ M₂ N₁ N₂ T ε, f t) ≤ E₁₃)
    (h₂ :
      (∑ t ∈ finiteLargeValueR2 R M₁ M₂ N₁ N₂ T ε, f t) ≤ E₂) :
    ∑ t ∈ R, f t ≤ E₁₃ + E₂ := by
  rw [sum_finiteLargeValue_partition R M₁ M₂ N₁ N₂ T ε f]
  linarith

/-- Exact set-integral decomposition into the three deterministic regimes. -/
theorem integral_largeValue_partition {R : Set ℝ} {M₁ M₂ : ℂ → ℂ}
    {N₁ N₂ T ε : ℝ} {f : ℝ → ℝ}
    (hR : MeasurableSet R)
    (hM₁ : Measurable (typeIIMagnitude M₁))
    (hM₂ : Measurable (typeIIMagnitude M₂))
    (hf : IntegrableOn f R) :
    ∫ t in R, f t =
      (∫ t in largeValueR1 R M₁ M₂ N₁ N₂ ε, f t) +
      (∫ t in largeValueR2 R M₁ M₂ N₁ N₂ T ε, f t) +
      (∫ t in largeValueR3 R M₁ M₂ N₁ N₂ T ε, f t) := by
  let R₁ := largeValueR1 R M₁ M₂ N₁ N₂ ε
  let R₂ := largeValueR2 R M₁ M₂ N₁ N₂ T ε
  let R₃ := largeValueR3 R M₁ M₂ N₁ N₂ T ε
  have hpartition : R₁ ∪ R₂ ∪ R₃ = R :=
    largeValue_partition R M₁ M₂ N₁ N₂ T ε
  have h₁₂ : Disjoint R₁ R₂ :=
    largeValueR1_disjoint_R2 R M₁ M₂ N₁ N₂ T ε
  have h₁₃ : Disjoint R₁ R₃ :=
    largeValueR1_disjoint_R3 R M₁ M₂ N₁ N₂ T ε
  have h₂₃ : Disjoint R₂ R₃ :=
    largeValueR2_disjoint_R3 R M₁ M₂ N₁ N₂ T ε
  have h₁₂₃ : Disjoint (R₁ ∪ R₂) R₃ := by
    rw [Set.disjoint_left]
    intro t ht ht₃
    rcases ht with ht₁ | ht₂
    · exact Set.disjoint_left.mp h₁₃ ht₁ ht₃
    · exact Set.disjoint_left.mp h₂₃ ht₂ ht₃
  have hm₂ : MeasurableSet R₂ := measurableSet_largeValueR2 hR hM₁ hM₂
  have hm₃ : MeasurableSet R₃ := measurableSet_largeValueR3 hR hM₁ hM₂
  have hi₁ : IntegrableOn f R₁ := hf.mono_set Set.inter_subset_left
  have hi₂ : IntegrableOn f R₂ := hf.mono_set Set.sdiff_subset
  have hi₃ : IntegrableOn f R₃ := hf.mono_set (by
    intro t ht
    exact ht.1.1)
  calc
    ∫ t in R, f t = ∫ t in R₁ ∪ R₂ ∪ R₃, f t := by rw [hpartition]
    _ = (∫ t in R₁ ∪ R₂, f t) + ∫ t in R₃, f t := by
      rw [setIntegral_union h₁₂₃ hm₃ (hi₁.union hi₂) hi₃]
    _ = (∫ t in R₁, f t) + (∫ t in R₂, f t) +
        ∫ t in R₃, f t := by
      rw [setIntegral_union h₁₂ hm₂ hi₁ hi₂]
    _ = (∫ t in largeValueR1 R M₁ M₂ N₁ N₂ ε, f t) +
        (∫ t in largeValueR2 R M₁ M₂ N₁ N₂ T ε, f t) +
        (∫ t in largeValueR3 R M₁ M₂ N₁ N₂ T ε, f t) := by
      simp only [R₁, R₂, R₃, add_assoc]

/-- Three separate integral estimates combine without any hidden loss. -/
theorem integral_largeValue_partition_le {R : Set ℝ} {M₁ M₂ : ℂ → ℂ}
    {N₁ N₂ T ε : ℝ} {f : ℝ → ℝ} {E₁ E₂ E₃ : ℝ}
    (hR : MeasurableSet R)
    (hM₁ : Measurable (typeIIMagnitude M₁))
    (hM₂ : Measurable (typeIIMagnitude M₂))
    (hf : IntegrableOn f R)
    (h₁ : (∫ t in largeValueR1 R M₁ M₂ N₁ N₂ ε, f t) ≤ E₁)
    (h₂ : (∫ t in largeValueR2 R M₁ M₂ N₁ N₂ T ε, f t) ≤ E₂)
    (h₃ : (∫ t in largeValueR3 R M₁ M₂ N₁ N₂ T ε, f t) ≤ E₃) :
    ∫ t in R, f t ≤ E₁ + E₂ + E₃ := by
  rw [integral_largeValue_partition (N₁ := N₁) (N₂ := N₂)
    (T := T) (ε := ε) hR hM₁ hM₂ hf]
  simpa only [add_assoc] using add_le_add (add_le_add h₁ h₂) h₃

/-!
## Exact summation over the medium logarithmic bins

The following fibers are the literal finite bins used in the proof.  The
first identity is purely combinatorial; the integral version additionally
records every measurability and integrability hypothesis needed to invoke
finite additivity.
-/

/-- The medium points whose canonical logarithmic magnitude pair equals
`k`. -/
def finiteMediumLogMagnitudeBin (R : Finset ℝ) (M₁ M₂ : ℂ → ℂ)
    (N₁ N₂ T ε : ℝ) (k : ℤ × ℤ) : Finset ℝ :=
  (finiteLargeValueR2 R M₁ M₂ N₁ N₂ T ε).filter fun t ↦
    canonicalLogMagnitudePair M₁ M₂ t = k

/-- A finite medium sum is exactly the sum of its occupied logarithmic-bin
fibers. -/
theorem sum_finiteLargeValueR2_eq_sum_occupied_bins
    (R : Finset ℝ) (M₁ M₂ : ℂ → ℂ) (N₁ N₂ T ε : ℝ)
    (f : ℝ → ℝ) :
    ∑ t ∈ finiteLargeValueR2 R M₁ M₂ N₁ N₂ T ε, f t =
      ∑ k ∈ occupiedMediumLogMagnitudePairs R M₁ M₂ N₁ N₂ T ε,
        ∑ t ∈ finiteMediumLogMagnitudeBin R M₁ M₂ N₁ N₂ T ε k, f t := by
  classical
  symm
  simpa only [finiteMediumLogMagnitudeBin] using
    (Finset.sum_fiberwise_of_maps_to
      (s := finiteLargeValueR2 R M₁ M₂ N₁ N₂ T ε)
      (t := occupiedMediumLogMagnitudePairs R M₁ M₂ N₁ N₂ T ε)
      (g := canonicalLogMagnitudePair M₁ M₂)
      (fun t ht ↦ Finset.mem_image.mpr ⟨t, ht, rfl⟩) f)

/-- A uniform bound for each occupied medium bin costs exactly the number
of occupied bins. -/
theorem sum_finiteLargeValueR2_le_card_mul
    (R : Finset ℝ) (M₁ M₂ : ℂ → ℂ) (N₁ N₂ T ε V : ℝ)
    (f : ℝ → ℝ)
    (hbin : ∀ k ∈ occupiedMediumLogMagnitudePairs R M₁ M₂ N₁ N₂ T ε,
      (∑ t ∈ finiteMediumLogMagnitudeBin R M₁ M₂ N₁ N₂ T ε k, f t) ≤ V) :
    ∑ t ∈ finiteLargeValueR2 R M₁ M₂ N₁ N₂ T ε, f t ≤
      ((occupiedMediumLogMagnitudePairs R M₁ M₂ N₁ N₂ T ε).card : ℝ) * V := by
  rw [sum_finiteLargeValueR2_eq_sum_occupied_bins]
  simpa using Finset.sum_le_card_nsmul
    (occupiedMediumLogMagnitudePairs R M₁ M₂ N₁ N₂ T ε)
    (fun k ↦ ∑ t ∈ finiteMediumLogMagnitudeBin R M₁ M₂ N₁ N₂ T ε k, f t)
    V hbin

/-- The exact `O((log T)²)` finite-bin loss, with the floor and natural
rounding made explicit. -/
theorem sum_finiteLargeValueR2_le_logBinCount_mul
    (R : Finset ℝ) (M₁ M₂ : ℂ → ℂ) (N₁ N₂ T ε V : ℝ)
    (f : ℝ → ℝ) (hT : 0 < T) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂)
    (hε : 0 ≤ ε) (hV : 0 ≤ V)
    (hbin : ∀ k ∈ occupiedMediumLogMagnitudePairs R M₁ M₂ N₁ N₂ T ε,
      (∑ t ∈ finiteMediumLogMagnitudeBin R M₁ M₂ N₁ N₂ T ε k, f t) ≤ V) :
    ∑ t ∈ finiteLargeValueR2 R M₁ M₂ N₁ N₂ T ε, f t ≤
      ((((⌊Real.log T⌋ + 1).toNat) ^ 2 : ℕ) : ℝ) * V := by
  refine (sum_finiteLargeValueR2_le_card_mul R M₁ M₂ N₁ N₂ T ε V f hbin).trans ?_
  have hcardNat := card_occupiedMediumLogMagnitudePairs_le
    R M₁ M₂ N₁ N₂ T ε hT hN₁ hN₂ hε
  have hcardReal :
      ((occupiedMediumLogMagnitudePairs R M₁ M₂ N₁ N₂ T ε).card : ℝ) ≤
        ((((⌊Real.log T⌋ + 1).toNat) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hcardNat
  exact mul_le_mul_of_nonneg_right
    hcardReal hV

/-- Final deterministic finite-sum assembly.  Once the two extreme pieces
and every occupied medium bin have been bounded, only the explicit
square-logarithmic number of bins remains.  This is the discrete counterpart
of `integral_typeII_le_of_extremes_and_medium_bins` below. -/
theorem sum_typeII_le_of_extremes_and_medium_bins
    (R : Finset ℝ) (M₁ M₂ : ℂ → ℂ) (N₁ N₂ T ε V : ℝ)
    (f : ℝ → ℝ) {E₁ E₃ : ℝ}
    (hT : 0 < T) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂) (hε : 0 ≤ ε)
    (hV : 0 ≤ V)
    (h₁ : (∑ t ∈ finiteLargeValueR1 R M₁ M₂ N₁ N₂ ε, f t) ≤ E₁)
    (h₃ : (∑ t ∈ finiteLargeValueR3 R M₁ M₂ N₁ N₂ T ε, f t) ≤ E₃)
    (hbin : ∀ k ∈ occupiedMediumLogMagnitudePairs R M₁ M₂ N₁ N₂ T ε,
      (∑ t ∈ finiteMediumLogMagnitudeBin R M₁ M₂ N₁ N₂ T ε k, f t) ≤ V) :
    ∑ t ∈ R, f t ≤
      E₁ + ((((⌊Real.log T⌋ + 1).toNat) ^ 2 : ℕ) : ℝ) * V + E₃ := by
  apply sum_finiteLargeValue_partition_le R M₁ M₂ N₁ N₂ T ε f h₁
  · exact sum_finiteLargeValueR2_le_logBinCount_mul
      R M₁ M₂ N₁ N₂ T ε V f hT hN₁ hN₂ hε hV hbin
  · exact h₃

/-- The measurable subset of `R₂` belonging to the logarithmic pair bin
`k`. -/
def mediumLogMagnitudeBinSet (R : Set ℝ) (M₁ M₂ : ℂ → ℂ)
    (N₁ N₂ T ε : ℝ) (k : ℤ × ℤ) : Set ℝ :=
  largeValueR2 R M₁ M₂ N₁ N₂ T ε ∩
    logMagnitudePairBin M₁ M₂ k.1 k.2

theorem measurableSet_mediumLogMagnitudeBinSet
    {R : Set ℝ} {M₁ M₂ : ℂ → ℂ} {N₁ N₂ T ε : ℝ} {k : ℤ × ℤ}
    (hR : MeasurableSet R)
    (hM₁ : Measurable (typeIIMagnitude M₁))
    (hM₂ : Measurable (typeIIMagnitude M₂)) :
    MeasurableSet (mediumLogMagnitudeBinSet R M₁ M₂ N₁ N₂ T ε k) :=
  (measurableSet_largeValueR2 hR hM₁ hM₂).inter
    (measurableSet_logMagnitudePairBin hM₁ hM₂)

/-- Distinct logarithmic pair bins are disjoint, even after intersection
with `R₂`. -/
theorem mediumLogMagnitudeBinSet_disjoint {R : Set ℝ} {M₁ M₂ : ℂ → ℂ}
    {N₁ N₂ T ε : ℝ} {k l : ℤ × ℤ} (hkl : k ≠ l) :
    Disjoint (mediumLogMagnitudeBinSet R M₁ M₂ N₁ N₂ T ε k)
      (mediumLogMagnitudeBinSet R M₁ M₂ N₁ N₂ T ε l) := by
  rw [Set.disjoint_left]
  intro t htk htl
  exact hkl (Prod.ext
    (logMagnitudeBin_index_unique htk.2.1 htl.2.1)
    (logMagnitudeBin_index_unique htk.2.2 htl.2.2))

/-- Under the medium-range hypotheses, the explicit finite square of
indices covers all of `R₂`. -/
theorem iUnion_mediumLogMagnitudeBinSet_eq_largeValueR2
    {R : Set ℝ} {M₁ M₂ : ℂ → ℂ} {N₁ N₂ T ε : ℝ}
    (hT : 0 < T) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂) (hε : 0 ≤ ε) :
    (⋃ k ∈ logMagnitudePairIndexRange T,
      mediumLogMagnitudeBinSet R M₁ M₂ N₁ N₂ T ε k) =
        largeValueR2 R M₁ M₂ N₁ N₂ T ε := by
  ext t
  constructor
  · intro ht
    simp only [Set.mem_iUnion] at ht
    rcases ht with ⟨k, -, hk⟩
    exact hk.1
  · intro ht
    let k := canonicalLogMagnitudePair M₁ M₂ t
    have hbounds :=
      logMagnitude_bounds_of_mem_largeValueR2 hT hN₁ hN₂ hε ht
    have hk : k ∈ logMagnitudePairIndexRange T := by
      exact Finset.mem_product.mpr
        ⟨floor_logMagnitude_mem_indexRange hbounds.1,
          floor_logMagnitude_mem_indexRange hbounds.2⟩
    simp only [Set.mem_iUnion]
    refine ⟨k, hk, ht, ?_, ?_⟩
    · exact mem_logMagnitudeBin_floor M₁ t
    · exact mem_logMagnitudeBin_floor M₂ t

/-- Exact finite-bin decomposition of the integral over `R₂`. -/
theorem integral_largeValueR2_eq_sum_logMagnitudeBins
    {R : Set ℝ} {M₁ M₂ : ℂ → ℂ} {N₁ N₂ T ε : ℝ} {f : ℝ → ℝ}
    (hR : MeasurableSet R)
    (hM₁ : Measurable (typeIIMagnitude M₁))
    (hM₂ : Measurable (typeIIMagnitude M₂))
    (hf : IntegrableOn f (largeValueR2 R M₁ M₂ N₁ N₂ T ε))
    (hT : 0 < T) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂) (hε : 0 ≤ ε) :
    ∫ t in largeValueR2 R M₁ M₂ N₁ N₂ T ε, f t =
      ∑ k ∈ logMagnitudePairIndexRange T,
        ∫ t in mediumLogMagnitudeBinSet R M₁ M₂ N₁ N₂ T ε k, f t := by
  rw [← iUnion_mediumLogMagnitudeBinSet_eq_largeValueR2 hT hN₁ hN₂ hε]
  exact integral_biUnion_finset (logMagnitudePairIndexRange T)
    (fun k _ ↦ measurableSet_mediumLogMagnitudeBinSet hR hM₁ hM₂)
    (by
      intro k hk l hl hkl
      exact mediumLogMagnitudeBinSet_disjoint hkl)
    (fun k _ ↦ hf.mono_set Set.inter_subset_left)

/-- A uniform integral estimate on every medium logarithmic bin incurs
exactly the explicit square-logarithmic bin count. -/
theorem integral_largeValueR2_le_logBinCount_mul
    {R : Set ℝ} {M₁ M₂ : ℂ → ℂ} {N₁ N₂ T ε V : ℝ} {f : ℝ → ℝ}
    (hR : MeasurableSet R)
    (hM₁ : Measurable (typeIIMagnitude M₁))
    (hM₂ : Measurable (typeIIMagnitude M₂))
    (hf : IntegrableOn f (largeValueR2 R M₁ M₂ N₁ N₂ T ε))
    (hT : 0 < T) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂) (hε : 0 ≤ ε)
    (hbin : ∀ k ∈ logMagnitudePairIndexRange T,
      (∫ t in mediumLogMagnitudeBinSet R M₁ M₂ N₁ N₂ T ε k, f t) ≤ V) :
    ∫ t in largeValueR2 R M₁ M₂ N₁ N₂ T ε, f t ≤
      ((((⌊Real.log T⌋ + 1).toNat) ^ 2 : ℕ) : ℝ) * V := by
  rw [integral_largeValueR2_eq_sum_logMagnitudeBins hR hM₁ hM₂ hf
    hT hN₁ hN₂ hε]
  have hsum := Finset.sum_le_card_nsmul (logMagnitudePairIndexRange T)
    (fun k ↦ ∫ t in mediumLogMagnitudeBinSet R M₁ M₂ N₁ N₂ T ε k, f t)
    V hbin
  simpa [card_logMagnitudePairIndexRange] using hsum

/-- Final deterministic integral assembly: after the two extreme regimes
and each medium logarithmic bin have been bounded, Proposition 5.1 reduces
to adding those three contributions. -/
theorem integral_typeII_le_of_extremes_and_medium_bins
    {R : Set ℝ} {M₁ M₂ : ℂ → ℂ} {N₁ N₂ T ε V : ℝ} {f : ℝ → ℝ}
    {E₁ E₃ : ℝ}
    (hR : MeasurableSet R)
    (hM₁ : Measurable (typeIIMagnitude M₁))
    (hM₂ : Measurable (typeIIMagnitude M₂))
    (hf : IntegrableOn f R)
    (hT : 0 < T) (hN₁ : 1 ≤ N₁) (hN₂ : 1 ≤ N₂) (hε : 0 ≤ ε)
    (h₁ : (∫ t in largeValueR1 R M₁ M₂ N₁ N₂ ε, f t) ≤ E₁)
    (h₃ : (∫ t in largeValueR3 R M₁ M₂ N₁ N₂ T ε, f t) ≤ E₃)
    (hbin : ∀ k ∈ logMagnitudePairIndexRange T,
      (∫ t in mediumLogMagnitudeBinSet R M₁ M₂ N₁ N₂ T ε k, f t) ≤ V) :
    ∫ t in R, f t ≤
      E₁ + ((((⌊Real.log T⌋ + 1).toNat) ^ 2 : ℕ) : ℝ) * V + E₃ := by
  apply integral_largeValue_partition_le hR hM₁ hM₂ hf h₁
  · exact integral_largeValueR2_le_logBinCount_mul hR hM₁ hM₂
      (hf.mono_set Set.sdiff_subset) hT hN₁ hN₂ hε hbin
  · exact h₃

/-! ## The exact one-spaced-sum to integral bridge -/

/-- A uniform estimate for the precise Type-II weight on every finite
one-spaced subset of `U` implies the desired integral estimate with the
explicit absolute factor `2`.  Continuity supplies integrability, so the
caller has no remaining measure-theoretic side condition to discharge. -/
theorem integral_typeII_weight_le_two_mul_of_uniform_oneSpaced_sum_bound
    {U : Set ℝ} {T E N₁ N₂ : ℝ} {a₁ a₂ : ℕ → ℂ}
    (hUmeas : MeasurableSet U) (hU : U ⊆ Set.Icc 0 T)
    (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hsum : ∀ R : Finset ℝ,
      (R : Set ℝ) ⊆ U → IsOneSpaced (R : Set ℝ) →
        (∑ t ∈ R,
          ‖dyadicDirichletPolynomial a₁ N₁ (onePlusIT t)‖ ^ 2 *
          ‖dyadicDirichletPolynomial a₂ N₂ (onePlusIT t)‖ ^ 2) ≤ E) :
    (∫ t in U,
      ‖dyadicDirichletPolynomial a₁ N₁ (onePlusIT t)‖ ^ 2 *
      ‖dyadicDirichletPolynomial a₂ N₂ (onePlusIT t)‖ ^ 2) ≤ 2 * E := by
  exact Hybrid.integral_le_two_mul_of_uniform_oneSpaced_sum_bound
    hUmeas hU (Hybrid.integrableOn_typeII_weight hN₁ hN₂ hU)
    (fun t _ ↦ Hybrid.typeII_weight_nonneg a₁ a₂ N₁ N₂ t) hsum

/-- Fully quantified target corresponding to Proposition 5.1.  The auxiliary
number `S` is an explicit upper bound for the supremum of the first
polynomial on `U`; using it avoids hiding a boundedness convention inside
`sSup`.  The quantifier order records the repaired uniformity: `κ₁` may
depend on `ε` and `B`, but not on `A₀`, `L`, the lengths, or the coefficient
sequences. -/
def TypeIIEstimateStatement : Prop :=
  ∃ C₁ ε₀ : ℝ, 0 < C₁ ∧ 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ B : ℝ, 0 ≤ B →
        ∃ κ₁ : ℝ, 0 < κ₁ ∧
          ∀ A₀ L : ℝ, 1 ≤ A₀ → 0 ≤ L →
            ∃ C₂ C T₀ : ℝ,
              0 < C₂ ∧ 0 < C ∧ 1 ≤ T₀ ∧
                ∀ (T : ℝ) (N₁ N₂ : ℕ) (a₁ a₂ : ℕ → ℂ)
                    (U : Set ℝ) (S : ℝ),
                  T₀ ≤ T → 1 ≤ N₁ → 1 ≤ N₂ →
                  (Real.log T) ^ (-L) ≤
                    ((N₁ : ℝ) * (N₂ : ℝ)) / T →
                  ((N₁ : ℝ) * (N₂ : ℝ)) / T ≤
                    (Real.log T) ^ L →
                  T ^ (ε / 5) ≤ (N₁ : ℝ) →
                  (N₁ : ℝ) ≤ T ^ (2 / 11 + ε) →
                  IsDivisorBoundedByConstant B A₀ a₁ →
                  IsDivisorBoundedByConstant B A₀ a₂ →
                  MeasurableSet U → U ⊆ Set.Icc (0 : ℝ) T →
                  (∀ t ∈ U,
                    (N₁ : ℝ) ^ (-(17 / 70 - C₁ * ε)) ≤
                        ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ)
                          (onePlusIT t)‖ ∨
                      (N₂ : ℝ) ^ (-(17 / 70 - C₁ * ε)) ≤
                        ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ)
                          (onePlusIT t)‖) →
                  0 ≤ S →
                  (∀ t ∈ U,
                    ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ)
                      (onePlusIT t)‖ ^ 2 ≤ S) →
                  (∫ t in U,
                      ‖dyadicDirichletPolynomial a₁ (N₁ : ℝ)
                        (onePlusIT t)‖ ^ 2 *
                      ‖dyadicDirichletPolynomial a₂ (N₂ : ℝ)
                        (onePlusIT t)‖ ^ 2) ≤
                    C * (T ^ (-κ₁) + (Real.log T) ^ C₂ * S)

def typeIIEstimateModule : ProofModule :=
  { name := "TypeII.TypeIIEstimate"
    paperLocation := "Proposition 5.1"
    purpose :=
      "Define the fully quantified Proposition 5.1 target and prove its deterministic R₁/R₂/R₃ partition, logarithmic-bin summation, and exact one-spaced-sum-to-integral bridge. The analytic instantiation is completed in TypeII.FullTypeIIEstimate."
    dependsOn :=
      ["TypeII.WeightedExtremeRange", "TypeII.ExtremeSmallAssembly",
        "TypeII.MediumLogBinBridge", "TypeII.OuterParameterReserve",
        "TypeII.OuterLengthGeometry",
        "TypeII.LargeValuePartition", "Hybrid.IntegralDiscretization"]
    status := .proved }

end

end TypeII
end ExactSemiprimes
