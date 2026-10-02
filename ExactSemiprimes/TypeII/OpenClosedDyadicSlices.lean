import ExactSemiprimes.TypeII.PoweredMeanValue

/-!
# Endpoint-compatible dyadic slices

The hybrid density theorem is stated for Dirichlet polynomials supported on
open--closed intervals `(P,2P]`.  This file supplies the matching finite
tuple partition for a positive power of a polynomial on `(M,2M]`.
-/

namespace ExactSemiprimes
namespace TypeII

open scoped BigOperators

noncomputable section

/-- Tuples whose product lies in the open--closed dyadic interval
`(2^j L, 2^(j+1)L]`. -/
def openClosedDyadicTuplePiece (S : Finset ℕ) (ell : ℕ)
    (L : ℝ) (j : ℕ) : Finset (Fin ell → ℕ) :=
  (powerTuples S ell).filter fun f ↦
    (2 : ℝ) ^ j * L < (tupleProduct f : ℝ) ∧
      (tupleProduct f : ℝ) ≤ (2 : ℝ) ^ (j + 1) * L

@[simp]
theorem mem_openClosedDyadicTuplePiece_iff
    {S : Finset ℕ} {ell : ℕ} {L : ℝ} {j : ℕ}
    {f : Fin ell → ℕ} :
    f ∈ openClosedDyadicTuplePiece S ell L j ↔
      f ∈ powerTuples S ell ∧
      (2 : ℝ) ^ j * L < (tupleProduct f : ℝ) ∧
      (tupleProduct f : ℝ) ≤ (2 : ℝ) ^ (j + 1) * L := by
  simp [openClosedDyadicTuplePiece]

/-- Every point of `(L,2^r L]` lies in one of its first `r`
open--closed dyadic pieces. -/
theorem exists_openClosedDyadicIndex {L x : ℝ} {r : ℕ}
    (hlower : L < x) (hupper : x ≤ (2 : ℝ) ^ r * L) :
    ∃ j < r, (2 : ℝ) ^ j * L < x ∧
      x ≤ (2 : ℝ) ^ (j + 1) * L := by
  induction r with
  | zero =>
      norm_num at hupper
      exact (not_lt_of_ge hupper hlower).elim
  | succ r ih =>
      by_cases hmid : x ≤ (2 : ℝ) ^ r * L
      · obtain ⟨j, hj, hjbounds⟩ := ih hmid
        exact ⟨j, hj.trans (Nat.lt_succ_self r), hjbounds⟩
      · refine ⟨r, Nat.lt_succ_self r, lt_of_not_ge hmid, ?_⟩
        simpa [Nat.succ_eq_add_one] using hupper

/-- Distinct open--closed pieces are disjoint. -/
theorem openClosedDyadicTuplePiece_pairwiseDisjoint
    (S : Finset ℕ) (ell : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    (Set.univ : Set ℕ).PairwiseDisjoint
      (openClosedDyadicTuplePiece S ell L) := by
  intro i _ j _ hij
  change Disjoint (openClosedDyadicTuplePiece S ell L i)
    (openClosedDyadicTuplePiece S ell L j)
  rw [Finset.disjoint_left]
  intro f hfi hfj
  have hi := (mem_openClosedDyadicTuplePiece_iff.mp hfi).2
  have hj := (mem_openClosedDyadicTuplePiece_iff.mp hfj).2
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hp : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hscaled : (2 : ℝ) ^ (i + 1) * L ≤ (2 : ℝ) ^ j * L :=
      mul_le_mul_of_nonneg_right hp hL
    exact (not_lt_of_ge (hi.2.trans hscaled)) hj.1
  · have hp : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ i :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hscaled : (2 : ℝ) ^ (j + 1) * L ≤ (2 : ℝ) ^ i * L :=
      mul_le_mul_of_nonneg_right hp hL
    exact (not_lt_of_ge (hj.2.trans hscaled)) hi.1

/-- If every tuple product lies in `(L,2^r L]`, the first `r`
open--closed pieces cover the tuple set. -/
theorem biUnion_openClosedDyadicTuplePiece_eq
    {S : Finset ℕ} {ell r : ℕ} {L : ℝ}
    (hbounds : ∀ f ∈ powerTuples S ell,
      L < (tupleProduct f : ℝ) ∧
        (tupleProduct f : ℝ) ≤ (2 : ℝ) ^ r * L) :
    (Finset.range r).biUnion (openClosedDyadicTuplePiece S ell L) =
      powerTuples S ell := by
  ext f
  constructor
  · simp only [Finset.mem_biUnion, Finset.mem_range]
    rintro ⟨j, _, hj⟩
    exact (mem_openClosedDyadicTuplePiece_iff.mp hj).1
  · intro hf
    obtain ⟨j, hjr, hj⟩ :=
      exists_openClosedDyadicIndex (hbounds f hf).1 (hbounds f hf).2
    simp only [Finset.mem_biUnion, Finset.mem_range]
    exact ⟨j, hjr,
      mem_openClosedDyadicTuplePiece_iff.mpr ⟨hf, hj⟩⟩

/-- The tuple sum is exactly the sum over the endpoint-compatible pieces. -/
theorem sum_openClosedDyadicTuplePieces
    {S : Finset ℕ} {ell r : ℕ} {L : ℝ} (hL : 0 ≤ L)
    (hbounds : ∀ f ∈ powerTuples S ell,
      L < (tupleProduct f : ℝ) ∧
        (tupleProduct f : ℝ) ≤ (2 : ℝ) ^ r * L)
    (F : (Fin ell → ℕ) → ℂ) :
    ∑ f ∈ powerTuples S ell, F f =
      ∑ j ∈ Finset.range r,
        ∑ f ∈ openClosedDyadicTuplePiece S ell L j, F f := by
  rw [← biUnion_openClosedDyadicTuplePiece_eq hbounds]
  apply Finset.sum_biUnion
  intro i _ j _ hij
  exact openClosedDyadicTuplePiece_pairwiseDisjoint S ell hL
    (Set.mem_univ i) (Set.mem_univ j) hij

/-- Products of a positive number of factors from `(M,2M]` are strictly
larger than `M^ell`. -/
theorem poweredTupleProduct_lower_strict
    {S : Finset ℕ} {M : ℝ} {ell : ℕ}
    (hM : 0 < M) (hell : 1 ≤ ell)
    (hS : ∀ n ∈ S, InDyadicRange M n)
    {f : Fin ell → ℕ} (hf : f ∈ powerTuples S ell) :
    M ^ ell < (tupleProduct f : ℝ) := by
  have hnonempty : (Finset.univ : Finset (Fin ell)).Nonempty := by
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hprod :
      (∏ _i : Fin ell, M) < ∏ i : Fin ell, (f i : ℝ) := by
    apply Finset.prod_lt_prod_of_nonempty₀
    · intro _i _hi
      exact hM
    · intro i _hi
      exact (hS (f i) ((mem_powerTuples_iff.mp hf) i)).1
    · exact hnonempty
  simpa [tupleProduct, Nat.cast_prod] using hprod

/-- The endpoint-compatible powered support uses exactly `ell` pieces, not
`ell+1`: the last piece includes the upper endpoint `(2M)^ell`. -/
theorem poweredOpenClosedDyadicTupleBounds
    {S : Finset ℕ} {M : ℝ} {ell : ℕ}
    (hM : 0 < M) (hell : 1 ≤ ell)
    (hS : ∀ n ∈ S, InDyadicRange M n) :
    ∀ f ∈ powerTuples S ell,
      M ^ ell < (tupleProduct f : ℝ) ∧
        (tupleProduct f : ℝ) ≤ (2 : ℝ) ^ ell * M ^ ell := by
  intro f hf
  refine ⟨poweredTupleProduct_lower_strict hM hell hS hf, ?_⟩
  have hupper := (tupleProduct_mem_poweredSupport hM.le hf hS).2
  simpa [mul_pow] using hupper

/-- Concrete endpoint-compatible decomposition of the powered tuple sum. -/
theorem sum_poweredOpenClosedDyadicTuplePieces
    {S : Finset ℕ} {M : ℝ} {ell : ℕ}
    (hM : 0 < M) (hell : 1 ≤ ell)
    (hS : ∀ n ∈ S, InDyadicRange M n)
    (F : (Fin ell → ℕ) → ℂ) :
    ∑ f ∈ powerTuples S ell, F f =
      ∑ j ∈ Finset.range ell,
        ∑ f ∈ openClosedDyadicTuplePiece S ell (M ^ ell) j, F f := by
  exact sum_openClosedDyadicTuplePieces (pow_nonneg hM.le ell)
    (poweredOpenClosedDyadicTupleBounds hM hell hS) F

/-! ## Identification with ordinary dyadic Dirichlet polynomials -/

/-- A tuple slice is exactly the ordinary Dirichlet polynomial of the
collected convolution coefficient on the corresponding interval `(P,2P]`.
This is the endpoint bridge missing from the earlier half-open slicing. -/
theorem dyadicConvolutionPolynomial_eq_openClosedTuplePiece
    (a : ℕ → ℂ) (S : Finset ℕ) (ell j : ℕ)
    {L : ℝ} (hL : 0 ≤ L) (s : ℂ) :
    dyadicDirichletPolynomial (powerConvolutionCoefficient a S ell)
        ((2 : ℝ) ^ j * L) s =
      ∑ f ∈ openClosedDyadicTuplePiece S ell L j,
        tupleCoefficient a f * (tupleProduct f : ℂ) ^ (-s) := by
  classical
  let P : ℝ := (2 : ℝ) ^ j * L
  have hP : 0 ≤ P := mul_nonneg (pow_nonneg (by norm_num) j) hL
  have hupperIdentity : (2 : ℝ) ^ (j + 1) * L = 2 * P := by
    dsimp [P]
    rw [pow_succ]
    ring
  have hmaps : ∀ f ∈ openClosedDyadicTuplePiece S ell L j,
      tupleProduct f ∈ dyadicInterval P := by
    intro f hf
    have hb := (mem_openClosedDyadicTuplePiece_iff.mp hf).2
    apply (mem_dyadicInterval hP).2
    exact ⟨by simpa [P] using hb.1, by simpa [hupperIdentity] using hb.2⟩
  have hfiber : ∀ n ∈ dyadicInterval P,
      (openClosedDyadicTuplePiece S ell L j).filter
          (fun f ↦ tupleProduct f = n) =
        (powerTuples S ell).filter (fun f ↦ tupleProduct f = n) := by
    intro n hn
    have hnrange := (mem_dyadicInterval hP).mp hn
    ext f
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hf, hfn⟩
      exact ⟨(mem_openClosedDyadicTuplePiece_iff.mp hf).1, hfn⟩
    · rintro ⟨hf, hfn⟩
      refine ⟨mem_openClosedDyadicTuplePiece_iff.mpr
        ⟨hf, ?_, ?_⟩, hfn⟩
      · rw [hfn]
        simpa [P] using hnrange.1
      · rw [hfn, hupperIdentity]
        exact hnrange.2
  change dirichletPolynomial (powerConvolutionCoefficient a S ell)
      (dyadicInterval ((2 : ℝ) ^ j * L)) s = _
  change (∑ n ∈ dyadicInterval P,
      powerConvolutionCoefficient a S ell n * (n : ℂ) ^ (-s)) = _
  calc
    (∑ n ∈ dyadicInterval P,
        powerConvolutionCoefficient a S ell n * (n : ℂ) ^ (-s)) =
        ∑ n ∈ dyadicInterval P,
          (∑ f ∈ openClosedDyadicTuplePiece S ell L j with
              tupleProduct f = n, tupleCoefficient a f) *
            (n : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [powerConvolutionCoefficient, ← hfiber n hn]
    _ = ∑ n ∈ dyadicInterval P,
          ∑ f ∈ openClosedDyadicTuplePiece S ell L j with
              tupleProduct f = n,
            tupleCoefficient a f * (n : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [Finset.sum_mul]
    _ = ∑ n ∈ dyadicInterval P,
          ∑ f ∈ openClosedDyadicTuplePiece S ell L j with
              tupleProduct f = n,
            tupleCoefficient a f * (tupleProduct f : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro n _hn
      apply Finset.sum_congr rfl
      intro f hf
      rw [(Finset.mem_filter.mp hf).2]
    _ = ∑ f ∈ openClosedDyadicTuplePiece S ell L j,
          tupleCoefficient a f * (tupleProduct f : ℂ) ^ (-s) := by
      exact Finset.sum_fiberwise_of_maps_to hmaps _

/-- A large powered tuple sum has an endpoint-compatible dyadic slice
carrying at least its `1/ell` share. -/
theorem exists_large_poweredOpenClosedDyadicTuplePiece
    {S : Finset ℕ} {M : ℝ} {ell : ℕ}
    (hM : 0 < M) (hell : 1 ≤ ell)
    (hS : ∀ n ∈ S, InDyadicRange M n)
    (F : (Fin ell → ℕ) → ℂ) :
    ∃ j < ell,
      ‖∑ f ∈ powerTuples S ell, F f‖ / (ell : ℝ) ≤
        ‖∑ f ∈ openClosedDyadicTuplePiece S ell (M ^ ell) j,
          F f‖ := by
  let total : ℂ := ∑ f ∈ powerTuples S ell, F f
  let piece : ℕ → ℂ := fun j ↦
    ∑ f ∈ openClosedDyadicTuplePiece S ell (M ^ ell) j, F f
  have hdecomp : total = ∑ j ∈ Finset.range ell, piece j := by
    exact sum_poweredOpenClosedDyadicTuplePieces hM hell hS F
  have hnorm : ‖total‖ ≤ ∑ j ∈ Finset.range ell, ‖piece j‖ := by
    rw [hdecomp]
    exact norm_sum_le _ _
  have haverage :
      ∑ _j ∈ Finset.range ell, ‖total‖ / (ell : ℝ) ≤
        ∑ j ∈ Finset.range ell, ‖piece j‖ := by
    calc
      ∑ _j ∈ Finset.range ell, ‖total‖ / (ell : ℝ) = ‖total‖ := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        have hell0 : (ell : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hell))
        field_simp [hell0]
      _ ≤ ∑ j ∈ Finset.range ell, ‖piece j‖ := hnorm
  obtain ⟨j, hj, hjlarge⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr (by omega : ell ≠ 0)) haverage
  exact ⟨j, Finset.mem_range.mp hj, hjlarge⟩

/-- Polynomial form of the endpoint-compatible pigeonhole step.  At every
height, one of the `ell` ordinary dyadic convolution polynomials carries at
least a `1/ell` fraction of the powered value. -/
theorem exists_large_poweredOpenClosedDyadicPolynomial
    (a : ℕ → ℂ) {S : Finset ℕ} {M : ℝ} {ell : ℕ}
    (hM : 0 < M) (hell : 1 ≤ ell)
    (hS : ∀ n ∈ S, InDyadicRange M n) (s : ℂ) :
    ∃ j < ell,
      ‖dirichletPolynomial a S s ^ ell‖ / (ell : ℝ) ≤
        ‖dyadicDirichletPolynomial
          (powerConvolutionCoefficient a S ell)
          ((2 : ℝ) ^ j * M ^ ell) s‖ := by
  let F : (Fin ell → ℕ) → ℂ := fun f ↦
    tupleCoefficient a f * (tupleProduct f : ℂ) ^ (-s)
  obtain ⟨j, hj, hjlarge⟩ :=
    exists_large_poweredOpenClosedDyadicTuplePiece hM hell hS F
  refine ⟨j, hj, ?_⟩
  calc
    ‖dirichletPolynomial a S s ^ ell‖ / (ell : ℝ) =
        ‖∑ f ∈ powerTuples S ell, F f‖ / (ell : ℝ) := by
      congr 2
      rw [dirichletPolynomial_pow_eq_tupleSum]
      apply Finset.sum_congr rfl
      intro f _hf
      exact tupleDirichletTerm_eq f s
    _ ≤ ‖∑ f ∈ openClosedDyadicTuplePiece S ell (M ^ ell) j,
          F f‖ := hjlarge
    _ = ‖dyadicDirichletPolynomial
          (powerConvolutionCoefficient a S ell)
          ((2 : ℝ) ^ j * M ^ ell) s‖ := by
      rw [dyadicConvolutionPolynomial_eq_openClosedTuplePiece
        a S ell j (pow_nonneg hM.le ell) s]

/-! ## Aggregating the height-dependent slice choice -/

/-- A pointwise choice among at most `ell` large slices costs at most the
factor `ell` in cardinality.  The slice sets need not be disjoint; using a
cover makes the lemma directly applicable to existential choices. -/
theorem card_le_ell_mul_of_heightSlice_cover
    {α : Type*} [DecidableEq α]
    (R : Finset α) {ell : ℕ}
    (Large : ℕ → α → Prop) [DecidableRel Large]
    {Y : ℝ}
    (hselect : ∀ t ∈ R, ∃ j < ell, Large j t)
    (hslice : ∀ j < ell,
      ((R.filter fun t ↦ Large j t).card : ℝ) ≤ Y) :
    (R.card : ℝ) ≤ (ell : ℝ) * Y := by
  let pieces : ℕ → Finset α :=
    fun j ↦ R.filter fun t ↦ Large j t
  have hcover : R ⊆ (Finset.range ell).biUnion pieces := by
    intro t ht
    obtain ⟨j, hj, hlarge⟩ := hselect t ht
    exact Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_range.mpr hj,
        Finset.mem_filter.mpr ⟨ht, hlarge⟩⟩
  calc
    (R.card : ℝ) ≤
        (((Finset.range ell).biUnion pieces).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hcover
    _ ≤ ∑ j ∈ Finset.range ell, ((pieces j).card : ℝ) := by
      exact_mod_cast
        (Finset.card_biUnion_le
          (s := Finset.range ell) (t := pieces))
    _ ≤ ∑ _j ∈ Finset.range ell, Y := by
      apply Finset.sum_le_sum
      intro j hj
      simpa [pieces] using hslice j (Finset.mem_range.mp hj)
    _ = (ell : ℝ) * Y := by simp

def openClosedDyadicSlicesModule : ProofModule :=
  { name := "TypeII.OpenClosedDyadicSlices"
    paperLocation := "Proof of Proposition 5.1, powered medium branch"
    purpose :=
      "Partition a powered tuple expansion into slices with the exact (P,2P] endpoint convention required by the hybrid-density theorem, and aggregate height-dependent slice choices."
    dependsOn := ["TypeII.PoweredPolynomial", "TypeII.PoweredMeanValue"]
    status := .proved }

end

end TypeII
end ExactSemiprimes
