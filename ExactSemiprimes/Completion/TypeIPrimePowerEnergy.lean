import ExactSemiprimes.Sparse.QLowerBound
import ExactSemiprimes.TypeII.OpenClosedDyadicSlices

/-!
# Coefficient energy for the Type-I inserted prime power

This file proves the finite combinatorics behind MT23 equation (5.4).
The unnormalised `k`th power of a prime polynomial has nonnegative integer
coefficients.  Each product fibre has at most `k!` elements, and the sum of
all fibre sizes is exactly the number of ordered tuples.  Consequently every
dyadic slice has squared coefficient energy at most

`k! * |S|^k`.

The later scale layer may replace `|S|^k` by the appropriate power of the
nominal length.  No analytic input is used here.
-/

namespace ExactSemiprimes
namespace Completion

open scoped BigOperators

noncomputable section

/-- The raw coefficient of the `k`th power of a polynomial with unit
coefficients on `S`. -/
def rawPrimePowerCoefficient (S : Finset ℕ) (k n : ℕ) : ℂ :=
  TypeII.powerConvolutionCoefficient (fun _ ↦ 1) S k n

def rawPrimePowerFiber (S : Finset ℕ) (k n : ℕ) :
    Finset (Fin k → ℕ) :=
  (TypeII.powerTuples S k).filter fun f ↦ TypeII.tupleProduct f = n

@[simp]
theorem rawPrimePowerCoefficient_eq_card
    (S : Finset ℕ) (k n : ℕ) :
    rawPrimePowerCoefficient S k n = (rawPrimePowerFiber S k n).card := by
  classical
  simp [rawPrimePowerCoefficient, rawPrimePowerFiber,
    TypeII.powerConvolutionCoefficient, TypeII.tupleCoefficient]

@[simp]
theorem norm_rawPrimePowerCoefficient
    (S : Finset ℕ) (k n : ℕ) :
    ‖rawPrimePowerCoefficient S k n‖ = (rawPrimePowerFiber S k n).card := by
  rw [rawPrimePowerCoefficient_eq_card]
  simp

/-- Forgetting the membership proofs identifies the raw product fibre with
a subset of the prime-tuple fibre used in `Sparse.PrimePowerPolynomial`. -/
theorem card_rawPrimePowerFiber_le_primeTupleFiber
    {S : Finset ℕ} {k n : ℕ} :
    (rawPrimePowerFiber S k n).card ≤
      (Sparse.primeTupleFiber S k n).card := by
  classical
  let Φ : {f // f ∈ rawPrimePowerFiber S k n} →
      {g // g ∈ Sparse.primeTupleFiber S k n} := fun f ↦ by
    let g : Sparse.PrimeTuple S k := fun i ↦
      ⟨f.1 i, (TypeII.mem_powerTuples_iff.mp
        (Finset.mem_filter.mp f.2).1) i⟩
    exact ⟨g, Sparse.mem_primeTupleFiber.mpr (by
      simpa [g, Sparse.primeTupleProduct, TypeII.tupleProduct] using
        (Finset.mem_filter.mp f.2).2)⟩
  have hΦ : Function.Injective Φ := by
    intro f g hfg
    apply Subtype.ext
    apply funext
    intro i
    have hi := congrArg (fun u ↦ ((u.1 i : S) : ℕ)) hfg
    exact hi
  have hcard : Fintype.card {f // f ∈ rawPrimePowerFiber S k n} ≤
      Fintype.card {g // g ∈ Sparse.primeTupleFiber S k n} :=
    Fintype.card_le_of_injective Φ hΦ
  calc
    (rawPrimePowerFiber S k n).card =
        Fintype.card {f // f ∈ rawPrimePowerFiber S k n} := by simp
    _ ≤ Fintype.card {g // g ∈ Sparse.primeTupleFiber S k n} := hcard
    _ = (Sparse.primeTupleFiber S k n).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext g
      simp

/-- Unique factorisation gives the same sharp `k!` bound for the raw
convolution fibre. -/
theorem card_rawPrimePowerFiber_le_factorial
    {S : Finset ℕ} {k n : ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    (rawPrimePowerFiber S k n).card ≤ k.factorial :=
  (card_rawPrimePowerFiber_le_primeTupleFiber).trans
    (Sparse.primeTupleFiber_card_le_factorial hS)

theorem norm_rawPrimePowerCoefficient_le_factorial
    {S : Finset ℕ} {k n : ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    ‖rawPrimePowerCoefficient S k n‖ ≤ (k.factorial : ℝ) := by
  rw [norm_rawPrimePowerCoefficient]
  exact_mod_cast card_rawPrimePowerFiber_le_factorial hS

/-- The image of the tuple product is the finite support of the raw
coefficient sequence. -/
def rawPrimePowerSupport (S : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (TypeII.powerTuples S k).image TypeII.tupleProduct

theorem rawPrimePowerCoefficient_eq_zero_of_not_mem
    {S : Finset ℕ} {k n : ℕ} (hn : n ∉ rawPrimePowerSupport S k) :
    rawPrimePowerCoefficient S k n = 0 := by
  classical
  have hempty : rawPrimePowerFiber S k n = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨f, hf⟩
    apply hn
    exact Finset.mem_image.mpr
      ⟨f, (Finset.mem_filter.mp hf).1, (Finset.mem_filter.mp hf).2⟩
  simp [rawPrimePowerCoefficient_eq_card, hempty]

/-- Summing the fibre cardinalities recovers the cardinality of the entire
ordered tuple set. -/
theorem sum_rawPrimePowerFiber_card
    (S : Finset ℕ) (k : ℕ) :
    ∑ n ∈ rawPrimePowerSupport S k, (rawPrimePowerFiber S k n).card =
      (TypeII.powerTuples S k).card := by
  classical
  symm
  exact Finset.card_eq_sum_card_fiberwise
    (fun f hf ↦ Finset.mem_image.mpr ⟨f, hf, rfl⟩)

/-- Exact real-valued version of the preceding count. -/
theorem sum_norm_rawPrimePowerCoefficient
    (S : Finset ℕ) (k : ℕ) :
    ∑ n ∈ rawPrimePowerSupport S k, ‖rawPrimePowerCoefficient S k n‖ =
      (S.card : ℝ) ^ k := by
  rw [show (∑ n ∈ rawPrimePowerSupport S k,
      ‖rawPrimePowerCoefficient S k n‖) =
      ((∑ n ∈ rawPrimePowerSupport S k,
        (rawPrimePowerFiber S k n).card : ℕ) : ℝ) by
    simp only [norm_rawPrimePowerCoefficient, Nat.cast_sum]]
  rw [sum_rawPrimePowerFiber_card, TypeII.card_powerTuples]
  norm_cast

/-- The sharp finite coefficient-energy estimate behind MT23 (5.4).  It
holds for every finite index set `D`, hence in particular for each dyadic
slice accepted by Lemma 3.5(ii). -/
theorem rawPrimePowerCoefficient_energy_le
    {S D : Finset ℕ} {k : ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    ∑ n ∈ D, ‖rawPrimePowerCoefficient S k n‖ ^ (2 : ℕ) ≤
      (k.factorial : ℝ) * (S.card : ℝ) ^ k := by
  classical
  let support := rawPrimePowerSupport S k
  have hrestrict :
      (∑ n ∈ D, ‖rawPrimePowerCoefficient S k n‖ ^ (2 : ℕ)) =
        ∑ n ∈ D ∩ support,
          ‖rawPrimePowerCoefficient S k n‖ ^ (2 : ℕ) := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro n hnD hnInter
    have hnNot : n ∉ support := by
      intro hnSupport
      exact hnInter (Finset.mem_inter.mpr ⟨hnD, hnSupport⟩)
    rw [rawPrimePowerCoefficient_eq_zero_of_not_mem hnNot]
    simp
  rw [hrestrict]
  calc
    (∑ n ∈ D ∩ support,
        ‖rawPrimePowerCoefficient S k n‖ ^ (2 : ℕ)) ≤
        ∑ n ∈ D ∩ support,
          (k.factorial : ℝ) * ‖rawPrimePowerCoefficient S k n‖ := by
      apply Finset.sum_le_sum
      intro n hn
      have hcoeff := norm_rawPrimePowerCoefficient_le_factorial
        (k := k) (n := n) hS
      have hnonneg := norm_nonneg (rawPrimePowerCoefficient S k n)
      nlinarith
    _ ≤ ∑ n ∈ support,
          (k.factorial : ℝ) * ‖rawPrimePowerCoefficient S k n‖ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      intro n hn hnot
      positivity
    _ = (k.factorial : ℝ) *
          ∑ n ∈ support, ‖rawPrimePowerCoefficient S k n‖ := by
      rw [Finset.mul_sum]
    _ = (k.factorial : ℝ) * (S.card : ℝ) ^ k := by
      rw [sum_norm_rawPrimePowerCoefficient]

/-- Every dyadic slice therefore has the averaged energy required in the
Deshouillers--Iwaniec majorant. -/
theorem rawPrimePowerCoefficient_dyadicAverage_le
    {S : Finset ℕ} {k : ℕ} {A : ℝ}
    (hS : ∀ p ∈ S, Nat.Prime p) (hA : 0 < A) :
    (1 / A) *
        ∑ n ∈ dyadicInterval A,
          ‖rawPrimePowerCoefficient S k n‖ ^ (2 : ℕ) ≤
      ((k.factorial : ℝ) * (S.card : ℝ) ^ k) / A := by
  calc
    (1 / A) *
        ∑ n ∈ dyadicInterval A,
          ‖rawPrimePowerCoefficient S k n‖ ^ (2 : ℕ) ≤
      (1 / A) * ((k.factorial : ℝ) * (S.card : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left
          (rawPrimePowerCoefficient_energy_le hS) (by positivity)
    _ = ((k.factorial : ℝ) * (S.card : ℝ) ^ k) / A := by
      field_simp

/-! ## Exact endpoint-compatible dyadic decomposition -/

/-- The unnormalised polynomial power is exactly the sum of its `k`
open--closed dyadic convolution slices. -/
theorem rawPrimePowerPolynomial_eq_sum_dyadicSlices
    (S : Finset ℕ) {P : ℝ} {k : ℕ}
    (hP : 0 < P) (hk : 1 ≤ k)
    (hS : ∀ n ∈ S, InDyadicRange P n) (s : ℂ) :
    dirichletPolynomial (fun _ ↦ 1) S s ^ k =
      ∑ j ∈ Finset.range k,
        dyadicDirichletPolynomial (rawPrimePowerCoefficient S k)
          ((2 : ℝ) ^ j * P ^ k) s := by
  let F : (Fin k → ℕ) → ℂ := fun f ↦
    TypeII.tupleCoefficient (fun _ ↦ 1) f *
      (TypeII.tupleProduct f : ℂ) ^ (-s)
  calc
    dirichletPolynomial (fun _ ↦ 1) S s ^ k =
        ∑ f ∈ TypeII.powerTuples S k, F f := by
      rw [TypeII.dirichletPolynomial_pow_eq_tupleSum]
      apply Finset.sum_congr rfl
      intro f hf
      simpa [F] using
        (TypeII.tupleDirichletTerm_eq (a := fun _ ↦ 1) f s)
    _ = ∑ j ∈ Finset.range k,
        ∑ f ∈ TypeII.openClosedDyadicTuplePiece S k (P ^ k) j,
          F f :=
      TypeII.sum_poweredOpenClosedDyadicTuplePieces hP hk hS F
    _ = ∑ j ∈ Finset.range k,
        dyadicDirichletPolynomial (rawPrimePowerCoefficient S k)
          ((2 : ℝ) ^ j * P ^ k) s := by
      apply Finset.sum_congr rfl
      intro j hj
      change
        (∑ f ∈ TypeII.openClosedDyadicTuplePiece S k (P ^ k) j,
          TypeII.tupleCoefficient (fun _ ↦ 1) f *
            (TypeII.tupleProduct f : ℂ) ^ (-s)) =
          dyadicDirichletPolynomial
            (TypeII.powerConvolutionCoefficient (fun _ ↦ 1) S k)
            ((2 : ℝ) ^ j * P ^ k) s
      exact (TypeII.dyadicConvolutionPolynomial_eq_openClosedTuplePiece
        (fun _ ↦ 1) S k j (pow_nonneg hP.le k) s).symm

/-- Pointwise triangle inequality for the exact dyadic decomposition. -/
theorem norm_rawPrimePowerPolynomial_le_sum_dyadicSlices
    (S : Finset ℕ) {P : ℝ} {k : ℕ}
    (hP : 0 < P) (hk : 1 ≤ k)
    (hS : ∀ n ∈ S, InDyadicRange P n) (s : ℂ) :
    ‖dirichletPolynomial (fun _ ↦ 1) S s ^ k‖ ≤
      ∑ j ∈ Finset.range k,
        ‖dyadicDirichletPolynomial (rawPrimePowerCoefficient S k)
          ((2 : ℝ) ^ j * P ^ k) s‖ := by
  rw [rawPrimePowerPolynomial_eq_sum_dyadicSlices S hP hk hS s]
  exact norm_sum_le _ _

/-- Exact pointwise insertion obtained from the large-prime-polynomial
condition.  Crucially, this theorem keeps the **sum of all dyadic slices**:
the triangle inequality does not supply one slice that works uniformly for
every height.  This is the quantifier-correct replacement for an informal
"choose a dyadic piece" step. -/
theorem typeI_primePower_dyadicSum_insertion
    {P epsilon : ℝ} {k : ℕ} (hP : 0 < P) (hk : 1 ≤ k)
    (t : ℝ)
    (hlarge : P ^ (-epsilon / 10) ≤
      ‖primeDirichletPolynomial P (onePlusIT t)‖) :
    1 ≤ ((P ^ (-epsilon / 10)) ^ k)⁻¹ *
      ∑ j ∈ Finset.range k,
        ‖dyadicDirichletPolynomial
          (rawPrimePowerCoefficient (dyadicPrimes P) k)
          ((2 : ℝ) ^ j * P ^ k) (onePlusIT t)‖ := by
  have hthresholdPos : 0 < P ^ (-epsilon / 10) :=
    Real.rpow_pos_of_pos hP _
  have hthresholdPowPos : 0 < (P ^ (-epsilon / 10)) ^ k :=
    pow_pos hthresholdPos k
  have hpower :
      (P ^ (-epsilon / 10)) ^ k ≤
        ‖primeDirichletPolynomial P (onePlusIT t) ^ k‖ := by
    rw [norm_pow]
    exact pow_le_pow_left₀ hthresholdPos.le hlarge k
  have hsupport : ∀ n ∈ dyadicPrimes P, InDyadicRange P n := by
    intro n hn
    exact (mem_dyadicInterval hP.le).mp (Finset.mem_filter.mp hn).1
  have hdecompose :
      ‖primeDirichletPolynomial P (onePlusIT t) ^ k‖ ≤
        ∑ j ∈ Finset.range k,
          ‖dyadicDirichletPolynomial
            (rawPrimePowerCoefficient (dyadicPrimes P) k)
            ((2 : ℝ) ^ j * P ^ k) (onePlusIT t)‖ := by
    simpa [primeDirichletPolynomial] using
      (norm_rawPrimePowerPolynomial_le_sum_dyadicSlices
        (dyadicPrimes P) hP hk hsupport (onePlusIT t))
  calc
    (1 : ℝ) = ((P ^ (-epsilon / 10)) ^ k)⁻¹ *
        (P ^ (-epsilon / 10)) ^ k := by
      exact (inv_mul_cancel₀ hthresholdPowPos.ne').symm
    _ ≤ ((P ^ (-epsilon / 10)) ^ k)⁻¹ *
        ‖primeDirichletPolynomial P (onePlusIT t) ^ k‖ :=
      mul_le_mul_of_nonneg_left hpower (inv_nonneg.mpr hthresholdPowPos.le)
    _ ≤ ((P ^ (-epsilon / 10)) ^ k)⁻¹ *
        ∑ j ∈ Finset.range k,
          ‖dyadicDirichletPolynomial
            (rawPrimePowerCoefficient (dyadicPrimes P) k)
            ((2 : ℝ) ^ j * P ^ k) (onePlusIT t)‖ :=
      mul_le_mul_of_nonneg_left hdecompose
        (inv_nonneg.mpr hthresholdPowPos.le)

def typeIPrimePowerEnergyModule : ProofModule :=
  { name := "Completion.TypeIPrimePowerEnergy"
    paperLocation := "MT23 Section 5.1, equation (5.4)"
    purpose :=
      "Prove the sharp finite k!*|S|^k coefficient-energy bound for every dyadic slice of the raw inserted prime-polynomial power."
    dependsOn :=
      [ "Sparse.PrimePowerPolynomial",
        "TypeII.OpenClosedDyadicSlices" ]
    status := .proved }

end

end Completion
end ExactSemiprimes
