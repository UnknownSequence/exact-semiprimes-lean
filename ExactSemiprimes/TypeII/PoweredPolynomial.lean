import ExactSemiprimes.TypeII.PolynomialLengthRanges

/-!
# Finite powers of a Dirichlet polynomial

This file contains only the finite algebra and combinatorics used when the
shorter Type-II polynomial is replaced by a fixed power.  It does **not**
invoke the hybrid large-values estimate.

For a finite support `S` and an exponent `ℓ`, `powerTuples S ℓ` is the set of
ordered `ℓ`-tuples with entries in `S`.  We expand a polynomial power over
these tuples, collect tuples with the same product into the convolution
coefficient `powerConvolutionCoefficient`, and prove both its support and an
elementary coefficient bound.

The last section gives a literal dyadic splitting.  We use half-open pieces
`[2^j L, 2^(j+1)L)`.  Products of `ℓ` integers in `(M,2M]` occupy at most
`ℓ+1` such pieces (the extra endpoint piece handles the possible product
`(2M)^ℓ`).  The triangle inequality then shows that one piece carries at
least a `1/(ℓ+1)` fraction of the norm of the whole tuple sum.
-/

namespace ExactSemiprimes
namespace TypeII

open scoped BigOperators

noncomputable section

/-! ## Tuple expansion and convolution coefficients -/

/-- Ordered `ℓ`-tuples whose entries lie in the finite support `S`. -/
def powerTuples (S : Finset ℕ) (ℓ : ℕ) : Finset (Fin ℓ → ℕ) :=
  Fintype.piFinset fun _ : Fin ℓ ↦ S

@[simp]
theorem mem_powerTuples_iff {S : Finset ℕ} {ℓ : ℕ} {f : Fin ℓ → ℕ} :
    f ∈ powerTuples S ℓ ↔ ∀ i, f i ∈ S := by
  simp [powerTuples]

@[simp]
theorem card_powerTuples (S : Finset ℕ) (ℓ : ℕ) :
    (powerTuples S ℓ).card = S.card ^ ℓ := by
  simp [powerTuples]

/-- The integer represented by a tuple of factors. -/
def tupleProduct {ℓ : ℕ} (f : Fin ℓ → ℕ) : ℕ :=
  ∏ i, f i

/-- The product of the coefficients attached to a tuple. -/
def tupleCoefficient {ℓ : ℕ} (a : ℕ → ℂ) (f : Fin ℓ → ℕ) : ℂ :=
  ∏ i, a (f i)

/-- The coefficient of `n` in the `ℓ`-fold finite convolution of `a|S`. -/
def powerConvolutionCoefficient (a : ℕ → ℂ) (S : Finset ℕ)
    (ℓ n : ℕ) : ℂ :=
  ∑ f ∈ powerTuples S ℓ with tupleProduct f = n, tupleCoefficient a f

/-- A completely finite polynomial power expands as a sum over ordered
tuples.  Taking `z n = n⁻ˢ` gives the corresponding Dirichlet-polynomial
identity without requiring any infinite-series argument. -/
theorem finitePolynomial_pow_eq_tupleSum (a z : ℕ → ℂ)
    (S : Finset ℕ) (ℓ : ℕ) :
    (∑ n ∈ S, a n * z n) ^ ℓ =
      ∑ f ∈ powerTuples S ℓ, ∏ i, (a (f i) * z (f i)) := by
  simpa [powerTuples] using
    (Finset.sum_pow' S (fun n ↦ a n * z n) ℓ)

/-- Specialization of the preceding finite identity to the project's
Dirichlet-polynomial convention. -/
theorem dirichletPolynomial_pow_eq_tupleSum (a : ℕ → ℂ)
    (S : Finset ℕ) (s : ℂ) (ℓ : ℕ) :
    dirichletPolynomial a S s ^ ℓ =
      ∑ f ∈ powerTuples S ℓ,
        ∏ i, (a (f i) * (f i : ℂ) ^ (-s)) := by
  exact finitePolynomial_pow_eq_tupleSum a (fun n ↦ (n : ℂ) ^ (-s)) S ℓ

/-! ## Support and coefficient bounds -/

/-- A tuple drawn from `(M,2M]` has product in
`[M^ℓ,(2M)^ℓ]`. -/
theorem tupleProduct_mem_poweredSupport {S : Finset ℕ} {M : ℝ}
    {ℓ : ℕ} {f : Fin ℓ → ℕ} (hM : 0 ≤ M)
    (hf : f ∈ powerTuples S ℓ)
    (hS : ∀ n ∈ S, InDyadicRange M n) :
    M ^ ℓ ≤ (tupleProduct f : ℝ) ∧
      (tupleProduct f : ℝ) ≤ (2 * M) ^ ℓ := by
  have hfactor : ∀ i : Fin ℓ,
      M ≤ (f i : ℝ) ∧ (f i : ℝ) ≤ 2 * M := by
    intro i
    have hi := hS (f i) ((mem_powerTuples_iff.mp hf) i)
    exact ⟨hi.1.le, hi.2⟩
  constructor
  · simpa [tupleProduct, Nat.cast_prod] using
      (Finset.prod_le_prod₀
        (fun _ (_ : _ ∈ (Finset.univ : Finset (Fin ℓ))) ↦ hM)
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin ℓ))) ↦ (hfactor i).1))
  · simpa [tupleProduct, Nat.cast_prod] using
      (Finset.prod_le_prod₀
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin ℓ))) ↦
          Nat.cast_nonneg (f i))
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin ℓ))) ↦ (hfactor i).2))

/-- Outside the powered dyadic support the convolution coefficient vanishes. -/
theorem powerConvolutionCoefficient_eq_zero_of_outside {a : ℕ → ℂ}
    {S : Finset ℕ} {M : ℝ} {ℓ n : ℕ} (hM : 0 ≤ M)
    (hS : ∀ m ∈ S, InDyadicRange M m)
    (hout : (n : ℝ) < M ^ ℓ ∨ (2 * M) ^ ℓ < (n : ℝ)) :
    powerConvolutionCoefficient a S ℓ n = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro f hf
  simp only [Finset.mem_filter] at hf
  have hsupp := tupleProduct_mem_poweredSupport hM hf.1 hS
  have hcast : (tupleProduct f : ℝ) = n := by
    exact_mod_cast hf.2
  rcases hout with hout | hout
  · exact (not_lt_of_ge hsupp.1) (hcast ▸ hout) |>.elim
  · exact (not_lt_of_ge hsupp.2) (hcast.symm ▸ hout) |>.elim

/-- If every input coefficient has norm at most `A`, every tuple coefficient
has norm at most `A^ℓ`. -/
theorem norm_tupleCoefficient_le {a : ℕ → ℂ} {S : Finset ℕ}
    {ℓ : ℕ} {f : Fin ℓ → ℕ} {A : ℝ} (hf : f ∈ powerTuples S ℓ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ A) :
    ‖tupleCoefficient a f‖ ≤ A ^ ℓ := by
  rw [tupleCoefficient, norm_prod]
  simpa using
    (Finset.prod_le_prod₀
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin ℓ))) ↦ norm_nonneg (a (f i)))
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin ℓ))) ↦
        ha (f i) ((mem_powerTuples_iff.mp hf) i)))

/-- Elementary convolution bound: at most `|S|^ℓ` tuples contribute, and
each has norm at most `A^ℓ`. -/
theorem norm_powerConvolutionCoefficient_le {a : ℕ → ℂ}
    {S : Finset ℕ} {ℓ n : ℕ} {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ m ∈ S, ‖a m‖ ≤ A) :
    ‖powerConvolutionCoefficient a S ℓ n‖ ≤
      (S.card : ℝ) ^ ℓ * A ^ ℓ := by
  classical
  let fiber := (powerTuples S ℓ).filter fun f ↦ tupleProduct f = n
  calc
    ‖powerConvolutionCoefficient a S ℓ n‖ =
        ‖∑ f ∈ fiber, tupleCoefficient a f‖ := by
          rfl
    _ ≤ ∑ f ∈ fiber, ‖tupleCoefficient a f‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ fiber, A ^ ℓ := by
      apply Finset.sum_le_sum
      intro f hf
      exact norm_tupleCoefficient_le ((Finset.filter_subset _ _) hf) ha
    _ = (fiber.card : ℝ) * A ^ ℓ := by simp
    _ ≤ ((powerTuples S ℓ).card : ℝ) * A ^ ℓ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hA _)
      exact_mod_cast Finset.card_filter_le (powerTuples S ℓ) (fun f ↦ tupleProduct f = n)
    _ = (S.card : ℝ) ^ ℓ * A ^ ℓ := by
      rw [card_powerTuples]
      norm_cast

/-- A tuple with positive product `n` is determined by its first `k`
entries: the last entry is forced by the product.  Since every entry divides
`n`, this bounds the fibre of the product map on `(k+1)`-tuples by
`d(n)^k`. -/
theorem card_powerConvolutionFiber_le_divisorCount_pow
    {S : Finset ℕ} {k n : ℕ} (hn : 0 < n) :
    ((powerTuples S (k + 1)).filter fun f ↦ tupleProduct f = n).card ≤
      divisorCount n ^ k := by
  classical
  let fiber :=
    (powerTuples S (k + 1)).filter fun f ↦ tupleProduct f = n
  let prefixes : Finset (Fin k → ℕ) :=
    Fintype.piFinset fun _ : Fin k ↦ n.divisors
  calc
    fiber.card ≤ prefixes.card := by
      apply Finset.card_le_card_of_injOn
        (fun f i ↦ f i.castSucc)
      · intro f hf
        have hfprod : tupleProduct f = n :=
          (Finset.mem_filter.mp hf).2
        rw [Finset.mem_coe]
        simp only [prefixes, Fintype.mem_piFinset]
        intro i
        rw [Nat.mem_divisors]
        refine ⟨?_, hn.ne'⟩
        rw [← hfprod]
        exact Finset.dvd_prod_of_mem f (Finset.mem_univ i.castSucc)
      · intro f hf g hg hprefix
        have hfprod : tupleProduct f = n :=
          (Finset.mem_filter.mp hf).2
        have hgprod : tupleProduct g = n :=
          (Finset.mem_filter.mp hg).2
        apply funext
        intro i
        refine Fin.lastCases ?_ (fun j ↦ congrFun hprefix j) i
        have hprefix_ne : (∏ j : Fin k, f j.castSucc) ≠ 0 := by
          apply Finset.prod_ne_zero_iff.mpr
          intro j _hj
          apply ne_zero_of_dvd_ne_zero hn.ne'
          rw [← hfprod, tupleProduct]
          exact Finset.dvd_prod_of_mem f (Finset.mem_univ j.castSucc)
        apply mul_left_cancel₀ hprefix_ne
        calc
          (∏ j : Fin k, f j.castSucc) * f (Fin.last k) =
              tupleProduct f := by
                rw [tupleProduct, Fin.prod_univ_castSucc]
          _ = n := hfprod
          _ = tupleProduct g := hgprod.symm
          _ = (∏ j : Fin k, f j.castSucc) * g (Fin.last k) := by
            rw [tupleProduct, Fin.prod_univ_castSucc]
            congr 1
            exact Finset.prod_congr rfl fun j _hj ↦
              (congrFun hprefix j).symm
    _ = divisorCount n ^ k := by
      simp [prefixes, divisorCount]

/-- On a tuple whose positive product is `n`, a divisor-bounded input
sequence contributes at most `(A₀ d(n)^B)^ℓ`. -/
theorem norm_tupleCoefficient_le_divisorCount
    {a : ℕ → ℂ} {B A₀ : ℝ} {ℓ n : ℕ} {f : Fin ℓ → ℕ}
    (hn : 0 < n) (hfprod : tupleProduct f = n)
    (ha : IsDivisorBoundedByConstant B A₀ a) :
    ‖tupleCoefficient a f‖ ≤
      (A₀ * (divisorCount n : ℝ) ^ B) ^ ℓ := by
  rw [tupleCoefficient, norm_prod]
  calc
    (∏ i : Fin ℓ, ‖a (f i)‖) ≤
        ∏ _i : Fin ℓ, (A₀ * (divisorCount n : ℝ) ^ B) :=
      Finset.prod_le_prod₀
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin ℓ))) ↦
        norm_nonneg (a (f i)))
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin ℓ))) ↦ by
        have hdiv : f i ∣ n := by
          rw [← hfprod, tupleProduct]
          exact Finset.dvd_prod_of_mem f (Finset.mem_univ i)
        have hfi : 0 < f i :=
          Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hn.ne' hdiv)
        have hcard : divisorCount (f i) ≤ divisorCount n := by
          unfold divisorCount
          exact Finset.card_le_card
            (Nat.divisors_subset_of_dvd hn.ne' hdiv)
        calc
          ‖a (f i)‖ ≤
              A₀ * (divisorCount (f i) : ℝ) ^ B :=
            ha.2.2 (f i) hfi
          _ ≤ A₀ * (divisorCount n : ℝ) ^ B := by
            apply mul_le_mul_of_nonneg_left _ ha.2.1.le
            apply Real.rpow_le_rpow (Nat.cast_nonneg _)
              (by exact_mod_cast hcard) ha.1)
    _ = (A₀ * (divisorCount n : ℝ) ^ B) ^ ℓ := by simp

/-- The repaired coefficient propagation for an `(k+1)`-fold convolution.
The exponent `B(k+1)+k` combines the divisor loss in each coefficient with
the `d(n)^k` choices for a product fibre. -/
theorem norm_powerConvolutionCoefficient_le_divisorCount_succ
    {a : ℕ → ℂ} {S : Finset ℕ} {B A₀ : ℝ} {k n : ℕ}
    (hn : 0 < n) (ha : IsDivisorBoundedByConstant B A₀ a) :
    ‖powerConvolutionCoefficient a S (k + 1) n‖ ≤
      A₀ ^ (k + 1) *
        (divisorCount n : ℝ) ^ (B * (k + 1 : ℕ) + k) := by
  classical
  let fiber :=
    (powerTuples S (k + 1)).filter fun f ↦ tupleProduct f = n
  have hfiber : fiber.card ≤ divisorCount n ^ k := by
    exact card_powerConvolutionFiber_le_divisorCount_pow hn
  have hdposNat : 0 < divisorCount n := by
    apply Finset.card_pos.mpr
    exact ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩
  have hdpos : 0 < (divisorCount n : ℝ) :=
    Nat.cast_pos.mpr hdposNat
  calc
    ‖powerConvolutionCoefficient a S (k + 1) n‖ =
        ‖∑ f ∈ fiber, tupleCoefficient a f‖ := by
          rfl
    _ ≤ ∑ f ∈ fiber, ‖tupleCoefficient a f‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ fiber,
          (A₀ * (divisorCount n : ℝ) ^ B) ^ (k + 1) := by
      apply Finset.sum_le_sum
      intro f hf
      exact norm_tupleCoefficient_le_divisorCount hn
        (Finset.mem_filter.mp hf).2 ha
    _ = (fiber.card : ℝ) *
          (A₀ * (divisorCount n : ℝ) ^ B) ^ (k + 1) := by
      simp
    _ ≤ (divisorCount n : ℝ) ^ k *
          (A₀ * (divisorCount n : ℝ) ^ B) ^ (k + 1) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hfiber
      · exact pow_nonneg
          (mul_nonneg ha.2.1.le (Real.rpow_nonneg hdpos.le B)) _
    _ = A₀ ^ (k + 1) *
          (divisorCount n : ℝ) ^ (B * (k + 1 : ℕ) + k) := by
      rw [mul_pow]
      calc
        (divisorCount n : ℝ) ^ k *
              (A₀ ^ (k + 1) *
                ((divisorCount n : ℝ) ^ B) ^ (k + 1)) =
            A₀ ^ (k + 1) *
              (((divisorCount n : ℝ) ^ B) ^ (k + 1) *
                (divisorCount n : ℝ) ^ k) := by ring
        _ = A₀ ^ (k + 1) *
              ((divisorCount n : ℝ) ^ (B * (k + 1 : ℕ)) *
                (divisorCount n : ℝ) ^ (k : ℝ)) := by
          rw [← Real.rpow_natCast
              ((divisorCount n : ℝ) ^ B) (k + 1),
            ← Real.rpow_mul hdpos.le,
            ← Real.rpow_natCast (divisorCount n : ℝ) k]
        _ = A₀ ^ (k + 1) *
              (divisorCount n : ℝ) ^ (B * (k + 1 : ℕ) + k) := by
          rw [← Real.rpow_add hdpos]

/-- For every positive convolution order `ℓ`, the propagated coefficient
bound has the repaired exponent `Bℓ + ℓ - 1`. -/
theorem norm_powerConvolutionCoefficient_le_divisorCount
    {a : ℕ → ℂ} {S : Finset ℕ} {B A₀ : ℝ} {ℓ n : ℕ}
    (hℓ : 1 ≤ ℓ) (hn : 0 < n)
    (ha : IsDivisorBoundedByConstant B A₀ a) :
    ‖powerConvolutionCoefficient a S ℓ n‖ ≤
      A₀ ^ ℓ *
        (divisorCount n : ℝ) ^ (B * ℓ + ℓ - 1) := by
  cases ℓ with
  | zero => omega
  | succ k =>
      simpa [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
        sub_eq_add_neg, add_assoc] using
        (norm_powerConvolutionCoefficient_le_divisorCount_succ
          (S := S) (k := k) hn ha)

/-- The propagated pointwise estimate is itself a globally quantified
divisor-bound hypothesis of the exact form accepted by the hybrid density
theorem.  This packages the repaired exponent `Bℓ+ℓ-1` and constant `A₀^ℓ`
without adding an analytic assumption. -/
theorem powerConvolutionCoefficient_isDivisorBoundedByConstant
    {a : ℕ → ℂ} {S : Finset ℕ} {B A₀ : ℝ} {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (ha : IsDivisorBoundedByConstant B A₀ a) :
    IsDivisorBoundedByConstant (B * ℓ + ℓ - 1) (A₀ ^ ℓ)
      (powerConvolutionCoefficient a S ℓ) := by
  refine ⟨?_, ?_, ?_⟩
  · have hℓcast : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
    nlinarith [ha.1]
  · exact pow_pos ha.2.1 ℓ
  · intro n hn
    exact norm_powerConvolutionCoefficient_le_divisorCount hℓ hn ha

/-! ## A finite dyadic splitting -/

/-- The tuples whose integer product lies in the half-open dyadic interval
`[2^j L,2^(j+1)L)`. -/
def dyadicTuplePiece (S : Finset ℕ) (ℓ : ℕ) (L : ℝ) (j : ℕ) :
    Finset (Fin ℓ → ℕ) :=
  (powerTuples S ℓ).filter fun f ↦
    (2 : ℝ) ^ j * L ≤ (tupleProduct f : ℝ) ∧
      (tupleProduct f : ℝ) < (2 : ℝ) ^ (j + 1) * L

@[simp]
theorem mem_dyadicTuplePiece_iff {S : Finset ℕ} {ℓ : ℕ}
    {L : ℝ} {j : ℕ} {f : Fin ℓ → ℕ} :
    f ∈ dyadicTuplePiece S ℓ L j ↔
      f ∈ powerTuples S ℓ ∧
      (2 : ℝ) ^ j * L ≤ (tupleProduct f : ℝ) ∧
      (tupleProduct f : ℝ) < (2 : ℝ) ^ (j + 1) * L := by
  simp [dyadicTuplePiece]

/-- Every positive number between `L` and `2^r L` belongs to one of the
first `r` half-open dyadic pieces. -/
theorem exists_dyadicIndex {L x : ℝ} {r : ℕ} (hL : 0 < L)
    (hlower : L ≤ x) (hupper : x < (2 : ℝ) ^ r * L) :
    ∃ j < r, (2 : ℝ) ^ j * L ≤ x ∧
      x < (2 : ℝ) ^ (j + 1) * L := by
  have hx : 1 ≤ x / L := (le_div_iff₀ hL).2 (by simpa using hlower)
  obtain ⟨j, hjlower, hjupper⟩ :=
    exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2)
  have hjlower' : (2 : ℝ) ^ j * L ≤ x := by
    exact (le_div_iff₀ hL).1 hjlower
  have hjupper' : x < (2 : ℝ) ^ (j + 1) * L := by
    exact (div_lt_iff₀ hL).1 hjupper
  have hjr : j < r := by
    have hpowers : (2 : ℝ) ^ j < (2 : ℝ) ^ r := by
      exact lt_of_mul_lt_mul_right (hjlower'.trans_lt hupper) hL.le
    exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hpowers
  exact ⟨j, hjr, hjlower', hjupper'⟩

/-- Distinct half-open dyadic tuple pieces are disjoint. -/
theorem dyadicTuplePiece_pairwiseDisjoint (S : Finset ℕ) (ℓ : ℕ)
    {L : ℝ} (hL : 0 < L) :
    (Set.univ : Set ℕ).PairwiseDisjoint (dyadicTuplePiece S ℓ L) := by
  intro i _ j _ hij
  change Disjoint (dyadicTuplePiece S ℓ L i) (dyadicTuplePiece S ℓ L j)
  rw [Finset.disjoint_left]
  intro f hfi hfj
  have hi := (mem_dyadicTuplePiece_iff.mp hfi).2
  have hj := (mem_dyadicTuplePiece_iff.mp hfj).2
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hp : (2 : ℝ) ^ (i + 1) ≤ (2 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hscaled : (2 : ℝ) ^ (i + 1) * L ≤ (2 : ℝ) ^ j * L :=
      mul_le_mul_of_nonneg_right hp hL.le
    exact (not_lt_of_ge (hscaled.trans hj.1)) hi.2
  · have hp : (2 : ℝ) ^ (j + 1) ≤ (2 : ℝ) ^ i :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hscaled : (2 : ℝ) ^ (j + 1) * L ≤ (2 : ℝ) ^ i * L :=
      mul_le_mul_of_nonneg_right hp hL.le
    exact (not_lt_of_ge (hscaled.trans hi.1)) hj.2

/-- If all tuple products lie in `[L,2^r L)`, the first `r` dyadic pieces
are a disjoint cover of the tuple set. -/
theorem biUnion_dyadicTuplePiece_eq {S : Finset ℕ} {ℓ r : ℕ}
    {L : ℝ} (hL : 0 < L)
    (hbounds : ∀ f ∈ powerTuples S ℓ,
      L ≤ (tupleProduct f : ℝ) ∧
        (tupleProduct f : ℝ) < (2 : ℝ) ^ r * L) :
    (Finset.range r).biUnion (dyadicTuplePiece S ℓ L) =
      powerTuples S ℓ := by
  ext f
  constructor
  · simp only [Finset.mem_biUnion, Finset.mem_range]
    rintro ⟨j, _, hj⟩
    exact (mem_dyadicTuplePiece_iff.mp hj).1
  · intro hf
    obtain ⟨j, hjr, hj⟩ :=
      exists_dyadicIndex hL (hbounds f hf).1 (hbounds f hf).2
    simp only [Finset.mem_biUnion, Finset.mem_range]
    exact ⟨j, hjr, mem_dyadicTuplePiece_iff.mpr ⟨hf, hj⟩⟩

/-- The tuple sum is the sum of its dyadic pieces. -/
theorem sum_dyadicTuplePieces {S : Finset ℕ} {ℓ r : ℕ}
    {L : ℝ} (hL : 0 < L)
    (hbounds : ∀ f ∈ powerTuples S ℓ,
      L ≤ (tupleProduct f : ℝ) ∧
        (tupleProduct f : ℝ) < (2 : ℝ) ^ r * L)
    (F : (Fin ℓ → ℕ) → ℂ) :
    ∑ f ∈ powerTuples S ℓ, F f =
      ∑ j ∈ Finset.range r, ∑ f ∈ dyadicTuplePiece S ℓ L j, F f := by
  rw [← biUnion_dyadicTuplePiece_eq hL hbounds]
  apply Finset.sum_biUnion
  intro i _ j _ hij
  exact dyadicTuplePiece_pairwiseDisjoint S ℓ hL (Set.mem_univ i)
    (Set.mem_univ j) hij

/-- Products of `ℓ` factors from `(M,2M]` lie in the first `ℓ+1` dyadic
pieces starting at `M^ℓ`. -/
theorem poweredDyadicTupleBounds {S : Finset ℕ} {M : ℝ} {ℓ : ℕ}
    (hM : 0 < M) (hS : ∀ n ∈ S, InDyadicRange M n) :
    ∀ f ∈ powerTuples S ℓ,
      M ^ ℓ ≤ (tupleProduct f : ℝ) ∧
        (tupleProduct f : ℝ) < (2 : ℝ) ^ (ℓ + 1) * M ^ ℓ := by
  intro f hf
  have hsupp := tupleProduct_mem_poweredSupport hM.le hf hS
  refine ⟨hsupp.1, hsupp.2.trans_lt ?_⟩
  rw [mul_pow]
  have hpow : 0 < M ^ ℓ := pow_pos hM _
  have htwo : (2 : ℝ) ^ ℓ < (2 : ℝ) ^ (ℓ + 1) :=
    pow_lt_pow_right₀ (by norm_num) (by omega)
  exact mul_lt_mul_of_pos_right htwo hpow

/-- Concrete dyadic decomposition for the powered polynomial. -/
theorem sum_poweredDyadicTuplePieces {S : Finset ℕ} {M : ℝ} {ℓ : ℕ}
    (hM : 0 < M) (hS : ∀ n ∈ S, InDyadicRange M n)
    (F : (Fin ℓ → ℕ) → ℂ) :
    ∑ f ∈ powerTuples S ℓ, F f =
      ∑ j ∈ Finset.range (ℓ + 1),
        ∑ f ∈ dyadicTuplePiece S ℓ (M ^ ℓ) j, F f := by
  exact sum_dyadicTuplePieces (pow_pos hM _) (poweredDyadicTupleBounds hM hS) F

/-- A large whole tuple sum forces a large dyadic piece.  This is the exact
finite pigeonhole loss: one of the at most `ℓ+1` pieces carries at least
`1/(ℓ+1)` of the norm of the whole sum. -/
theorem exists_large_poweredDyadicTuplePiece {S : Finset ℕ}
    {M : ℝ} {ℓ : ℕ} (hM : 0 < M)
    (hS : ∀ n ∈ S, InDyadicRange M n)
    (F : (Fin ℓ → ℕ) → ℂ) :
    ∃ j < ℓ + 1,
      ‖∑ f ∈ powerTuples S ℓ, F f‖ / (ℓ + 1 : ℝ) ≤
        ‖∑ f ∈ dyadicTuplePiece S ℓ (M ^ ℓ) j, F f‖ := by
  let total : ℂ := ∑ f ∈ powerTuples S ℓ, F f
  let piece : ℕ → ℂ := fun j ↦
    ∑ f ∈ dyadicTuplePiece S ℓ (M ^ ℓ) j, F f
  have hdecomp : total = ∑ j ∈ Finset.range (ℓ + 1), piece j := by
    exact sum_poweredDyadicTuplePieces hM hS F
  have hnorm : ‖total‖ ≤
      ∑ j ∈ Finset.range (ℓ + 1), ‖piece j‖ := by
    rw [hdecomp]
    exact norm_sum_le _ _
  have haverage :
      ∑ _j ∈ Finset.range (ℓ + 1), ‖total‖ / (ℓ + 1 : ℝ) ≤
        ∑ j ∈ Finset.range (ℓ + 1), ‖piece j‖ := by
    calc
      ∑ _j ∈ Finset.range (ℓ + 1), ‖total‖ / (ℓ + 1 : ℝ) =
          ‖total‖ := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            field_simp
            push_cast
            ring
      _ ≤ ∑ j ∈ Finset.range (ℓ + 1), ‖piece j‖ := hnorm
  obtain ⟨j, hj, hjlarge⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr (by omega : ℓ + 1 ≠ 0)) haverage
  exact ⟨j, Finset.mem_range.mp hj, hjlarge⟩

def poweredPolynomialModule : ProofModule :=
  { name := "TypeII.PoweredPolynomial"
    paperLocation := "Proof of Proposition 5.1, case τ₁ ≤ τ₂"
    purpose :=
      "Expand finite powers, bound convolution coefficients and support, split into dyadic pieces, and retain a large piece."
    dependsOn :=
      ["TypeII.PolynomialLengthRanges", "Mathlib finite sums, products, and norm inequalities"]
    status := .proved }

end

end TypeII
end ExactSemiprimes
