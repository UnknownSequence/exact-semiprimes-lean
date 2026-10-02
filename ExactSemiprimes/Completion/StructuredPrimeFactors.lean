import ExactSemiprimes.TypeII.FullTypeIIEstimate
import ExactSemiprimes.Sparse.PrimePowerPolynomial
import ExactSemiprimes.Assumptions

/-! # Structured prime factors

The exact short and dyadic prime-polynomial factors attached to the
structured Type-II coefficient, together with every direct consequence of
Harman's literal dyadic Lemma 1.5.  No short-segment cancellation is claimed
here. -/

namespace ExactSemiprimes
namespace Completion

open scoped BigOperators

noncomputable section

/-- The prime polynomial on the short segment
`Q < p ≤ (1+delta)Q` occurring in the structured Type-II coefficient. -/
noncomputable def structuredShortPrimePolynomial
    (Q delta t : ℝ) : ℂ :=
  dirichletPolynomial (fun _ ↦ 1)
    ((natOpenClosedInterval Q ((1 + delta) * Q)).filter Nat.Prime)
    (onePlusIT t)

/-- The product representation of the structured Type-II factor after the
finite coefficient/fibre identity has been made. -/
noncomputable def structuredShortPrimeProduct
    {R : ℕ} (Q : Fin R → ℝ) (delta t : ℝ) : ℂ :=
  ∏ j, structuredShortPrimePolynomial (Q j) delta t

/-! ## Exact finite-fibre identity for the structured coefficient -/

/-- The prime set in one short structured factor. -/
def structuredPrimeSet (Q delta : ℝ) : Finset ℕ :=
  (natOpenClosedInterval Q ((1 + delta) * Q)).filter Nat.Prime

/-- All ordered tuples, with the `j`th entry in the `j`th short prime set. -/
def structuredPrimeTuples {R : ℕ} (Q : Fin R → ℝ) (delta : ℝ) :
    Finset (Fin R → ℕ) :=
  Fintype.piFinset fun j ↦ structuredPrimeSet (Q j) delta

def structuredPrimeTupleProduct {R : ℕ} (q : Fin R → ℕ) : ℕ :=
  ∏ j, q j

def structuredPrimeTupleFiber {R : ℕ} (Q : Fin R → ℝ)
    (delta : ℝ) (m : ℕ) : Finset (Fin R → ℕ) :=
  (structuredPrimeTuples Q delta).filter fun q ↦
    structuredPrimeTupleProduct q = m

/-- The bounded tuple fibre used literally in the source coefficient. -/
def boundedStructuredPrimeTupleFiber
    (delta : ℝ) (R : ℕ) (Q : Fin R → ℝ) (m : ℕ) :
    Finset (Fin R → Fin (m + 1)) :=
  (Finset.univ : Finset (Fin R → Fin (m + 1))).filter fun q ↦
    (∀ j : Fin R,
      (q j : ℕ).Prime ∧ Q j < (q j : ℝ) ∧
        (q j : ℝ) ≤ Q j * (1 + delta)) ∧
      (∏ j : Fin R, (q j : ℕ)) = m

theorem mem_structuredPrimeSet {Q delta : ℝ} {p : ℕ}
    (hQ : 0 ≤ Q) (hdelta : 0 ≤ delta) :
    p ∈ structuredPrimeSet Q delta ↔
      p.Prime ∧ Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + delta) := by
  rw [structuredPrimeSet, Finset.mem_filter,
    mem_natOpenClosedInterval hQ (mul_nonneg (by linarith) hQ)]
  constructor
  · rintro ⟨⟨hlow, hupp⟩, hp⟩
    exact ⟨hp, hlow, by simpa [mul_comm] using hupp⟩
  · rintro ⟨hp, hlow, hupp⟩
    exact ⟨⟨hlow, by simpa [mul_comm] using hupp⟩, hp⟩

theorem mem_structuredPrimeTuples
    {R : ℕ} {Q : Fin R → ℝ} {delta : ℝ} {q : Fin R → ℕ}
    (hQ : ∀ j, 0 ≤ Q j) (hdelta : 0 ≤ delta) :
    q ∈ structuredPrimeTuples Q delta ↔
      ∀ j, (q j).Prime ∧ Q j < (q j : ℝ) ∧
        (q j : ℝ) ≤ Q j * (1 + delta) := by
  rw [structuredPrimeTuples, Fintype.mem_piFinset]
  exact forall_congr' fun j ↦ mem_structuredPrimeSet (hQ j) hdelta

theorem mem_structuredPrimeTupleFiber
    {R : ℕ} {Q : Fin R → ℝ} {delta : ℝ} {m : ℕ}
    {q : Fin R → ℕ}
    (hQ : ∀ j, 0 ≤ Q j) (hdelta : 0 ≤ delta) :
    q ∈ structuredPrimeTupleFiber Q delta m ↔
      (∀ j, (q j).Prime ∧ Q j < (q j : ℝ) ∧
        (q j : ℝ) ≤ Q j * (1 + delta)) ∧
      (∏ j, q j) = m := by
  rw [structuredPrimeTupleFiber, Finset.mem_filter,
    mem_structuredPrimeTuples hQ hdelta]
  rfl

@[simp] theorem mem_boundedStructuredPrimeTupleFiber
    {delta : ℝ} {R : ℕ} {Q : Fin R → ℝ} {m : ℕ}
    {q : Fin R → Fin (m + 1)} :
    q ∈ boundedStructuredPrimeTupleFiber delta R Q m ↔
      (∀ j : Fin R,
        (q j : ℕ).Prime ∧ Q j < (q j : ℝ) ∧
          (q j : ℝ) ≤ Q j * (1 + delta)) ∧
        (∏ j : Fin R, (q j : ℕ)) = m := by
  simp [boundedStructuredPrimeTupleFiber]

/-- In a structured tuple, every entry is at most the tuple product. -/
theorem structuredPrimeTuple_entry_le_product
    {R : ℕ} {Q : Fin R → ℝ} {delta : ℝ} {q : Fin R → ℕ}
    (hQ : ∀ j, 0 ≤ Q j) (hdelta : 0 ≤ delta)
    (hq : q ∈ structuredPrimeTuples Q delta) (j : Fin R) :
    q j ≤ structuredPrimeTupleProduct q := by
  have hqdata := (mem_structuredPrimeTuples hQ hdelta).mp hq
  have hprodPos : 0 < structuredPrimeTupleProduct q := by
    rw [structuredPrimeTupleProduct]
    exact Finset.prod_pos fun i _ ↦ (hqdata i).1.pos
  apply Nat.le_of_dvd hprodPos
  exact Finset.dvd_prod_of_mem q (Finset.mem_univ j)

/-- The source's artificial `Fin (m+1)` search bound neither loses nor
duplicates a tuple: it has exactly the same cardinality as the intrinsic
short-prime tuple fibre. -/
theorem card_boundedStructuredPrimeTupleFiber_eq
    {delta : ℝ} {R : ℕ} {Q : Fin R → ℝ} {m : ℕ}
    (hQ : ∀ j, 0 ≤ Q j) (hdelta : 0 ≤ delta) :
    (boundedStructuredPrimeTupleFiber delta R Q m).card =
      (structuredPrimeTupleFiber Q delta m).card := by
  classical
  let forgetBound : (Fin R → Fin (m + 1)) → (Fin R → ℕ) :=
    fun q j ↦ q j
  apply Finset.card_bij (fun q _hq ↦ forgetBound q)
  · intro q hq
    have hdata := mem_boundedStructuredPrimeTupleFiber.mp hq
    apply (mem_structuredPrimeTupleFiber hQ hdelta).mpr
    simpa [forgetBound] using hdata
  · intro q₁ hq₁ q₂ hq₂ heq
    funext j
    apply Fin.ext
    exact congrFun heq j
  · intro q hq
    have hdata := (mem_structuredPrimeTupleFiber hQ hdelta).mp hq
    have htuple : q ∈ structuredPrimeTuples Q delta :=
      (mem_structuredPrimeTuples hQ hdelta).mpr hdata.1
    have hbound (j : Fin R) : q j < m + 1 := by
      have hle := structuredPrimeTuple_entry_le_product hQ hdelta htuple j
      rw [structuredPrimeTupleProduct, hdata.2] at hle
      omega
    let qb : Fin R → Fin (m + 1) := fun j ↦ ⟨q j, hbound j⟩
    refine ⟨qb, ?_, ?_⟩
    · apply mem_boundedStructuredPrimeTupleFiber.mpr
      simpa [qb] using hdata
    · funext j
      rfl

/-- The literal coefficient is the cardinality of the intrinsic tuple
fibre. -/
theorem structuredTypeIICoefficient_eq_tupleFiberCard
    {delta : ℝ} {R : ℕ} {Q : Fin R → ℝ} {m : ℕ}
    (hQ : ∀ j, 0 ≤ Q j) (hdelta : 0 ≤ delta) :
    matomakiTeravainenStructuredTypeIICoefficient delta R Q m =
      ((structuredPrimeTupleFiber Q delta m).card : ℂ) := by
  have hcard := card_boundedStructuredPrimeTupleFiber_eq
    (delta := delta) (R := R) (Q := Q) (m := m) hQ hdelta
  rw [matomakiTeravainenStructuredTypeIICoefficient]
  change ((boundedStructuredPrimeTupleFiber delta R Q m).card : ℂ) = _
  exact_mod_cast hcard

/-- Every short-prime tuple product belongs to the source's first Type-II
support interval. -/
theorem structuredPrimeTupleProduct_mem_firstSupport
    {delta M1 : ℝ} {R : ℕ} {Q : Fin R → ℝ} {q : Fin R → ℕ}
    (hdelta : 0 ≤ delta) (hR : 1 ≤ R)
    (hQ : ∀ j, 0 < Q j) (hprodQ : (∏ j, Q j) = M1)
    (hq : q ∈ structuredPrimeTuples Q delta) :
    structuredPrimeTupleProduct q ∈
      natOpenClosedInterval M1 ((1 + delta) ^ R * M1) := by
  have hQ0 : ∀ j, 0 ≤ Q j := fun j ↦ (hQ j).le
  have hqdata := (mem_structuredPrimeTuples hQ0 hdelta).mp hq
  have hM1 : 0 < M1 := by
    rw [← hprodQ]
    exact Finset.prod_pos fun j _ ↦ hQ j
  have hnonempty : (Finset.univ : Finset (Fin R)).Nonempty := by
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  have hlowerProduct :
      (∏ j, Q j) < ∏ j, (q j : ℝ) := by
    exact Finset.prod_lt_prod_of_nonempty₀
      (fun j _ ↦ hQ j) (fun j _ ↦ (hqdata j).2.1) hnonempty
  have hlower : M1 < (structuredPrimeTupleProduct q : ℝ) := by
    rw [← hprodQ]
    simpa [structuredPrimeTupleProduct, Nat.cast_prod] using hlowerProduct
  have hupperProduct :
      (∏ j, (q j : ℝ)) ≤ ∏ j, Q j * (1 + delta) := by
    exact Finset.prod_le_prod₀ (fun j _ ↦ Nat.cast_nonneg (q j))
      (fun j _ ↦ (hqdata j).2.2)
  have hupper :
      (structuredPrimeTupleProduct q : ℝ) ≤ (1 + delta) ^ R * M1 := by
    calc
      (structuredPrimeTupleProduct q : ℝ) = ∏ j, (q j : ℝ) := by
        simp [structuredPrimeTupleProduct, Nat.cast_prod]
      _ ≤ ∏ j, Q j * (1 + delta) := hupperProduct
      _ = (∏ j, Q j) * (∏ _j : Fin R, (1 + delta)) := by
        rw [Finset.prod_mul_distrib]
      _ = M1 * (1 + delta) ^ R := by simp [hprodQ]
      _ = (1 + delta) ^ R * M1 := by ring
  exact (mem_natOpenClosedInterval hM1.le
    (mul_nonneg (pow_nonneg (by linarith) R) hM1.le)).mpr
      ⟨hlower, hupper⟩

/-- Complex powers turn tuple products into products of the corresponding
complex powers. -/
theorem structuredPrimeTupleProduct_cpow
    {R : ℕ} (q : Fin R → ℕ) (s : ℂ) :
    (structuredPrimeTupleProduct q : ℂ) ^ s =
      ∏ j, (q j : ℂ) ^ s := by
  change Sparse.natCpowMonoidHom s (∏ j, q j) =
    ∏ j, Sparse.natCpowMonoidHom s (q j)
  exact map_prod (Sparse.natCpowMonoidHom s) q Finset.univ

/-- Expanding the product of the short prime polynomials gives the sum over
all structured prime tuples. -/
theorem structuredShortPrimeProduct_eq_tupleSum
    {R : ℕ} (Q : Fin R → ℝ) (delta t : ℝ) :
    structuredShortPrimeProduct Q delta t =
      ∑ q ∈ structuredPrimeTuples Q delta,
        (structuredPrimeTupleProduct q : ℂ) ^ (-onePlusIT t) := by
  classical
  rw [structuredShortPrimeProduct]
  simp only [structuredShortPrimePolynomial, dirichletPolynomial, one_mul]
  change
    (∏ j, ∑ p ∈ structuredPrimeSet (Q j) delta,
      (p : ℂ) ^ (-onePlusIT t)) = _
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro q hq
  exact (structuredPrimeTupleProduct_cpow q (-onePlusIT t)).symm

/-- Grouping the tuple expansion by its product gives the intrinsic fibre
cardinality as coefficient. -/
theorem structuredPrimeTupleSum_eq_fiberSum
    {delta M1 t : ℝ} {R : ℕ} {Q : Fin R → ℝ}
    (hdelta : 0 ≤ delta) (hR : 1 ≤ R)
    (hQ : ∀ j, 0 < Q j) (hprodQ : (∏ j, Q j) = M1) :
    (∑ q ∈ structuredPrimeTuples Q delta,
        (structuredPrimeTupleProduct q : ℂ) ^ (-onePlusIT t)) =
      ∑ m ∈ natOpenClosedInterval M1 ((1 + delta) ^ R * M1),
        ((structuredPrimeTupleFiber Q delta m).card : ℂ) *
          (m : ℂ) ^ (-onePlusIT t) := by
  classical
  let S : Finset ℕ :=
    natOpenClosedInterval M1 ((1 + delta) ^ R * M1)
  have hmaps : ∀ q ∈ structuredPrimeTuples Q delta,
      structuredPrimeTupleProduct q ∈ S := by
    intro q hq
    exact structuredPrimeTupleProduct_mem_firstSupport
      hdelta hR hQ hprodQ hq
  have hgroup := Finset.sum_fiberwise_of_maps_to hmaps
    (fun q : Fin R → ℕ ↦
      (structuredPrimeTupleProduct q : ℂ) ^ (-onePlusIT t))
  have hinter (m : ℕ) :
      (∑ q ∈ structuredPrimeTuples Q delta with
          structuredPrimeTupleProduct q = m,
          (structuredPrimeTupleProduct q : ℂ) ^ (-onePlusIT t)) =
        ((structuredPrimeTupleFiber Q delta m).card : ℂ) *
          (m : ℂ) ^ (-onePlusIT t) := by
    change
      (∑ q ∈ structuredPrimeTupleFiber Q delta m,
          (structuredPrimeTupleProduct q : ℂ) ^ (-onePlusIT t)) = _
    calc
      _ = ∑ _q ∈ structuredPrimeTupleFiber Q delta m,
          (m : ℂ) ^ (-onePlusIT t) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [(Finset.mem_filter.mp hq).2]
      _ = ((structuredPrimeTupleFiber Q delta m).card : ℂ) *
          (m : ℂ) ^ (-onePlusIT t) := by simp
  calc
    (∑ q ∈ structuredPrimeTuples Q delta,
        (structuredPrimeTupleProduct q : ℂ) ^ (-onePlusIT t)) =
      ∑ m ∈ S,
        ∑ q ∈ structuredPrimeTuples Q delta with
          structuredPrimeTupleProduct q = m,
          (structuredPrimeTupleProduct q : ℂ) ^ (-onePlusIT t) :=
        hgroup.symm
    _ = ∑ m ∈ S,
        ((structuredPrimeTupleFiber Q delta m).card : ℂ) *
          (m : ℂ) ^ (-onePlusIT t) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact hinter m
    _ = _ := rfl

/-- The complete finite-fibre identity: the Dirichlet polynomial of the
source's structured Type-II coefficient is exactly the product of its short
prime factors. -/
theorem structuredTypeIICoefficient_polynomial_eq_shortPrimeProduct
    {delta M1 t : ℝ} {R : ℕ} {Q : Fin R → ℝ}
    (hdelta : 0 ≤ delta) (hR : 1 ≤ R)
    (hQ : ∀ j, 0 < Q j) (hprodQ : (∏ j, Q j) = M1) :
    dirichletPolynomial
        (matomakiTeravainenStructuredTypeIICoefficient delta R Q)
        (natOpenClosedInterval M1 ((1 + delta) ^ R * M1))
        (onePlusIT t) =
      structuredShortPrimeProduct Q delta t := by
  have hQ0 : ∀ j, 0 ≤ Q j := fun j ↦ (hQ j).le
  calc
    dirichletPolynomial
        (matomakiTeravainenStructuredTypeIICoefficient delta R Q)
        (natOpenClosedInterval M1 ((1 + delta) ^ R * M1))
        (onePlusIT t) =
      ∑ m ∈ natOpenClosedInterval M1 ((1 + delta) ^ R * M1),
        ((structuredPrimeTupleFiber Q delta m).card : ℂ) *
          (m : ℂ) ^ (-onePlusIT t) := by
      unfold dirichletPolynomial
      apply Finset.sum_congr rfl
      intro m hm
      rw [structuredTypeIICoefficient_eq_tupleFiberCard hQ0 hdelta]
    _ = ∑ q ∈ structuredPrimeTuples Q delta,
        (structuredPrimeTupleProduct q : ℂ) ^ (-onePlusIT t) :=
      (structuredPrimeTupleSum_eq_fiberSum
        hdelta hR hQ hprodQ).symm
    _ = structuredShortPrimeProduct Q delta t :=
      (structuredShortPrimeProduct_eq_tupleSum Q delta t).symm

/-- The structured coefficient in MT23 (2.11) is bounded by `R!`.
This exposes the subpower normalization that was hidden by the phrase
"divisor bounded" in the paper-level argument. -/
theorem norm_structuredTypeIICoefficient_le_factorial
    (delta : ℝ) (R : ℕ) (Q : Fin R → ℝ) (m : ℕ) :
    ‖matomakiTeravainenStructuredTypeIICoefficient delta R Q m‖ ≤
      (R.factorial : ℝ) := by
  classical
  let tuples : Finset (Fin R → Fin (m + 1)) :=
    (Finset.univ : Finset (Fin R → Fin (m + 1))).filter fun q ↦
      (∀ j : Fin R,
        (q j : ℕ).Prime ∧ Q j < (q j : ℝ) ∧
          (q j : ℝ) ≤ Q j * (1 + delta)) ∧
        (∏ j : Fin R, (q j : ℕ)) = m
  let tupleList : (Fin R → Fin (m + 1)) → List ℕ :=
    fun q ↦ List.ofFn fun j ↦ (q j : ℕ)
  let lists : Finset (List ℕ) := tuples.image tupleList
  have htupleListInjective : Function.Injective tupleList := by
    intro q r hqr
    funext j
    apply Fin.ext
    exact congrFun (List.ofFn_injective hqr) j
  have hcard : tuples.card = lists.card := by
    symm
    exact Finset.card_image_of_injective _ htupleListInjective
  have hcardNat : tuples.card ≤ R.factorial := by
    by_cases htuples : tuples.Nonempty
    · obtain ⟨q₀, hq₀⟩ := htuples
      have hq₀data := (Finset.mem_filter.mp hq₀).2
      have hperm₀ : (tupleList q₀).Perm m.primeFactorsList := by
        apply Nat.primeFactorsList_unique
        · simpa [tupleList, List.prod_ofFn] using hq₀data.2
        · intro p hp
          simp only [tupleList, List.mem_ofFn] at hp
          obtain ⟨j, rfl⟩ := hp
          exact (hq₀data.1 j).1
      have hlength : m.primeFactorsList.length = R := by
        simpa [tupleList] using hperm₀.length_eq.symm
      have hsubset : lists ⊆ m.primeFactorsList.permutations.toFinset := by
        intro l hl
        rcases Finset.mem_image.mp hl with ⟨q, hq, rfl⟩
        rw [List.mem_toFinset, List.mem_permutations]
        have hqdata := (Finset.mem_filter.mp hq).2
        apply Nat.primeFactorsList_unique
        · simpa [tupleList, List.prod_ofFn] using hqdata.2
        · intro p hp
          simp only [tupleList, List.mem_ofFn] at hp
          obtain ⟨j, rfl⟩ := hp
          exact (hqdata.1 j).1
      calc
        tuples.card = lists.card := hcard
        _ ≤ m.primeFactorsList.permutations.toFinset.card :=
          Finset.card_le_card hsubset
        _ ≤ m.primeFactorsList.permutations.length :=
          List.toFinset_card_le _
        _ = Nat.factorial m.primeFactorsList.length :=
          List.length_permutations _
        _ = R.factorial := by rw [hlength]
    · have hempty : tuples = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp htuples
      simp [hempty]
  have hcardReal : (tuples.card : ℝ) ≤ (R.factorial : ℝ) := by
    exact_mod_cast hcardNat
  simpa only [matomakiTeravainenStructuredTypeIICoefficient, tuples,
    Complex.norm_natCast] using hcardReal

/-- The dyadic analogue of `structuredShortPrimeProduct`. -/
noncomputable def structuredDyadicPrimeProduct
    {R : ℕ} (Q : Fin R → ℝ) (t : ℝ) : ℂ :=
  ∏ j, harmanPrimePolynomial (Q j) 1 t

/-- Harman's estimate, specialized without loss to the line `Re(s)=1`
and a positive height `t`, by choosing the source parameter `V=t`.

This is the strongest pointwise statement that follows by direct
instantiation of the encoded source theorem: its polynomial is still the
full dyadic prime sum. -/
theorem harman_dyadic_at_one_of_positive_height
    (hHarman : HarmanLemmaOneFiveStatement) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P t : ℝ), Real.exp 1 ≤ t → 2 ≤ P →
        ‖harmanPrimePolynomial P 1 t‖ ≤
          C *
            (Real.exp
                (-Real.log P /
                  (Real.log t) ^ (7 / 10 : ℝ)) +
              (Real.log P) ^ (3 : ℕ) / t) := by
  obtain ⟨C, hC, hbound⟩ := hHarman 1
  refine ⟨C, hC, ?_⟩
  intro P t ht hP
  have htpos : 0 < t := (Real.exp_pos 1).trans_le ht
  have habs : |t| = t := abs_of_pos htpos
  have h := hbound t P t ht hP
    (by simp [habs]) (by rw [habs]; linarith)
  simpa [div_eq_mul_inv, mul_comm] using h

/-- Multiplying the direct Harman bounds gives a completely source-closed
estimate for the dyadic surrogate of the structured product. -/
theorem norm_structuredDyadicPrimeProduct_le
    (hHarman : HarmanLemmaOneFiveStatement) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (t : ℝ) (R : ℕ) (Q : Fin R → ℝ),
        Real.exp 1 ≤ t →
        (∀ j, 2 ≤ Q j) →
        ‖structuredDyadicPrimeProduct Q t‖ ≤
          ∏ j,
            C *
              (Real.exp
                  (-Real.log (Q j) /
                    (Real.log t) ^ (7 / 10 : ℝ)) +
                (Real.log (Q j)) ^ (3 : ℕ) / t) := by
  obtain ⟨C, hC, hpoint⟩ :=
    harman_dyadic_at_one_of_positive_height hHarman
  refine ⟨C, hC, ?_⟩
  intro t R Q ht hQ
  rw [structuredDyadicPrimeProduct, norm_prod]
  exact Finset.prod_le_prod₀
    (fun j _ ↦ norm_nonneg (harmanPrimePolynomial (Q j) 1 t))
    (fun j _ ↦ hpoint (Q j) t ht (hQ j))

/-! ## Elementary bounds for the genuinely short factor -/

/-- The elementary triangle-inequality estimate for the actual short prime
factor.  Unlike Harman's cancellation estimate, it retains the cardinality
of the short prime set.  This is useful for locating the precise gap: a
Fourier/Perron cutoff lemma must transfer cancellation from the dyadic sum;
set inclusion alone only gives this cardinality bound. -/
theorem norm_structuredShortPrimePolynomial_le_card_div
    {Q delta t : ℝ} (hQ : 0 < Q) (hdelta : 0 ≤ delta) :
    ‖structuredShortPrimePolynomial Q delta t‖ ≤
      (((natOpenClosedInterval Q ((1 + delta) * Q)).filter
          Nat.Prime).card : ℝ) / Q := by
  let S : Finset ℕ :=
    (natOpenClosedInterval Q ((1 + delta) * Q)).filter Nat.Prime
  have hupper : 0 ≤ (1 + delta) * Q :=
    mul_nonneg (by linarith) hQ.le
  have hterm : ∀ p ∈ S,
      ‖(1 : ℂ) * (p : ℂ) ^ (-onePlusIT t)‖ ≤ Q⁻¹ := by
    intro p hp
    have hpInterval : p ∈ natOpenClosedInterval Q ((1 + delta) * Q) :=
      (Finset.mem_filter.mp hp).1
    have hpRange :=
      (mem_natOpenClosedInterval hQ.le hupper).mp hpInterval
    have hpPosReal : 0 < (p : ℝ) := hQ.trans hpRange.1
    have hpPos : 0 < p := by exact_mod_cast hpPosReal
    rw [one_mul, TypeII.norm_cpow_neg_onePlusIT_eq_inv hpPos t]
    exact (inv_le_inv₀ hpPosReal hQ).2 hpRange.1.le
  change ‖∑ p ∈ S, (1 : ℂ) * (p : ℂ) ^ (-onePlusIT t)‖ ≤ _
  calc
    ‖∑ p ∈ S, (1 : ℂ) * (p : ℂ) ^ (-onePlusIT t)‖ ≤
        ∑ p ∈ S, ‖(1 : ℂ) * (p : ℂ) ^ (-onePlusIT t)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ S, Q⁻¹ := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) / Q := by
      simp [div_eq_mul_inv]
    _ = (((natOpenClosedInterval Q ((1 + delta) * Q)).filter
          Nat.Prime).card : ℝ) / Q := rfl

/-- Every full dyadic prime polynomial on the line `Re(s)=1` has the
absolute (non-cancellation) bound `4`.  The deliberately loose constant
keeps the ceiling arithmetic transparent. -/
theorem norm_harmanPrimePolynomial_le_four
    {P t : ℝ} (hP : 2 ≤ P) :
    ‖harmanPrimePolynomial P 1 t‖ ≤ 4 := by
  have hPpos : 0 < P := by linarith
  have hterm : ∀ p ∈ harmanDyadicPrimes P,
      ‖(1 : ℂ) * (p : ℂ) ^ (-onePlusIT t)‖ ≤ P⁻¹ := by
    intro p hp
    have hpdata := (Finset.mem_filter.mp hp).2
    have hpPosReal : 0 < (p : ℝ) := hPpos.trans_le hpdata.2.1
    have hpPos : 0 < p := by exact_mod_cast hpPosReal
    rw [one_mul, TypeII.norm_cpow_neg_onePlusIT_eq_inv hpPos t]
    exact (inv_le_inv₀ hpPosReal hPpos).2 hpdata.2.1
  have hcardNat : (harmanDyadicPrimes P).card ≤ ⌈2 * P⌉₊ := by
    calc
      (harmanDyadicPrimes P).card ≤
          (Finset.range ⌈2 * P⌉₊).card := by
        apply Finset.card_le_card
        intro p hp
        exact (Finset.mem_filter.mp hp).1
      _ = ⌈2 * P⌉₊ := Finset.card_range _
  have hcardReal : ((harmanDyadicPrimes P).card : ℝ) ≤ 4 * P := by
    calc
      ((harmanDyadicPrimes P).card : ℝ) ≤ (⌈2 * P⌉₊ : ℝ) := by
        exact_mod_cast hcardNat
      _ ≤ 2 * (2 * P) := by
        exact_mod_cast Nat.ceil_le_two_mul (by linarith : (2 : ℝ)⁻¹ ≤ 2 * P)
      _ = 4 * P := by ring
  simp only [harmanPrimePolynomial, dirichletPolynomial]
  calc
    ‖∑ p ∈ harmanDyadicPrimes P,
        (1 : ℂ) * (p : ℂ) ^ (-onePlusIT t)‖ ≤
        ∑ p ∈ harmanDyadicPrimes P,
          ‖(1 : ℂ) * (p : ℂ) ^ (-onePlusIT t)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ harmanDyadicPrimes P, P⁻¹ :=
      Finset.sum_le_sum hterm
    _ = ((harmanDyadicPrimes P).card : ℝ) * P⁻¹ := by simp
    _ ≤ (4 * P) * P⁻¹ :=
      mul_le_mul_of_nonneg_right hcardReal (inv_nonneg.mpr hPpos.le)
    _ = 4 := by field_simp [hPpos.ne']

/-- Once one selected dyadic factor has a cancellation bound `E`, all
remaining factors can be bounded absolutely at cost `4^(R-1)`. -/
theorem norm_structuredDyadicPrimeProduct_le_selected
    {R : ℕ} (Q : Fin R → ℝ) (t E : ℝ) (j₀ : Fin R)
    (hQ : ∀ j, 2 ≤ Q j)
    (hselected : ‖harmanPrimePolynomial (Q j₀) 1 t‖ ≤ E) :
    ‖structuredDyadicPrimeProduct Q t‖ ≤ E * 4 ^ (R - 1) := by
  rw [structuredDyadicPrimeProduct, norm_prod,
    ← Finset.mul_prod_erase Finset.univ
      (fun j ↦ ‖harmanPrimePolynomial (Q j) 1 t‖)
      (Finset.mem_univ j₀)]
  have hrest : ∏ j ∈ (Finset.univ.erase j₀),
      ‖harmanPrimePolynomial (Q j) 1 t‖ ≤
      ∏ _j ∈ (Finset.univ.erase j₀), (4 : ℝ) := by
    exact Finset.prod_le_prod₀
      (fun j _ ↦ norm_nonneg (harmanPrimePolynomial (Q j) 1 t))
      (fun j _ ↦ norm_harmanPrimePolynomial_le_four (hQ j))
  calc
    ‖harmanPrimePolynomial (Q j₀) 1 t‖ *
          ∏ j ∈ Finset.univ.erase j₀,
            ‖harmanPrimePolynomial (Q j) 1 t‖ ≤
        E * ∏ _j ∈ Finset.univ.erase j₀, (4 : ℝ) :=
      mul_le_mul hselected hrest
        (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
        (by exact le_trans (norm_nonneg _) hselected)
    _ = E * 4 ^ (R - 1) := by simp

/-- Harman's dyadic estimate already has more than the required exponential
saving as soon as its two printed terms satisfy the displayed elementary
scale comparisons.  This isolates all number-theoretic input from the later
real-variable exponent bookkeeping. -/
theorem harman_dyadic_exp_decay_of_numeric_scales
    (hHarman : HarmanLemmaOneFiveStatement) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (P t Y : ℝ), Real.exp 1 ≤ t → 2 ≤ P → 0 ≤ Y →
        4 * Y ≤ Real.log P / (Real.log t) ^ (7 / 10 : ℝ) →
        (Real.log P) ^ (3 : ℕ) / t ≤ Real.exp (-4 * Y) →
        ‖harmanPrimePolynomial P 1 t‖ ≤
          2 * C * Real.exp (-4 * Y) := by
  obtain ⟨C, hC, hHarman⟩ :=
    harman_dyadic_at_one_of_positive_height hHarman
  refine ⟨C, hC, ?_⟩
  intro P t Y ht hP _hY hfirst hsecond
  have hfirstExp :
      Real.exp
          (-Real.log P / (Real.log t) ^ (7 / 10 : ℝ)) ≤
        Real.exp (-4 * Y) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div]
    have hneg := neg_le_neg hfirst
    convert hneg using 1
    ring
  calc
    ‖harmanPrimePolynomial P 1 t‖ ≤
        C *
          (Real.exp
              (-Real.log P / (Real.log t) ^ (7 / 10 : ℝ)) +
            (Real.log P) ^ (3 : ℕ) / t) := hHarman P t ht hP
    _ ≤ C * (Real.exp (-4 * Y) + Real.exp (-4 * Y)) := by
      gcongr
    _ = 2 * C * Real.exp (-4 * Y) := by ring

/-- The corresponding structured dyadic surrogate: one selected factor
uses Harman cancellation and the other factors cost only `4^(R-1)`.
At the paper's bound `R=O((log log X)^3)`, this loss is subexponential and
is absorbed by the stronger dyadic Vinogradov--Korobov exponent. -/
theorem structuredDyadicPrimeProduct_exp_decay_of_numeric_scales
    (hHarman : HarmanLemmaOneFiveStatement) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (t Y : ℝ) (R : ℕ) (Q : Fin R → ℝ) (j₀ : Fin R),
        Real.exp 1 ≤ t →
        (∀ j, 2 ≤ Q j) → 0 ≤ Y →
        4 * Y ≤
          Real.log (Q j₀) / (Real.log t) ^ (7 / 10 : ℝ) →
        (Real.log (Q j₀)) ^ (3 : ℕ) / t ≤ Real.exp (-4 * Y) →
        ‖structuredDyadicPrimeProduct Q t‖ ≤
          (2 * C * Real.exp (-4 * Y)) * 4 ^ (R - 1) := by
  obtain ⟨C, hC, hpoint⟩ :=
    harman_dyadic_exp_decay_of_numeric_scales hHarman
  refine ⟨C, hC, ?_⟩
  intro t Y R Q j₀ ht hQ hY hfirst hsecond
  exact norm_structuredDyadicPrimeProduct_le_selected Q t
    (2 * C * Real.exp (-4 * Y)) j₀ hQ
    (hpoint (Q j₀) t Y ht (hQ j₀) hY hfirst hsecond)

def structuredPrimeFactorsModule : ProofModule :=
  { name := "Completion.StructuredPrimeFactors"
    paperLocation := "Proposition 7.1, structured Type-II factor and MT23 equation (5.6)"
    purpose :=
      "Define the exact short and dyadic structured prime factors, prove the finite-fibre product identity and factorial fibre bound, and derive every direct dyadic consequence of Harman's cited lemma."
    dependsOn :=
      [ "TypeII.FullTypeIIEstimate",
        "Assumptions.harmanLemmaOneFive",
        "Assumptions.matomakiTeravainenPropositionTwoTwo" ]
    status := .proved }

end

end Completion
end ExactSemiprimes
