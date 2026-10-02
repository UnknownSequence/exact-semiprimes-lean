import ExactSemiprimes.Sparse.Propagation

/-!
# Global cancellation of component tails

The decomposition in Matomäki--Teräväinen Proposition 2.2 is a
pointwise identity on every natural number, with the minorant cut off on the
ambient interval.  Consequently, individual convolution components need not
be truncated before they are estimated: on any finite set containing all
their supports, their portions outside the ambient interval cancel globally
against the remainder.
-/

namespace ExactSemiprimes
namespace Sparse

open scoped BigOperators

noncomputable section

/-! ## Literal finite supports of the three source alternatives -/

def typeIProductSupport (delta M₁ M₂ : ℝ) : Finset ℕ :=
  ((dyadicInterval M₁).product
    (natOpenClosedInterval M₂ ((1 + delta) * M₂))).image
      fun p ↦ p.1 * p.2

def typeIOneHalfProductSupport
    (delta M₁ M₂ M₃ : ℝ) : Finset ℕ :=
  ((((dyadicInterval M₁).product (dyadicInterval M₂)).product
    (natOpenClosedInterval M₃ ((1 + delta) * M₃))).image
      fun p ↦ p.1.1 * p.1.2 * p.2)

theorem matomakiTeravainenTypeIValue_eq_zero_of_not_mem_productSupport
    {delta M₁ M₂ : ℝ} {alpha : ℕ → ℂ} {n : ℕ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hn : n ∉ typeIProductSupport delta M₁ M₂) :
    matomakiTeravainenTypeIValue delta M₁ M₂ alpha n = 0 := by
  classical
  rw [matomakiTeravainenTypeIValue]
  apply Finset.sum_eq_zero
  intro m₁ hm₁
  apply Finset.sum_eq_zero
  intro m₂ hm₂
  split_ifs with hconditions
  · exfalso
    apply hn
    rw [typeIProductSupport, Finset.mem_image]
    refine ⟨(m₁, m₂), Finset.mem_product.mpr ⟨?_, ?_⟩,
      hconditions.1⟩
    · exact (mem_dyadicInterval hM₁.le).mpr hconditions.2.1
    · exact (mem_natOpenClosedInterval hM₂.le
        (mul_nonneg (by linarith) hM₂.le)).mpr
          ⟨hconditions.2.2.1, hconditions.2.2.2⟩
  · rfl

theorem matomakiTeravainenTypeIOneHalfValue_eq_zero_of_not_mem_productSupport
    {delta M₁ M₂ M₃ : ℝ} {alpha beta : ℕ → ℂ} {n : ℕ}
    (hdelta : 0 ≤ delta) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM₃ : 0 < M₃)
    (hn : n ∉ typeIOneHalfProductSupport delta M₁ M₂ M₃) :
    matomakiTeravainenTypeIOneHalfValue
      delta M₁ M₂ M₃ alpha beta n = 0 := by
  classical
  rw [matomakiTeravainenTypeIOneHalfValue]
  apply Finset.sum_eq_zero
  intro m₁ hm₁
  apply Finset.sum_eq_zero
  intro m₂ hm₂
  apply Finset.sum_eq_zero
  intro m₃ hm₃
  split_ifs with hconditions
  · exfalso
    apply hn
    rw [typeIOneHalfProductSupport, Finset.mem_image]
    refine ⟨((m₁, m₂), m₃), Finset.mem_product.mpr ⟨?_, ?_⟩,
      hconditions.1⟩
    · exact Finset.mem_product.mpr
        ⟨(mem_dyadicInterval hM₁.le).mpr hconditions.2.1,
          (mem_dyadicInterval hM₂.le).mpr hconditions.2.2.1⟩
    · exact (mem_natOpenClosedInterval hM₃.le
        (mul_nonneg (by linarith) hM₃.le)).mpr
          ⟨hconditions.2.2.2.1, hconditions.2.2.2.2⟩
  · rfl

/-- Every component in one of the three alternatives of Proposition 2.2
has a literal finite support.  The Type-II choice is precisely the product
support on which its polynomial factorization has already been proved. -/
theorem exists_finiteSupport_of_matomakiTeravainenComponent
    {X Y epsilon delta z₀ z Bcoeff Acoeff : ℝ} {f : ℕ → ℂ}
    (hdelta : 0 ≤ delta)
    (hcase :
      MatomakiTeravainenTypeICase
          X Y epsilon delta Bcoeff Acoeff f ∨
        MatomakiTeravainenTypeIOneHalfCase
          X Y epsilon delta Bcoeff Acoeff f ∨
        MatomakiTeravainenTypeIICase
          X Y epsilon delta z₀ z Bcoeff Acoeff f) :
    ∃ support : Finset ℕ, ∀ n, n ∉ support → f n = 0 := by
  rcases hcase with hI | hIOII | hII
  · rcases hI with
      ⟨M₁, M₂, alpha, hM₁, hM₂, _halpha, _hM₁upper,
        _hprodLower, _hprodUpper, hf⟩
    refine ⟨typeIProductSupport delta M₁ M₂, ?_⟩
    intro n hn
    rw [hf n]
    exact matomakiTeravainenTypeIValue_eq_zero_of_not_mem_productSupport
      hdelta hM₁ hM₂ hn
  · rcases hIOII with
      ⟨M₁, M₂, M₃, alpha, beta, hM₁, hM₂, hM₃,
        _halpha, _hbeta, _hscale, _hM₂upper, _hprodLower,
        _hprodUpper, hf⟩
    refine ⟨typeIOneHalfProductSupport delta M₁ M₂ M₃, ?_⟩
    intro n hn
    rw [hf n]
    exact
      matomakiTeravainenTypeIOneHalfValue_eq_zero_of_not_mem_productSupport
        hdelta hM₁ hM₂ hM₃ hn
  · rcases hII with
      ⟨R, M₁, M₂, alpha, beta, Q, _hR, _hRupper, hM₁, hM₂,
        _halphaBound, _hbetaBound, _hM₁lower, _hM₁upper,
        _hprodLower, _hprodUpper, _hQ, _hprodQ, _halpha, hf⟩
    refine ⟨typeIIProductSupport delta M₁ M₂ R, ?_⟩
    intro n hn
    exact representedTypeII_eq_zero_of_not_mem_productSupport
      hdelta hM₁ hM₂ hf hn

/-- Classical choice packages the literal finite support of every member of
a finite Proposition 2.2 family into one support function.  Values away from
the family are irrelevant and are assigned the empty support. -/
theorem exists_componentSupportFunction_of_matomakiTeravainenCases
    {X Y epsilon delta z₀ z Bcoeff Acoeff : ℝ}
    (components : Finset (ℕ → ℂ))
    (hdelta : 0 ≤ delta)
    (hcases : ∀ f ∈ components,
      MatomakiTeravainenTypeICase
          X Y epsilon delta Bcoeff Acoeff f ∨
        MatomakiTeravainenTypeIOneHalfCase
          X Y epsilon delta Bcoeff Acoeff f ∨
        MatomakiTeravainenTypeIICase
          X Y epsilon delta z₀ z Bcoeff Acoeff f) :
    ∃ componentSupport : (ℕ → ℂ) → Finset ℕ,
      ∀ f ∈ components, ∀ n,
        n ∉ componentSupport f → f n = 0 := by
  classical
  have hexists : ∀ f : {f // f ∈ components},
      ∃ support : Finset ℕ, ∀ n, n ∉ support → f.1 n = 0 := by
    intro f
    exact exists_finiteSupport_of_matomakiTeravainenComponent hdelta
      (hcases f.1 f.2)
  choose support hsupport using hexists
  let componentSupport : (ℕ → ℂ) → Finset ℕ := fun f ↦
    if hf : f ∈ components then support ⟨f, hf⟩ else ∅
  refine ⟨componentSupport, ?_⟩
  intro f hf n hn
  have hn' : n ∉ support ⟨f, hf⟩ := by
    simpa [componentSupport, hf] using hn
  exact hsupport ⟨f, hf⟩ n hn'

/-- A globally valid pointwise decomposition can be summed on any finite
superset of the ambient support.  This is the basic cancellation mechanism:
the right side retains all component values on `S`, including their
individual upper tails, while their sum is still exactly the polynomial of
the ambiently truncated left side. -/
theorem dirichletPolynomial_globalDecomposition_on_superset
    {weight remainder : ℕ → ℂ} {components : Finset (ℕ → ℂ)}
    {ambient S : Finset ℕ} {s : ℂ}
    (hambient : ambient ⊆ S)
    (hdecomp : ∀ n : ℕ,
      (if n ∈ ambient then weight n else 0) =
        (∑ f ∈ components, f n) + remainder n) :
    dirichletPolynomial weight ambient s =
      (∑ f ∈ components, dirichletPolynomial f S s) +
        dirichletPolynomial remainder S s := by
  classical
  unfold dirichletPolynomial
  calc
    (∑ n ∈ ambient, weight n * (n : ℂ) ^ (-s)) =
        ∑ n ∈ S,
            (if n ∈ ambient then weight n else 0) *
            (n : ℂ) ^ (-s) := by
      symm
      calc
        (∑ n ∈ S,
            (if n ∈ ambient then weight n else 0) *
              (n : ℂ) ^ (-s)) =
            ∑ n ∈ ambient,
              (if n ∈ ambient then weight n else 0) *
                (n : ℂ) ^ (-s) := by
          symm
          apply Finset.sum_subset hambient
          intro n hnS hnAmbient
          simp [hnAmbient]
        _ = ∑ n ∈ ambient, weight n * (n : ℂ) ^ (-s) := by
          apply Finset.sum_congr rfl
          intro n hn
          simp [hn]
    _ = ∑ n ∈ S,
          ((∑ f ∈ components, f n) + remainder n) *
            (n : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hdecomp n]
    _ = (∑ f ∈ components,
            ∑ n ∈ S, f n * (n : ℂ) ^ (-s)) +
          ∑ n ∈ S, remainder n * (n : ℂ) ^ (-s) := by
      simp_rw [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
      rw [Finset.sum_comm]

/-- If a function vanishes off `support`, summing it over a larger finite
set is the same as summing it over its literal support. -/
theorem dirichletPolynomial_eq_support_of_subset
    {f : ℕ → ℂ} {support S : Finset ℕ} {s : ℂ}
    (hsubset : support ⊆ S)
    (hzero : ∀ n, n ∉ support → f n = 0) :
    dirichletPolynomial f S s = dirichletPolynomial f support s := by
  rw [dirichletPolynomial_eq_inter_of_zero_outside hzero]
  congr 1
  exact Finset.inter_eq_left.mpr hsubset

/-- Dirichlet polynomials over any two finite supports of the same function
are equal.  This lets a globally chosen support be replaced by the literal
product support exposed when a particular component alternative is opened. -/
theorem dirichletPolynomial_eq_of_two_finiteSupports
    {f : ℕ → ℂ} {support₁ support₂ : Finset ℕ} {s : ℂ}
    (hzero₁ : ∀ n, n ∉ support₁ → f n = 0)
    (hzero₂ : ∀ n, n ∉ support₂ → f n = 0) :
    dirichletPolynomial f support₁ s =
      dirichletPolynomial f support₂ s := by
  calc
    dirichletPolynomial f support₁ s =
        dirichletPolynomial f (support₁ ∪ support₂) s :=
      (dirichletPolynomial_eq_support_of_subset
        Finset.subset_union_left hzero₁).symm
    _ = dirichletPolynomial f support₂ s :=
      dirichletPolynomial_eq_support_of_subset
        Finset.subset_union_right hzero₂

/-- Fully support-resolved form of global tail cancellation.  Each component
may have its own finite support.  Although an individual support may extend
past `ambient`, the sum of the complete component polynomials (and the
complete remainder polynomial) is exactly the ambient polynomial.

This is the form needed for Proposition 2.2: convolution factorization is
applied on each component's literal product support, while the source's
global pointwise identity performs the cancellation outside the ambient
Perron interval. -/
theorem dirichletPolynomial_globalDecomposition_on_componentSupports
    {weight remainder : ℕ → ℂ} (components : Finset (ℕ → ℂ))
    (ambient remainderSupport : Finset ℕ)
    (componentSupport : (ℕ → ℂ) → Finset ℕ) (s : ℂ)
    (hdecomp : ∀ n : ℕ,
      (if n ∈ ambient then weight n else 0) =
        (∑ f ∈ components, f n) + remainder n)
    (hcomponentZero : ∀ f ∈ components, ∀ n,
      n ∉ componentSupport f → f n = 0)
    (hremainderZero : ∀ n, n ∉ remainderSupport → remainder n = 0) :
    dirichletPolynomial weight ambient s =
      (∑ f ∈ components,
        dirichletPolynomial f (componentSupport f) s) +
      dirichletPolynomial remainder remainderSupport s := by
  classical
  let S : Finset ℕ :=
    ambient ∪ remainderSupport ∪
      components.biUnion componentSupport
  have hambient : ambient ⊆ S := by
    intro n hn
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hn)
  have hcomponentSubset : ∀ f ∈ components, componentSupport f ⊆ S := by
    intro f hf n hn
    apply Finset.mem_union_right
    exact Finset.mem_biUnion.mpr ⟨f, hf, hn⟩
  have hremainderSubset : remainderSupport ⊆ S := by
    intro n hn
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hn)
  rw [dirichletPolynomial_globalDecomposition_on_superset
    hambient hdecomp]
  congr 1
  · apply Finset.sum_congr rfl
    intro f hf
    exact dirichletPolynomial_eq_support_of_subset
      (hcomponentSubset f hf) (hcomponentZero f hf)
  · exact dirichletPolynomial_eq_support_of_subset
      hremainderSubset hremainderZero

/-- Specialization to the literal global identity and remainder support in
Matomäki--Teräväinen Proposition 2.2.  The component supports are left as
data because the three alternatives have different product boxes.  In
particular, no componentwise inclusion in `(Y/2,4Y]` is required. -/
theorem matomakiTeravainenDecomposition_fullComponentSupports
    {X Y epsilon : ℝ} {components : Finset (ℕ → ℂ)}
    {remainder : ℕ → ℂ}
    (componentSupport : (ℕ → ℂ) → Finset ℕ) (s : ℂ)
    (hY : 0 ≤ Y)
    (hdecomp : ∀ n : ℕ,
      (if n ∈ natOpenClosedInterval (Y / 2) (4 * Y) then
          (matomakiTeravainenMinorant X epsilon n : ℂ)
        else 0) =
        (∑ f ∈ components, f n) + remainder n)
    (hremainderSupport : ∀ n : ℕ, remainder n ≠ 0 →
      Y / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * Y)
    (hcomponentZero : ∀ f ∈ components, ∀ n,
      n ∉ componentSupport f → f n = 0) :
    dirichletPolynomial
        (fun n ↦ (matomakiTeravainenMinorant X epsilon n : ℂ))
        (natOpenClosedInterval (Y / 2) (4 * Y)) s =
      (∑ f ∈ components,
        dirichletPolynomial f (componentSupport f) s) +
      dirichletPolynomial remainder
        (natOpenClosedInterval (Y / 4) (8 * Y)) s := by
  apply dirichletPolynomial_globalDecomposition_on_componentSupports
    components (natOpenClosedInterval (Y / 2) (4 * Y))
      (natOpenClosedInterval (Y / 4) (8 * Y)) componentSupport s
      hdecomp hcomponentZero
  intro n hn
  by_contra hne
  exact hn ((mem_natOpenClosedInterval (by positivity) (by positivity)).2
    (hremainderSupport n hne))

/-- End-to-end cancellation package for the output of Proposition 2.2.
The source alternatives themselves provide a finite support for each
component; classical choice selects those supports, and the global source
identity then sums the *complete* component polynomials.  Thus no estimate
for an individual component's upper tail is needed. -/
theorem exists_matomakiTeravainenDecomposition_fullComponentSupports
    {X Y epsilon delta z₀ z Bcoeff Acoeff : ℝ}
    {components : Finset (ℕ → ℂ)} {remainder : ℕ → ℂ}
    (s : ℂ) (hdelta : 0 ≤ delta) (hY : 0 ≤ Y)
    (hdecomp : ∀ n : ℕ,
      (if n ∈ natOpenClosedInterval (Y / 2) (4 * Y) then
          (matomakiTeravainenMinorant X epsilon n : ℂ)
        else 0) =
        (∑ f ∈ components, f n) + remainder n)
    (hremainderSupport : ∀ n : ℕ, remainder n ≠ 0 →
      Y / 4 < (n : ℝ) ∧ (n : ℝ) ≤ 8 * Y)
    (hcases : ∀ f ∈ components,
      MatomakiTeravainenTypeICase
          X Y epsilon delta Bcoeff Acoeff f ∨
        MatomakiTeravainenTypeIOneHalfCase
          X Y epsilon delta Bcoeff Acoeff f ∨
        MatomakiTeravainenTypeIICase
          X Y epsilon delta z₀ z Bcoeff Acoeff f) :
    ∃ componentSupport : (ℕ → ℂ) → Finset ℕ,
      (∀ f ∈ components, ∀ n,
        n ∉ componentSupport f → f n = 0) ∧
      dirichletPolynomial
          (fun n ↦ (matomakiTeravainenMinorant X epsilon n : ℂ))
          (natOpenClosedInterval (Y / 2) (4 * Y)) s =
        (∑ f ∈ components,
          dirichletPolynomial f (componentSupport f) s) +
        dirichletPolynomial remainder
          (natOpenClosedInterval (Y / 4) (8 * Y)) s := by
  obtain ⟨componentSupport, hcomponentZero⟩ :=
    exists_componentSupportFunction_of_matomakiTeravainenCases
      components hdelta hcases
  refine ⟨componentSupport, hcomponentZero, ?_⟩
  exact matomakiTeravainenDecomposition_fullComponentSupports componentSupport
    s hY hdecomp hremainderSupport hcomponentZero

end

end Sparse
end ExactSemiprimes
