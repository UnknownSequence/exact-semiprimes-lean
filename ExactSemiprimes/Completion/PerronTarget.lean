import ExactSemiprimes.Assumptions

/-! # Matomäki--Teräväinen Perron reduction target -/

namespace ExactSemiprimes
namespace Completion

open MeasureTheory

noncomputable section

/-- The minorant Dirichlet polynomial supported on
`X/(2P) < n ≤ 4X/P` in the Perron reduction. -/
def perronMinorantPolynomial
    (weight : ℕ → ℝ) (X P : ℝ) (s : ℂ) : ℂ :=
  dirichletPolynomial (fun n ↦ (weight n : ℂ))
    (natOpenClosedInterval (X / (2 * P)) (4 * X / P)) s

/-- The product of the dyadic prime polynomial and the minorant polynomial
on the line `Re(s)=1`. -/
def perronProduct
    (weight : ℕ → ℝ) (X P t : ℝ) : ℂ :=
  primeDirichletPolynomial P (onePlusIT t) *
    perronMinorantPolynomial weight X P (onePlusIT t)

/-- The exact Dirichlet-polynomial integral occurring in `(DPtarget)`. -/
def perronProductIntegral
    (weight : ℕ → ℝ) (X P T : ℝ) : ℝ :=
  ∫ t in Set.Ioc (X ^ (1 / 1000 : ℝ)) T,
    ‖perronProduct weight X P t‖ ^ 2

/-! ## Exact normalization against the published integral -/

/-- The internal minorant polynomial is exactly the polynomial occurring in
the source-scoped transcription of [MT23, Lemma 3.1]. -/
theorem perronMinorantPolynomial_eq_matomakiTeravainen
    (weight : ℕ → ℝ) (X P : ℝ) (s : ℂ) :
    perronMinorantPolynomial weight X P s =
      dirichletPolynomial (fun n ↦ (weight n : ℂ))
        (natOpenClosedInterval (X / (2 * P)) (4 * X / P)) s :=
  rfl

/-- There is no hidden change of line, support, endpoint convention, or
normalizing factor between `perronProductIntegral` and the exact integral in
the imported Matomäki--Teräväinen statement.  The latter keeps its lower
height as an argument, so here it is specialized to the paper's
`T₀ = X^(1/1000)`. -/
theorem perronProductIntegral_eq_matomakiTeravainen
    (weight : ℕ → ℝ) (X P T : ℝ) :
    perronProductIntegral weight X P T =
      matomakiTeravainenPerronIntegral weight X P
        (X ^ (1 / 1000 : ℝ)) T :=
  rfl

/-- Fully quantified target delivered after the Perron reduction.  The
constant and starting scale are explicit, and the statement includes every
height `T≥X/h`; the range `T≥X` is later dispatched by the ordinary mean
value theorem. -/
def PerronDirichletPolynomialTargetStatement
    (minorant : ℕ → ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ a c : ℝ,
        35 / 32 + η ≤ a → a ≤ 11 / 10 →
        a ≤ c - 1 → 2 + η < c →
        ∃ C : ℝ, 0 < C ∧
          ∃ X₀ : ℕ, 3 ≤ X₀ ∧
            ∀ X : ℕ, X₀ ≤ X →
              ∀ T : ℝ,
                (X : ℝ) / (Real.log (X : ℝ)) ^ c ≤ T →
                perronProductIntegral (minorant X)
                    (X : ℝ) ((Real.log (X : ℝ)) ^ a) T ≤
                  C * (T / ((X : ℝ) /
                    (Real.log (X : ℝ)) ^ c)) /
                      (Real.log (X : ℝ)) ^ (2 + ε₀)

def perronTargetModule : ProofModule :=
  { name := "Completion.PerronTarget"
    paperLocation := "Proof of Proposition 7.1, reduction of variance to a Dirichlet-polynomial integral"
    purpose :=
      "Identify the internal integral exactly with the printed MT23 normalization and state the wider uniform Dirichlet-polynomial target. The target is proved in Final/DirichletTarget.lean."
    dependsOn := ["Assumptions.matomakiTeravainenLemmaThreeOne"]
    status := .superseded }

end

end Completion
end ExactSemiprimes
