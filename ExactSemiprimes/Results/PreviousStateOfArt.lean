import ExactSemiprimes.Definitions

/-! # Previous Matomäki--Teräväinen theorem (comparison only) -/

namespace ExactSemiprimes
namespace Results

/-- Matomäki--Teräväinen [MT23, Theorem 1.1], recorded for comparison in
fully quantified form.  No inhabitant is postulated because this theorem is
not used in the new proof. -/
def PreviousStateOfArtStatement : Prop :=
  ∃ cMT δMT C : ℝ, 0 < cMT ∧ 0 < δMT ∧ 0 < C ∧
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((Finset.Icc 2 X).filter fun (x : ℕ) ↦
        (windowedPrimeProductCount
          (x : ℝ)
          (logarithmicLength ((21 : ℝ) / 10) x)
          ((Real.log (x : ℝ)) ^ ((109 : ℝ) / 100))
          ((Real.log (x : ℝ)) ^ ((11 : ℝ) / 10)) : ℝ) <
            cMT * (Real.log (x : ℝ)) ^ ((11 : ℝ) / 10)).card : ℝ)
        ≤ C * (X : ℝ) / (Real.log (X : ℝ)) ^ δMT

def previousStateOfArtModule : ProofModule :=
  { name := "Results.PreviousStateOfArt"
    paperLocation := "Theorem 1.1 (quoted from Matomäki--Teräväinen)"
    purpose := "Record the published exponent 2.1 for comparison; it is not used to prove the new theorem."
    dependsOn := []
    status := .comparisonOnly }

end Results
end ExactSemiprimes
