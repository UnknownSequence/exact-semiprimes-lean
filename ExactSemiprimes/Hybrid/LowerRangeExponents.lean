import ExactSemiprimes.Definitions

/-!
# Hybrid-density exponent check below length `T^(5/6)`

This file formalizes only the exponent arithmetic in the lower-length half of
the proof of Lemma 4.3.  In particular, it does not assert or invoke the
Guth--Maynard large-values theorem.

The three definitions below are the powers of `T` obtained from the three
terms of the normalized main Guth--Maynard estimate after writing
`N = T^η`.  The parameter `ρ` records the coefficient-normalization loss.
-/

namespace ExactSemiprimes
namespace Hybrid
namespace LowerRange

noncomputable section

/-- The critical large-value threshold `17/70`. -/
def sigmaZero : ℝ := 17 / 70

/-- The nominal lower endpoint of the polynomial-length exponent. -/
def etaLower : ℝ := 9 / 11

/-- The point at which the proof switches to the long-polynomial estimate. -/
def etaJoin : ℝ := 5 / 6

/-- Exponent of the first term in the normalized lower-range estimate. -/
def firstExponent (η σ ρ : ℝ) : ℝ := η * (2 * σ + 4 * ρ)

/-- Exponent of the second term in the normalized lower-range estimate. -/
def secondExponent (η σ ρ : ℝ) : ℝ :=
  η * (4 * σ - 2 / 5 + 8 * ρ)

/-- Exponent of the third term in the normalized lower-range estimate. -/
def thirdExponent (η σ ρ : ℝ) : ℝ :=
  1 + η * (4 * σ - 8 / 5 + 8 * ρ)

/-- The target exponent in the density estimate. -/
def targetExponent (σ : ℝ) : ℝ := 2 * σ

/-! ## Exact identities at the critical threshold -/

theorem target_at_sigmaZero : targetExponent sigmaZero = 17 / 35 := by
  norm_num [targetExponent, sigmaZero]

theorem first_at_sigmaZero (η : ℝ) :
    firstExponent η sigmaZero 0 = (17 / 35) * η := by
  norm_num [firstExponent, sigmaZero]
  ring

theorem second_at_sigmaZero (η : ℝ) :
    secondExponent η sigmaZero 0 = (4 / 7) * η := by
  norm_num [secondExponent, sigmaZero]
  ring

theorem third_at_sigmaZero (η : ℝ) :
    thirdExponent η sigmaZero 0 = 1 - (22 / 35) * η := by
  norm_num [thirdExponent, sigmaZero]
  ring

/-- The third term saturates the target at the corner `(η,σ)=(9/11,17/70)`. -/
theorem third_corner_saturation :
    thirdExponent etaLower sigmaZero 0 = targetExponent sigmaZero := by
  norm_num [thirdExponent, targetExponent, etaLower, sigmaZero]

/-- The second term has the exact gap `1/105` at the joining point `η=5/6`. -/
theorem second_join_gap :
    targetExponent sigmaZero - secondExponent etaJoin sigmaZero 0 = 1 / 105 := by
  norm_num [targetExponent, secondExponent, etaJoin, sigmaZero]

/-- The gap of the saturating third term is linear in the distance from the
nominal lower endpoint. -/
theorem third_gap_formula (η : ℝ) :
    targetExponent sigmaZero - thirdExponent η sigmaZero 0 =
      (22 / 35) * (η - etaLower) := by
  norm_num [targetExponent, thirdExponent, sigmaZero, etaLower]
  ring

/-! ## Uniform lower-range gaps at `σ = 17/70` -/

/-- The first term actually has substantially more room than is needed. -/
theorem first_uniform_gap {η : ℝ} (hη : η ≤ etaJoin) :
    firstExponent η sigmaZero 0 ≤ targetExponent sigmaZero - 17 / 210 := by
  norm_num [firstExponent, targetExponent, sigmaZero, etaJoin] at hη ⊢
  linarith

/-- The second term has the uniform gap `1/105` on the lower range. -/
theorem second_uniform_gap {η : ℝ} (hη : η ≤ etaJoin) :
    secondExponent η sigmaZero 0 ≤ targetExponent sigmaZero - 1 / 105 := by
  norm_num [secondExponent, targetExponent, sigmaZero, etaJoin] at hη ⊢
  linarith

/-- The third term is below target throughout the nominal range and meets it
only at its lower endpoint. -/
theorem third_nonnegative_gap {η : ℝ} (hη : etaLower ≤ η) :
    thirdExponent η sigmaZero 0 ≤ targetExponent sigmaZero := by
  have hgap := third_gap_formula η
  have hnonneg : 0 ≤ (22 / 35 : ℝ) * (η - etaLower) := by
    positivity
  linarith

/-! ## Explicit absorption of the `ε`- and `ρ`-losses

The paper only needs unspecified sufficiently small constants.  The next
three lemmas give one concrete choice: `0 < ε ≤ 1/1000`,
`0 ≤ ρ ≤ ε²`, and `σ ≤ 17/70 - 6ε`.  These constants are not claimed to be
optimal; they make the phrase “taking `C` sufficiently large” completely
checkable.
-/

private theorem epsilon_sq_le_div {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 1000) : ε ^ 2 ≤ ε / 1000 := by
  have hprod : 0 ≤ ε * (1 / 1000 - ε) :=
    mul_nonneg hε0 (sub_nonneg.mpr hε)
  nlinarith [hprod]

theorem first_explicit_margin {ε η σ ρ : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 1000)
    (hη : η ≤ etaJoin) (hσ : 10 * ε ≤ σ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ε ^ 2) :
    firstExponent η σ ρ ≤ targetExponent σ - ε / 2 := by
  have hηOne : η ≤ 1 := by
    norm_num [etaJoin] at hη ⊢
    linarith
  have hOneη : 0 ≤ 1 - η := by linarith
  have hσnonneg : 0 ≤ σ - 10 * ε := by linarith
  have hmain : 0 ≤ (σ - 10 * ε) * (1 - η) :=
    mul_nonneg hσnonneg hOneη
  have hρeta : η * ρ ≤ ρ := by
    nlinarith [mul_nonneg hρ0 (sub_nonneg.mpr hηOne)]
  have hεsq := epsilon_sq_le_div (le_of_lt hε0) hε
  norm_num [firstExponent, targetExponent, etaJoin] at hη ⊢
  nlinarith

theorem second_explicit_margin {ε η σ ρ : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 1000)
    (hηlo : etaLower - 10 * ε ≤ η) (hηhi : η ≤ etaJoin)
    (hσ : σ ≤ sigmaZero - 6 * ε)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ε ^ 2) :
    secondExponent η σ ρ ≤ targetExponent σ - 1 / 210 := by
  have hηhalf : 1 / 2 ≤ η := by
    norm_num [etaLower] at hηlo ⊢
    linarith
  have hσzero : σ ≤ sigmaZero := by linarith
  have himprove : 0 ≤ (4 * η - 2) * (sigmaZero - σ) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hσzero)
  have hρeta : η * ρ ≤ (5 / 6) * ρ :=
    mul_le_mul_of_nonneg_right (by simpa [etaJoin] using hηhi) hρ0
  have hεsq := epsilon_sq_le_div (le_of_lt hε0) hε
  have hρsmall : ρ ≤ 1 / 1000000 := by nlinarith
  norm_num [secondExponent, targetExponent, sigmaZero, etaJoin] at hηhi himprove hρeta hρsmall ⊢
  nlinarith

theorem third_explicit_margin {ε η σ ρ : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 1000)
    (hηlo : etaLower - 10 * ε ≤ η) (hηhi : η ≤ etaJoin)
    (hσ : σ ≤ sigmaZero - 6 * ε)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ε ^ 2) :
    thirdExponent η σ ρ ≤ targetExponent σ - ε / 2 := by
  have hηhalf : 1 / 2 ≤ η := by
    norm_num [etaLower] at hηlo ⊢
    linarith
  have himproveSigma :
      0 ≤ (4 * η - 2) * ((sigmaZero - 6 * ε) - σ) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hσ)
  have hcoef : 0 ≤ 8 / 5 - 4 * (sigmaZero - 6 * ε) := by
    norm_num [sigmaZero]
    linarith
  have himproveEta :
      0 ≤ (η - (etaLower - 10 * ε)) *
        (8 / 5 - 4 * (sigmaZero - 6 * ε)) :=
    mul_nonneg (sub_nonneg.mpr hηlo) hcoef
  have hρeta : η * ρ ≤ (5 / 6) * ρ :=
    mul_le_mul_of_nonneg_right (by simpa [etaJoin] using hηhi) hρ0
  have hεsq := epsilon_sq_le_div (le_of_lt hε0) hε
  norm_num [thirdExponent, targetExponent, sigmaZero, etaLower, etaJoin] at hηlo hηhi hσ himproveSigma hcoef himproveEta hρeta ⊢
  nlinarith

/-- All three explicit lower-range margins, packaged in the form used by the
subsequent density argument. -/
theorem explicit_lower_range_margins {ε η σ ρ : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 1000)
    (hηlo : etaLower - 10 * ε ≤ η) (hηhi : η ≤ etaJoin)
    (hσlo : 10 * ε ≤ σ) (hσhi : σ ≤ sigmaZero - 6 * ε)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ε ^ 2) :
    firstExponent η σ ρ ≤ targetExponent σ - ε / 2 ∧
      secondExponent η σ ρ ≤ targetExponent σ - 1 / 210 ∧
      thirdExponent η σ ρ ≤ targetExponent σ - ε / 2 := by
  exact ⟨first_explicit_margin hε0 hε hηhi hσlo hρ0 hρ,
    second_explicit_margin hε0 hε hηlo hηhi hσhi hρ0 hρ,
    third_explicit_margin hε0 hε hηlo hηhi hσhi hρ0 hρ⟩

end
end LowerRange

def lowerRangeExponentsModule : ProofModule :=
  { name := "Hybrid.LowerRangeExponents"
    paperLocation := "Proof of Lemma 4.3, range 9/11 - 10ε ≤ η ≤ 5/6"
    purpose :=
      "Prove the exact threshold identities and explicit exponent margins below T^(5/6)."
    dependsOn := ["Hybrid.NormalizeCoefficients"]
    status := .proved }

end Hybrid
end ExactSemiprimes
