import ExactSemiprimes.Definitions

/-!
# Hybrid-density exponent check above length `T^(5/6)`

This file formalizes only the exponent arithmetic in the upper-length half of
the proof of Lemma 4.3.  It does not assert or invoke the Guth--Maynard
long-polynomial estimate.

The three definitions are the powers of `T` in the normalized estimate after
writing `N = T^η` and taking the large-value amplitude exponent
`varrho = 1 - σ - 2ρ`.  As in the paper, the last definition discards the
favourable factor `T^(-12ρ)`.
-/

namespace ExactSemiprimes
namespace Hybrid
namespace UpperRange

noncomputable section

/-- The critical large-value threshold `17/70`. -/
def sigmaZero : ℝ := 17 / 70

/-- The lower endpoint of the long-polynomial range. -/
def etaJoin : ℝ := 5 / 6

/-- Exponent of the first term in the normalized upper-range estimate. -/
def firstExponent (η σ ρ : ℝ) : ℝ := η * (2 * σ + 4 * ρ)

/-- Exponent of the second term in the normalized upper-range estimate. -/
def secondExponent (η σ ρ : ℝ) : ℝ :=
  1 / 2 + η * (-1 + 4 * σ + 8 * ρ)

/-- Exponent of the third term after discarding the favourable `T^(-12ρ)`. -/
def thirdExponent (η σ ρ : ℝ) : ℝ :=
  (9 - 30 * σ) / 5 + η * ((-14 + 60 * σ) / 5 + 24 * ρ)

/-- The target exponent in the density estimate. -/
def targetExponent (σ : ℝ) : ℝ := 2 * σ

/-! ## Exact identities and gap formulas at `σ = 17/70` -/

theorem target_at_sigmaZero : targetExponent sigmaZero = 17 / 35 := by
  norm_num [targetExponent, sigmaZero]

theorem first_at_sigmaZero (η : ℝ) :
    firstExponent η sigmaZero 0 = (17 / 35) * η := by
  norm_num [firstExponent, sigmaZero]
  ring

theorem second_at_sigmaZero (η : ℝ) :
    secondExponent η sigmaZero 0 = 1 / 2 - η / 35 := by
  norm_num [secondExponent, sigmaZero]
  ring

theorem third_at_sigmaZero (η : ℝ) :
    thirdExponent η sigmaZero 0 = (12 + 4 * η) / 35 := by
  norm_num [thirdExponent, sigmaZero]
  ring

theorem second_gap_formula (η : ℝ) :
    targetExponent sigmaZero - secondExponent η sigmaZero 0 =
      (2 * η - 1) / 70 := by
  norm_num [targetExponent, secondExponent, sigmaZero]
  ring

theorem third_gap_formula (η : ℝ) :
    targetExponent sigmaZero - thirdExponent η sigmaZero 0 =
      (5 - 4 * η) / 35 := by
  norm_num [targetExponent, thirdExponent, sigmaZero]
  ring

/-- At `η=5/6`, the second term again has the exact joining gap `1/105`. -/
theorem second_join_gap :
    targetExponent sigmaZero - secondExponent etaJoin sigmaZero 0 = 1 / 105 := by
  norm_num [targetExponent, secondExponent, etaJoin, sigmaZero]

/-- The smallest third-term gap on the closed nominal range occurs at `η=1`. -/
theorem third_endpoint_gap :
    targetExponent sigmaZero - thirdExponent 1 sigmaZero 0 = 1 / 35 := by
  norm_num [targetExponent, thirdExponent, sigmaZero]

/-! ## Uniform upper-range gaps at `σ = 17/70` -/

theorem second_uniform_gap {η : ℝ} (hη : etaJoin ≤ η) :
    secondExponent η sigmaZero 0 ≤ targetExponent sigmaZero - 1 / 105 := by
  norm_num [secondExponent, targetExponent, sigmaZero, etaJoin] at hη ⊢
  linarith

theorem third_uniform_gap {η : ℝ} (hη : η ≤ 1) :
    thirdExponent η sigmaZero 0 ≤ targetExponent sigmaZero - 1 / 35 := by
  norm_num [thirdExponent, targetExponent, sigmaZero] at hη ⊢
  linarith

/-! ## Explicit absorption of the `ε`- and `ρ`-losses

Here one may take `0 < ε ≤ 1/100` and `0 ≤ ρ ≤ ε²/4`.  Unlike the lower
range, lowering `σ` from `17/70` only improves the two nontrivial uniform
gaps.  The first term gets its saving from `η ≤ 1 - ε/10`.
-/

private theorem epsilon_sq_le_hundredth {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 100) : ε ^ 2 ≤ 1 / 10000 := by
  have hprod : 0 ≤ ε * (1 / 100 - ε) :=
    mul_nonneg hε0 (sub_nonneg.mpr hε)
  nlinarith [hprod]

/-- The normalized amplitude exponent `varrho = 1-σ-2ρ` lies in the legal
Guth--Maynard range. -/
theorem legal_amplitude_exponent {ε σ ρ : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100)
    (hσ : σ ≤ sigmaZero) (hρ : ρ ≤ ε ^ 2 / 4) :
    7 / 10 ≤ 1 - σ - 2 * ρ := by
  have hεsq := epsilon_sq_le_hundredth hε0 hε
  norm_num [sigmaZero] at hσ ⊢
  nlinarith

theorem first_explicit_margin {ε η σ ρ : ℝ}
    (hε0 : 0 < ε) (hη : η ≤ 1 - ε / 10)
    (hσ : 10 * ε ≤ σ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ε ^ 2 / 4) :
    firstExponent η σ ρ ≤ targetExponent σ - ε ^ 2 := by
  have hOneη : ε / 10 ≤ 1 - η := by linarith
  have hOneη0 : 0 ≤ 1 - η := by linarith
  have hσnonneg : 0 ≤ σ - 10 * ε := by linarith
  have hmain : 0 ≤ (σ - 10 * ε) * (1 - η) :=
    mul_nonneg hσnonneg hOneη0
  have hεmain : 0 ≤ ε * ((1 - η) - ε / 10) :=
    mul_nonneg (le_of_lt hε0) (sub_nonneg.mpr hOneη)
  have hηOne : η ≤ 1 := by linarith
  have hρeta : η * ρ ≤ ρ := by
    nlinarith [mul_nonneg hρ0 (sub_nonneg.mpr hηOne)]
  norm_num [firstExponent, targetExponent] at hη ⊢
  nlinarith

theorem second_explicit_margin {ε η σ ρ : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 100)
    (hηlo : etaJoin ≤ η) (hηhi : η ≤ 1 - ε / 10)
    (hσ : σ ≤ sigmaZero)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ε ^ 2 / 4) :
    secondExponent η σ ρ ≤ targetExponent σ - 1 / 210 := by
  have hηhalf : 1 / 2 ≤ η := by
    norm_num [etaJoin] at hηlo ⊢
    linarith
  have himprove : 0 ≤ (4 * η - 2) * (sigmaZero - σ) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hσ)
  have hηOne : η ≤ 1 := by linarith
  have hρeta : η * ρ ≤ ρ := by
    nlinarith [mul_nonneg hρ0 (sub_nonneg.mpr hηOne)]
  have hεsq := epsilon_sq_le_hundredth (le_of_lt hε0) hε
  have hρsmall : ρ ≤ 1 / 40000 := by nlinarith
  norm_num [secondExponent, targetExponent, sigmaZero, etaJoin] at hηlo himprove hρeta hρsmall ⊢
  nlinarith

theorem third_explicit_margin {ε η σ ρ : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 100)
    (hηlo : etaJoin ≤ η) (hηhi : η ≤ 1 - ε / 10)
    (hσ : σ ≤ sigmaZero)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ε ^ 2 / 4) :
    thirdExponent η σ ρ ≤ targetExponent σ - 1 / 70 := by
  have hηOne : η ≤ 1 := by linarith
  have hderivative : 2 ≤ 12 * η - 8 := by
    norm_num [etaJoin] at hηlo ⊢
    linarith
  have himprove : 0 ≤ (12 * η - 8) * (sigmaZero - σ) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr hσ)
  have hρeta : η * ρ ≤ ρ := by
    nlinarith [mul_nonneg hρ0 (sub_nonneg.mpr hηOne)]
  have hεsq := epsilon_sq_le_hundredth (le_of_lt hε0) hε
  have hρsmall : ρ ≤ 1 / 40000 := by nlinarith
  norm_num [thirdExponent, targetExponent, sigmaZero] at hηhi himprove hρeta hρsmall ⊢
  nlinarith

/-- All three explicit upper-range margins, packaged for the subsequent
density argument. -/
theorem explicit_upper_range_margins {ε η σ ρ : ℝ}
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 100)
    (hηlo : etaJoin ≤ η) (hηhi : η ≤ 1 - ε / 10)
    (hσlo : 10 * ε ≤ σ) (hσhi : σ ≤ sigmaZero)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ ε ^ 2 / 4) :
    firstExponent η σ ρ ≤ targetExponent σ - ε ^ 2 ∧
      secondExponent η σ ρ ≤ targetExponent σ - 1 / 210 ∧
      thirdExponent η σ ρ ≤ targetExponent σ - 1 / 70 := by
  exact ⟨first_explicit_margin hε0 hηhi hσlo hρ0 hρ,
    second_explicit_margin hε0 hε hηlo hηhi hσhi hρ0 hρ,
    third_explicit_margin hε0 hε hηlo hηhi hσhi hρ0 hρ⟩

end
end UpperRange

def upperRangeExponentsModule : ProofModule :=
  { name := "Hybrid.UpperRangeExponents"
    paperLocation := "Proof of Lemma 4.3, range 5/6 ≤ η ≤ 1 - ε/10"
    purpose :=
      "Prove the exact long-range identities and explicit exponent margins above T^(5/6)."
    dependsOn := ["Hybrid.NormalizeCoefficients"]
    status := .proved }

end Hybrid
end ExactSemiprimes
