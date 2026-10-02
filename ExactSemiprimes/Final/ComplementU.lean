import ExactSemiprimes.Extensions
import ExactSemiprimes.Final.SparseUniform
import ExactSemiprimes.Completion.ComplementOfU

/-!
# The complement of `𝒰` for general exponents

On the complement of the large-prime set the prime polynomial is small, so
it suffices to bound the mean square of the minorant polynomial.  This is
done exactly as in `Completion.ComplementOfU` ([MT23, Lemma 3.3], equation
(2.4), and the rough-pair sieve bound), but with the sieve bound supplied by
the labelled extension (E3), which is uniform in `a ≤ c - 1`, `c ≤ 2.1`.
-/

namespace ExactSemiprimes
namespace Final

open Filter Real MeasureTheory
open scoped BigOperators

noncomputable section

/-- The minorant mean square at one fixed scale, given the rough-pair sieve
inequality at that scale. -/
theorem minorant_meanSquare_of_sieveAt
    {Cmean Csieve εₘₐₓ X P ε T : ℝ} (hCmean : 0 < Cmean) (_hCsieve : 0 < Csieve)
    (hmeanBound : ∀ (N T : ℝ) (a : ℕ → ℂ), 1 ≤ N → 1 ≤ T →
      (∫ t in Set.Icc (-T) T,
          ‖matomakiTeravainenInitialDirichletPolynomial a N
              ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)) ≤
        Cmean *
          (T * (∑ n ∈ natOpenClosedInterval 0 N, ‖a n‖ ^ (2 : ℕ)) +
            T * matomakiTeravainenShiftedCorrelation a N T))
    (hequationTwoFour : ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∀ X : ℝ, 3 ≤ X → ∀ n : ℕ,
        2 * X ^ (1 / 2 : ℝ) ≤ (n : ℝ) → (n : ℝ) ≤ 3 * X →
          |matomakiTeravainenMinorant X ε n| ≤
            4 * (Real.log (3 * X) / Real.log (X ^ (2 / 11 : ℝ))) ^ (3 : ℕ) *
              matomakiTeravainenRoughIndicator n (X ^ (2 / 11 : ℝ)))
    (hX : 3 ≤ X) (hP : 0 < P) (hε : 0 < ε) (hεUpper : ε ≤ εₘₐₓ)
    (hN : 1 ≤ 4 * X / P) (hT : 1 ≤ T)
    (hsupportLower : 2 * X ^ (1 / 2 : ℝ) ≤ X / (2 * P))
    (hsupportUpper : 4 * X / P ≤ 3 * X)
    (hsieveAt :
      T * (∑ n ∈ natOpenClosedInterval 0 (4 * X / P),
            ‖matomakiTeravainenSectionFiveRoughCoefficient X P n‖ ^ (2 : ℕ)) +
          T * matomakiTeravainenShiftedCorrelation
            (matomakiTeravainenSectionFiveRoughCoefficient X P) (4 * X / P) T ≤
        Csieve * (T * P / (X * Real.log X) + 1 / (Real.log X) ^ (2 : ℕ))) :
    (∫ t in Set.Icc (-T) T,
        ‖Completion.perronMinorantPolynomial
            (matomakiTeravainenMinorant X ε) X P (onePlusIT t)‖ ^ (2 : ℕ)) ≤
      (Cmean * (5324 : ℝ) ^ (2 : ℕ) * Csieve) *
        (T * P / (X * Real.log X) + 1 / (Real.log X) ^ (2 : ℕ)) := by
  have hXpos : 0 < X := by linarith
  let N : ℝ := 4 * X / P
  let aminor : ℕ → ℂ := Completion.sectionFiveMinorantCoefficient X P ε
  let brough : ℕ → ℂ := Completion.sectionFiveRoughCoefficient X P
  have heq24 :
      ∀ ε' : ℝ, 0 < ε' → ε' ≤ εₘₐₓ →
        ∀ X' : ℝ, 3 ≤ X' → ∀ n : ℕ,
          2 * X' ^ (1 / 2 : ℝ) ≤ (n : ℝ) →
          (n : ℝ) ≤ 3 * X' →
            |matomakiTeravainenMinorant X' ε' n| ≤
              Completion.sectionFiveMinorantMajorant X' *
                matomakiTeravainenRoughIndicator n
                  (X' ^ (2 / 11 : ℝ)) := by
    intro ε' hε' hε'Upper X' hX' n hnLower hnUpper
    simpa only [Completion.sectionFiveMinorantMajorant] using
      hequationTwoFour ε' hε' hε'Upper X' hX' n hnLower hnUpper
  have hcoeffK : ∀ n : ℕ,
      ‖aminor n‖ ≤ Completion.sectionFiveMinorantMajorant X * ‖brough n‖ := by
    intro n
    exact Completion.sectionFiveMinorantCoefficient_norm_le_of_equationTwoFour
      hX hP hε hεUpper heq24 hsupportLower hsupportUpper n
  have hKle : Completion.sectionFiveMinorantMajorant X ≤ 5324 :=
    Completion.sectionFiveMinorantMajorant_le hX
  have hcoeff : ∀ n : ℕ, ‖aminor n‖ ≤ (5324 : ℝ) * ‖brough n‖ := by
    intro n
    exact (hcoeffK n).trans
      (mul_le_mul_of_nonneg_right hKle (norm_nonneg _))
  have henergy := Completion.coefficientEnergy_le (K := (5324 : ℝ))
    hcoeff (N := N)
  have hcorrelation := Completion.shiftedCorrelation_le (K := (5324 : ℝ))
    (by norm_num) hcoeff (N := N) (T := T)
  have hTnonneg : 0 ≤ T := zero_le_one.trans hT
  have hmeanApplied := hmeanBound N T aminor hN hT
  have hlineChange :
      (∫ t in Set.Icc (-T) T,
          ‖Completion.perronMinorantPolynomial
              (matomakiTeravainenMinorant X ε) X P
              (onePlusIT t)‖ ^ (2 : ℕ)) =
        ∫ t in Set.Icc (-T) T,
          ‖matomakiTeravainenInitialDirichletPolynomial aminor N
              ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ) := by
    apply integral_congr_ae
    filter_upwards with t
    rw [Completion.initialPolynomial_sectionFiveMinorantCoefficient_eq
      X P ε t hXpos hP]
  rw [hlineChange]
  have hrough : brough = matomakiTeravainenSectionFiveRoughCoefficient X P := rfl
  calc
    (∫ t in Set.Icc (-T) T,
        ‖matomakiTeravainenInitialDirichletPolynomial aminor N
            ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)) ≤
        Cmean *
          (T * (∑ n ∈ natOpenClosedInterval 0 N, ‖aminor n‖ ^ (2 : ℕ)) +
            T * matomakiTeravainenShiftedCorrelation aminor N T) := hmeanApplied
    _ ≤ Cmean *
        ((5324 : ℝ) ^ (2 : ℕ) *
          (T * (∑ n ∈ natOpenClosedInterval 0 N, ‖brough n‖ ^ (2 : ℕ)) +
            T * matomakiTeravainenShiftedCorrelation brough N T)) := by
      apply mul_le_mul_of_nonneg_left _ hCmean.le
      have h1 := mul_le_mul_of_nonneg_left henergy hTnonneg
      have h2 := mul_le_mul_of_nonneg_left hcorrelation hTnonneg
      nlinarith
    _ ≤ Cmean * ((5324 : ℝ) ^ (2 : ℕ) *
        (Csieve * (T * P / (X * Real.log X) + 1 / (Real.log X) ^ (2 : ℕ)))) := by
      apply mul_le_mul_of_nonneg_left _ hCmean.le
      apply mul_le_mul_of_nonneg_left hsieveAt
      positivity
    _ = (Cmean * (5324 : ℝ) ^ (2 : ℕ) * Csieve) *
          (T * P / (X * Real.log X) + 1 / (Real.log X) ^ (2 : ℕ)) := by ring

/-- **Complement of `𝒰`, general exponents.**  Uniformly for
`(log X) ≤ P ≤ (log X)^(c-1)` with `c ≤ 2.1` and
`X/(log X)^c ≤ T ≤ X`, the Perron product restricted to the small-prime
set at threshold `P^(-ε/20)` has mean square
`≪ P^(-ε/10) (T P/(X log X) + (log X)^(-2))`. -/
theorem complementU_uniform (inputs : ExternalInputs)
    (hsieve : UniformSectionFiveRoughSieveStatement) :
    ∃ εₘₐₓ C : ℝ, 0 < εₘₐₓ ∧ 0 < C ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (P c ε T : ℝ),
        Real.log (X : ℝ) ≤ P → P ≤ (Real.log (X : ℝ)) ^ (c - 1) →
        c ≤ 21 / 10 → 0 < ε → ε ≤ εₘₐₓ →
        (X : ℝ) / (Real.log (X : ℝ)) ^ c ≤ T → T ≤ (X : ℝ) →
        (∫ t in Completion.sectionFiveSmallPrimeSet (X : ℝ) P (ε / 2) T,
            ‖Completion.perronProduct (matomakiTeravainenMinorant (X : ℝ) ε)
                (X : ℝ) P t‖ ^ (2 : ℕ)) ≤
          C * P ^ (-ε / 10) *
            (T * P / ((X : ℝ) * Real.log (X : ℝ)) +
              1 / (Real.log (X : ℝ)) ^ (2 : ℕ)) := by
  obtain ⟨Cmean, hCmean, hmeanBound⟩ := inputs.matomakiTeravainenLemmaThreeThree
  obtain ⟨εₘₐₓ, hεₘₐₓ, heq24⟩ := inputs.matomakiTeravainenEquationTwoFour
  obtain ⟨Csieve, Xs, hCsieve, hXs, hsieveBound⟩ := hsieve
  refine ⟨εₘₐₓ, Cmean * (5324 : ℝ) ^ (2 : ℕ) * Csieve, hεₘₐₓ, by positivity, ?_⟩
  have hgeo := tendsto_natCast_atTop_atTop.eventually
    Completion.eventually_perronSupport_inside_equationTwoFour_range_wide
  have hT1 : ∀ᶠ X : ℕ in atTop, 1 ≤ (X : ℝ) / (Real.log (X : ℝ)) ^ (21 / 10 : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      Completion.eventually_one_le_sectionFive_minimumHeight
  have hXe : ∀ᶠ X : ℕ in atTop, Real.exp 1 < (X : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  filter_upwards [hgeo, hT1, hXe, eventually_ge_atTop ⌈Xs⌉₊] with
    X hgeoX hT1X hXeX hXsX
  intro P c ε T hPlo hPhi hc hε hεUpper hTlo hThi
  have hXs' : Xs ≤ (X : ℝ) := (Nat.le_ceil Xs).trans (by exact_mod_cast hXsX)
  have hX3 : (3 : ℝ) ≤ X := hXs.trans hXs'
  have hXpos : (0 : ℝ) < X := by linarith
  have hlog1 : 1 < Real.log (X : ℝ) := by
    rw [← Real.log_exp 1]; exact Real.log_lt_log (Real.exp_pos 1) hXeX
  have hPpos : 0 < P := by linarith
  set a := scaleExponent (X : ℝ) P with ha
  have hPa : P = (Real.log (X : ℝ)) ^ a := (rpow_scaleExponent hXeX hPpos).symm
  have ha1 : 1 ≤ a := le_scaleExponent_of_rpow_le hXeX hPpos (by rwa [Real.rpow_one])
  have hac : a ≤ c - 1 := scaleExponent_le_of_le_rpow hXeX hPpos hPhi
  have ha11 : a ≤ 11 / 10 := by linarith
  obtain ⟨_, hsupLo, hsupHi⟩ := hgeoX a ha1 ha11
  rw [← hPa] at hsupLo hsupHi
  have hlogc : (Real.log (X : ℝ)) ^ c ≤ (Real.log (X : ℝ)) ^ (21 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog1.le hc
  have hT : 1 ≤ T := by
    refine hT1X.trans (le_trans ?_ hTlo)
    exact div_le_div_of_nonneg_left hXpos.le (by positivity) hlogc
  have hN : 1 ≤ 4 * (X : ℝ) / P := by
    have h1 : (1 : ℝ) ≤ 2 * (X : ℝ) ^ (1 / 2 : ℝ) := by
      have : (1 : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
      linarith
    have h2 : (X : ℝ) / (2 * P) ≤ 4 * (X : ℝ) / P := by
      rw [div_le_div_iff₀ (by positivity) hPpos]; nlinarith
    linarith
  have hsieveAt := hsieveBound (X : ℝ) a c T hXs' ha1 hac hc hTlo hThi
  dsimp only at hsieveAt
  rw [← hPa] at hsieveAt
  have hmean := minorant_meanSquare_of_sieveAt hCmean hCsieve hmeanBound heq24 hX3
    hPpos hε hεUpper hN hT hsupLo hsupHi hsieveAt
  have hprod := Completion.sectionFiveSmallPrimeSet_integral_le_symmetricMeanSquare
    (weight := matomakiTeravainenMinorant (X : ℝ) ε) (ε := ε / 2) (T := T)
    hXpos.le hPpos (by linarith)
  have hexp : -(ε / 2) / 5 = -ε / 10 := by ring
  rw [hexp] at hprod
  calc _ ≤ P ^ (-ε / 10) * ∫ t in Set.Icc (-T) T,
          ‖Completion.perronMinorantPolynomial (matomakiTeravainenMinorant (X : ℝ) ε)
            (X : ℝ) P (onePlusIT t)‖ ^ (2 : ℕ) := hprod
    _ ≤ P ^ (-ε / 10) * ((Cmean * (5324 : ℝ) ^ (2 : ℕ) * Csieve) *
          (T * P / ((X : ℝ) * Real.log (X : ℝ)) + 1 / (Real.log (X : ℝ)) ^ (2 : ℕ))) :=
        mul_le_mul_of_nonneg_left hmean (Real.rpow_nonneg hPpos.le _)
    _ = _ := by ring

end

end Final
end ExactSemiprimes
