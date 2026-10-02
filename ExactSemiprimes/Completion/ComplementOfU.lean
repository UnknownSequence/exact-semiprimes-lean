import ExactSemiprimes.Completion.PerronTarget
import ExactSemiprimes.Completion.RoughCoefficientTransfer

/-! # Dirichlet-polynomial estimate on the complement of U -/

namespace ExactSemiprimes
namespace Completion

open MeasureTheory

noncomputable section

/-! ## Exact remaining rough-pair sieve target -/

/-- The zero-line rough coefficient supported on the interval used in
Matomäki--Teräväinen's Section 5.  This is the majorant to which the
minorant coefficients are reduced before applying Lemma 3.3. -/
noncomputable def sectionFiveRoughCoefficient
    (X P₁ : ℝ) (n : ℕ) : ℂ :=
  matomakiTeravainenSectionFiveRoughCoefficient X P₁ n

/-- The coefficient vector which moves the minorant polynomial from the
line `Re(s)=1` to the zero line used in MT23, Lemma 3.3. -/
noncomputable def sectionFiveMinorantCoefficient
    (X P₁ ε : ℝ) (n : ℕ) : ℂ :=
  if n ∈ natOpenClosedInterval (X / (2 * P₁)) (4 * X / P₁) then
    ((matomakiTeravainenMinorant X ε n / (n : ℝ) : ℝ) : ℂ)
  else 0

/-- The literal factor in MT23, equation (2.4), after substituting
`z=X^(2/11)`. -/
noncomputable def sectionFiveMinorantMajorant (X : ℝ) : ℝ :=
  4 * (Real.log (3 * X) /
    Real.log (X ^ (2 / 11 : ℝ))) ^ (3 : ℕ)

/-- The roughness indicator is nonnegative. -/
theorem matomakiTeravainenRoughIndicator_nonneg (n : ℕ) (z : ℝ) :
    0 ≤ matomakiTeravainenRoughIndicator n z := by
  unfold matomakiTeravainenRoughIndicator
  split_ifs <;> norm_num

/-- The exact equation-(2.4) factor is nonnegative in the source range. -/
theorem sectionFiveMinorantMajorant_nonneg {X : ℝ} (hX : 3 ≤ X) :
    0 ≤ sectionFiveMinorantMajorant X := by
  have hXpos : 0 < X := by linarith
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hdenpos : 0 < Real.log (X ^ (2 / 11 : ℝ)) := by
    rw [Real.log_rpow hXpos]
    positivity
  unfold sectionFiveMinorantMajorant
  exact mul_nonneg (by norm_num)
    (pow_nonneg
      (div_nonneg (Real.log_nonneg (by nlinarith : 1 ≤ 3 * X)) hdenpos.le) 3)

/-- Equation (2.4) has an absolute numerical factor on the whole source
range.  Keeping this deduction internal is important: no `X`-dependent
loss is introduced into the subsequent uniform estimate. -/
theorem sectionFiveMinorantMajorant_le {X : ℝ} (hX : 3 ≤ X) :
    sectionFiveMinorantMajorant X ≤ 5324 := by
  have hXpos : 0 < X := by linarith
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hlogThree_le : Real.log 3 ≤ Real.log X := by
    exact Real.log_le_log (by norm_num) hX
  have hlogMul : Real.log (3 * X) = Real.log 3 + Real.log X := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hXpos.ne']
  have hnum : Real.log (3 * X) ≤ 2 * Real.log X := by
    rw [hlogMul]
    linarith
  have hden : Real.log (X ^ (2 / 11 : ℝ)) =
      (2 / 11 : ℝ) * Real.log X := by
    rw [Real.log_rpow hXpos]
  have hdenpos : 0 < Real.log (X ^ (2 / 11 : ℝ)) := by
    rw [hden]
    positivity
  have hratioNonneg : 0 ≤
      Real.log (3 * X) / Real.log (X ^ (2 / 11 : ℝ)) := by
    exact div_nonneg (Real.log_nonneg (by nlinarith : 1 ≤ 3 * X)) hdenpos.le
  have hratio :
      Real.log (3 * X) / Real.log (X ^ (2 / 11 : ℝ)) ≤ 11 := by
    apply (div_le_iff₀ hdenpos).2
    rw [hden]
    calc
      Real.log (3 * X) ≤ 2 * Real.log X := hnum
      _ = 11 * ((2 / 11 : ℝ) * Real.log X) := by ring
  unfold sectionFiveMinorantMajorant
  have hcubed := pow_le_pow_left₀ hratioNonneg hratio 3
  norm_num at hcubed ⊢
  linarith

/-- The line-change identity for one coefficient of the minorant
polynomial. -/
theorem sectionFiveMinorantCoefficient_term_identity
    {X P₁ ε t : ℝ} {n : ℕ}
    (hn : n ∈ natOpenClosedInterval (X / (2 * P₁)) (4 * X / P₁))
    (hnpos : 0 < n) :
    sectionFiveMinorantCoefficient X P₁ ε n *
        (n : ℂ) ^ (-((t : ℂ) * Complex.I)) =
      (matomakiTeravainenMinorant X ε n : ℂ) *
        (n : ℂ) ^ (-onePlusIT t) := by
  have hnzero : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hnpos)
  have hexponent :
      -onePlusIT t = (-1 : ℂ) + (-((t : ℂ) * Complex.I)) := by
    simp only [onePlusIT]
    ring
  simp only [sectionFiveMinorantCoefficient, hn, ↓reduceIte]
  rw [hexponent, Complex.cpow_add _ _ hnzero, Complex.cpow_neg_one]
  push_cast
  field_simp [hnzero]

/-- The initial zero-line polynomial with the reciprocal-weighted minorant
coefficients is exactly the Perron minorant polynomial on `Re(s)=1`. -/
theorem initialPolynomial_sectionFiveMinorantCoefficient_eq
    (X P₁ ε t : ℝ) (hX : 0 < X) (hP₁ : 0 < P₁) :
    matomakiTeravainenInitialDirichletPolynomial
        (sectionFiveMinorantCoefficient X P₁ ε) (4 * X / P₁)
        ((t : ℂ) * Complex.I) =
      perronMinorantPolynomial (matomakiTeravainenMinorant X ε)
        X P₁ (onePlusIT t) := by
  classical
  have hlower : 0 ≤ X / (2 * P₁) := by positivity
  have hupper : 0 ≤ 4 * X / P₁ := by positivity
  have hsubset :
      natOpenClosedInterval (X / (2 * P₁)) (4 * X / P₁) ⊆
        natOpenClosedInterval 0 (4 * X / P₁) := by
    intro n hn
    rw [mem_natOpenClosedInterval hlower hupper] at hn
    rw [mem_natOpenClosedInterval (by norm_num) hupper]
    exact ⟨lt_of_le_of_lt hlower hn.1, hn.2⟩
  simp only [matomakiTeravainenInitialDirichletPolynomial,
    perronMinorantPolynomial, dirichletPolynomial]
  rw [← Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro n hn
    have hnrange := (mem_natOpenClosedInterval hlower hupper).mp hn
    have hnpos : 0 < n := by exact_mod_cast (hlower.trans_lt hnrange.1)
    exact sectionFiveMinorantCoefficient_term_identity hn hnpos
  · intro n hnInitial hnNotSupport
    simp [sectionFiveMinorantCoefficient, hnNotSupport]

/-- Equation (2.4), together with inclusion of the Perron support in the
interval on which that equation is stated, gives the required pointwise
coefficient majorant.  The two geometric inequalities are kept explicit;
they are elementary and eventually hold for polylogarithmic `P₁`. -/
theorem sectionFiveMinorantCoefficient_norm_le_of_equationTwoFour
    {X P₁ ε εₘₐₓ : ℝ}
    (hX : 3 ≤ X) (hP₁ : 0 < P₁)
    (hε : 0 < ε) (hεmax : ε ≤ εₘₐₓ)
    (heq24 : ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∀ X : ℝ, 3 ≤ X → ∀ n : ℕ,
        2 * X ^ (1 / 2 : ℝ) ≤ (n : ℝ) → (n : ℝ) ≤ 3 * X →
          |matomakiTeravainenMinorant X ε n| ≤
            sectionFiveMinorantMajorant X *
              matomakiTeravainenRoughIndicator n
                (X ^ (2 / 11 : ℝ)))
    (hlower : 2 * X ^ (1 / 2 : ℝ) ≤ X / (2 * P₁))
    (hupper : 4 * X / P₁ ≤ 3 * X) :
    ∀ n : ℕ,
      ‖sectionFiveMinorantCoefficient X P₁ ε n‖ ≤
        sectionFiveMinorantMajorant X *
          ‖sectionFiveRoughCoefficient X P₁ n‖ := by
  intro n
  by_cases hn :
      n ∈ natOpenClosedInterval (X / (2 * P₁)) (4 * X / P₁)
  · have hXpos : 0 < X := by linarith
    have hlowerNonneg : 0 ≤ X / (2 * P₁) := by positivity
    have hupperNonneg : 0 ≤ 4 * X / P₁ := by positivity
    have hnrange := (mem_natOpenClosedInterval hlowerNonneg hupperNonneg).mp hn
    have hnLower : 2 * X ^ (1 / 2 : ℝ) ≤ (n : ℝ) :=
      hlower.trans hnrange.1.le
    have hnUpper : (n : ℝ) ≤ 3 * X := hnrange.2.trans hupper
    have hnposReal : 0 < (n : ℝ) :=
      hlowerNonneg.trans_lt hnrange.1
    have hpoint := heq24 ε hε hεmax X hX n hnLower hnUpper
    simp only [sectionFiveMinorantCoefficient, sectionFiveRoughCoefficient,
      matomakiTeravainenSectionFiveRoughCoefficient, hn, ↓reduceIte,
      Complex.norm_real, Real.norm_eq_abs]
    have hroughNonneg := matomakiTeravainenRoughIndicator_nonneg n
      (X ^ (2 / 11 : ℝ))
    rw [abs_div, abs_of_pos hnposReal]
    rw [abs_div, abs_of_nonneg hroughNonneg, abs_of_pos hnposReal]
    calc
      |matomakiTeravainenMinorant X ε n| / (n : ℝ) ≤
          (sectionFiveMinorantMajorant X *
            matomakiTeravainenRoughIndicator n
              (X ^ (2 / 11 : ℝ))) / (n : ℝ) :=
        div_le_div_of_nonneg_right hpoint hnposReal.le
      _ = sectionFiveMinorantMajorant X *
          (matomakiTeravainenRoughIndicator n
            (X ^ (2 / 11 : ℝ)) / (n : ℝ)) := by ring
  · simp [sectionFiveMinorantCoefficient, sectionFiveRoughCoefficient,
      matomakiTeravainenSectionFiveRoughCoefficient, hn]

/-- The precise uniform sieve estimate still required after the source
audit.  It contains both the diagonal energy and the shifted rough-pair
correlations in the normalization accepted by the already typed MT23
Lemma 3.3.  IK04 Theorem 6.7 is a fixed prime-tuple theorem and does not
prove this statement directly. -/
def SectionFiveRoughSieveStatement : Prop :=
  ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧
    ∀ X alpha T : ℝ, X₀ ≤ X →
      let c : ℝ := 21 / 10
      let h : ℝ := (Real.log X) ^ c
      let P₁ : ℝ := (Real.log X) ^ alpha
      let N : ℝ := 4 * X / P₁
      c - 1 - 1 / 10000 ≤ alpha → alpha ≤ c - 1 →
      X / h ≤ T → T ≤ X →
      let b := sectionFiveRoughCoefficient X P₁
      T * (∑ n ∈ natOpenClosedInterval 0 N,
              ‖b n‖ ^ (2 : ℕ)) +
          T * matomakiTeravainenShiftedCorrelation b N T ≤
        C *
          (T * P₁ / (X * Real.log X) +
            1 / (Real.log X) ^ (2 : ℕ))

/-- The exact displayed rough-pair estimate in MT23 Section 5 supplies the
local interface without strengthening the merely analogous IK04 prime-tuple
theorem. -/
theorem sectionFiveRoughSieve_of_matomakiTeravainenSectionFive
    (hsource : MatomakiTeravainenSectionFiveRoughSieveStatement) :
    SectionFiveRoughSieveStatement := by
  exact hsource

/-- Combining MT23 Lemma 3.3 with the displayed Section 5 rough-pair sieve
bound gives the complete zero-line mean square used on the complement of
`U`.  The elementary lower bounds `1 ≤ N,T` are kept explicit so this
theorem introduces no hidden starting-scale claim. -/
theorem sectionFiveRough_meanSquare_of_sources
    (hmean : MatomakiTeravainenLemmaThreeThreeStatement)
    (hsieve : MatomakiTeravainenSectionFiveRoughSieveStatement) :
    ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧
      ∀ X alpha T : ℝ, X₀ ≤ X →
        let c : ℝ := 21 / 10
        let h : ℝ := (Real.log X) ^ c
        let P₁ : ℝ := (Real.log X) ^ alpha
        let N : ℝ := 4 * X / P₁
        c - 1 - 1 / 10000 ≤ alpha → alpha ≤ c - 1 →
        X / h ≤ T → T ≤ X →
        1 ≤ N → 1 ≤ T →
        let b := sectionFiveRoughCoefficient X P₁
        (∫ t in Set.Icc (-T) T,
            ‖matomakiTeravainenInitialDirichletPolynomial b N
                ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)) ≤
          C *
            (T * P₁ / (X * Real.log X) +
              1 / (Real.log X) ^ (2 : ℕ)) := by
  obtain ⟨Cmean, hCmean, hmean⟩ := hmean
  obtain ⟨Csieve, X₀, hCsieve, hX₀, hsieve⟩ := hsieve
  refine ⟨Cmean * Csieve, X₀, mul_pos hCmean hCsieve, hX₀, ?_⟩
  intro X alpha T hX
  dsimp only
  intro halphaLower halphaUpper hTLower hTUpper hN hT
  let P₁ : ℝ := Real.log X ^ alpha
  let N : ℝ := 4 * X / P₁
  let b := sectionFiveRoughCoefficient X P₁
  have hsieveBound := hsieve X alpha T hX halphaLower halphaUpper
    hTLower hTUpper
  have hmeanBound := hmean N T b hN hT
  dsimp only [P₁, N, b] at hsieveBound hmeanBound ⊢
  calc
    (∫ t in Set.Icc (-T) T,
        ‖matomakiTeravainenInitialDirichletPolynomial
            (sectionFiveRoughCoefficient X (Real.log X ^ alpha))
            (4 * X / Real.log X ^ alpha)
            ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)) ≤
        Cmean *
          (T * (∑ n ∈ natOpenClosedInterval 0
                  (4 * X / Real.log X ^ alpha),
                ‖sectionFiveRoughCoefficient X
                    (Real.log X ^ alpha) n‖ ^ (2 : ℕ)) +
            T * matomakiTeravainenShiftedCorrelation
              (sectionFiveRoughCoefficient X (Real.log X ^ alpha))
              (4 * X / Real.log X ^ alpha) T) := hmeanBound
    _ ≤ Cmean *
        (Csieve *
          (T * Real.log X ^ alpha / (X * Real.log X) +
            1 / Real.log X ^ (2 : ℕ))) := by
      exact mul_le_mul_of_nonneg_left hsieveBound hCmean.le
    _ = (Cmean * Csieve) *
          (T * Real.log X ^ alpha / (X * Real.log X) +
            1 / Real.log X ^ (2 : ℕ)) := by ring

/-- Convenience form from the project's explicit assumption bundle. -/
theorem sectionFiveRough_meanSquare_of_inputs (inputs : ExternalInputs) :
    ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧
      ∀ X alpha T : ℝ, X₀ ≤ X →
        let c : ℝ := 21 / 10
        let h : ℝ := (Real.log X) ^ c
        let P₁ : ℝ := (Real.log X) ^ alpha
        let N : ℝ := 4 * X / P₁
        c - 1 - 1 / 10000 ≤ alpha → alpha ≤ c - 1 →
        X / h ≤ T → T ≤ X →
        1 ≤ N → 1 ≤ T →
        let b := sectionFiveRoughCoefficient X P₁
        (∫ t in Set.Icc (-T) T,
            ‖matomakiTeravainenInitialDirichletPolynomial b N
                ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)) ≤
          C *
            (T * P₁ / (X * Real.log X) +
              1 / (Real.log X) ^ (2 : ℕ)) :=
  sectionFiveRough_meanSquare_of_sources
    inputs.matomakiTeravainenLemmaThreeThree
    inputs.matomakiTeravainenSectionFiveRoughSieve

/-! ## The actual minorant mean square in the printed source range -/

/-- Uniformly over the compact exponent window printed in MT23, the
polylogarithmic Perron support is eventually contained in the interval on
which equation (2.4) is stated. -/
theorem eventually_sectionFiveSupport_inside_equationTwoFour_range :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ alpha : ℝ,
        (21 / 10 : ℝ) - 1 - 1 / 10000 ≤ alpha →
        alpha ≤ (21 / 10 : ℝ) - 1 →
        let P₁ : ℝ := (Real.log X) ^ alpha
        0 < P₁ ∧
          2 * X ^ (1 / 2 : ℝ) ≤ X / (2 * P₁) ∧
          4 * X / P₁ ≤ 3 * X := by
  have hsmall : ∀ᶠ X : ℝ in Filter.atTop,
      (Real.log X) ^ (11 / 10 : ℝ) ≤
        (1 / 4 : ℝ) * X ^ (1 / 2 : ℝ) := by
    have hlittle := Asymptotics.isLittleO_iff.1
      (isLittleO_log_rpow_rpow_atTop (11 / 10 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 2))
      (by norm_num : (0 : ℝ) < 1 / 4)
    filter_upwards [hlittle, Filter.eventually_gt_atTop (1 : ℝ)] with X hX hXone
    have hlogNonneg : 0 ≤ Real.log X := Real.log_nonneg hXone.le
    have hXnonneg : 0 ≤ X := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hlogNonneg _),
      Real.norm_of_nonneg (Real.rpow_nonneg hXnonneg _)] at hX
    exact hX
  filter_upwards [hsmall,
    Filter.eventually_ge_atTop (Real.exp 2)] with X hsmallX hX
  intro alpha halphaLower halphaUpper
  have hXpos : 0 < X := (Real.exp_pos 2).trans_le hX
  have hlogXtwo : 2 ≤ Real.log X := by
    rw [← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos 2) hX
  have hlogXone : 1 ≤ Real.log X := by linarith
  have halphaOne : 1 ≤ alpha := by
    norm_num at halphaLower ⊢
    linarith
  have halphaUpper' : alpha ≤ 11 / 10 := by
    norm_num at halphaUpper ⊢
    linarith
  have hP₁pos : 0 < Real.log X ^ alpha :=
    Real.rpow_pos_of_pos (by linarith) alpha
  have hP₁lower : 4 / 3 ≤ Real.log X ^ alpha := by
    calc
      (4 / 3 : ℝ) ≤ Real.log X := by linarith
      _ = Real.log X ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ Real.log X ^ alpha :=
        Real.rpow_le_rpow_of_exponent_le hlogXone halphaOne
  have hP₁upper : Real.log X ^ alpha ≤
      Real.log X ^ (11 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlogXone halphaUpper'
  have hfourP₁ : 4 * Real.log X ^ alpha ≤ X ^ (1 / 2 : ℝ) := by
    calc
      4 * Real.log X ^ alpha ≤
          4 * Real.log X ^ (11 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hP₁upper (by norm_num)
      _ ≤ 4 * ((1 / 4 : ℝ) * X ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsmallX (by norm_num)
      _ = X ^ (1 / 2 : ℝ) := by ring
  refine ⟨hP₁pos, ?_, ?_⟩
  · apply (le_div_iff₀ (mul_pos (by norm_num) hP₁pos)).2
    calc
      2 * X ^ (1 / 2 : ℝ) * (2 * Real.log X ^ alpha) =
          (4 * Real.log X ^ alpha) * X ^ (1 / 2 : ℝ) := by ring
      _ ≤ X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hfourP₁
          (Real.rpow_nonneg hXpos.le _)
      _ = X := by
        rw [← Real.rpow_add hXpos]
        norm_num
  · apply (div_le_iff₀ hP₁pos).2
    have hmul := mul_le_mul_of_nonneg_left hP₁lower
      (show 0 ≤ 3 * X by positivity)
    nlinarith

/-- Combining equation (2.4), Lemma 3.3, and the displayed rough-pair
sieve estimate proves the mean square for the actual minorant polynomial.
The two support-inclusion inequalities are exposed rather than hidden; they
are the elementary facts that the polylogarithmic Perron support lies inside
`[2*sqrt X,3X]`. -/
theorem sectionFiveMinorant_meanSquare_of_sources
    (hmean : MatomakiTeravainenLemmaThreeThreeStatement)
    (hsieve : MatomakiTeravainenSectionFiveRoughSieveStatement)
    (hequationTwoFour : MatomakiTeravainenEquationTwoFourStatement) :
    ∃ εₘₐₓ C X₀ : ℝ,
      0 < εₘₐₓ ∧ 0 < C ∧ 3 ≤ X₀ ∧
      ∀ X alpha ε T : ℝ, X₀ ≤ X →
        let c : ℝ := 21 / 10
        let h : ℝ := (Real.log X) ^ c
        let P₁ : ℝ := (Real.log X) ^ alpha
        let N : ℝ := 4 * X / P₁
        0 < ε → ε ≤ εₘₐₓ →
        c - 1 - 1 / 10000 ≤ alpha → alpha ≤ c - 1 →
        X / h ≤ T → T ≤ X →
        1 ≤ N → 1 ≤ T →
        2 * X ^ (1 / 2 : ℝ) ≤ X / (2 * P₁) →
        4 * X / P₁ ≤ 3 * X →
        (∫ t in Set.Icc (-T) T,
            ‖perronMinorantPolynomial
                (matomakiTeravainenMinorant X ε) X P₁
                (onePlusIT t)‖ ^ (2 : ℕ)) ≤
          C *
            (T * P₁ / (X * Real.log X) +
              1 / (Real.log X) ^ (2 : ℕ)) := by
  obtain ⟨Cmean, hCmean, hmeanBound⟩ := hmean
  obtain ⟨Csieve, X₀, hCsieve, hX₀, hsieveBound⟩ := hsieve
  obtain ⟨εₘₐₓ, hεₘₐₓ, hequationTwoFour⟩ := hequationTwoFour
  refine ⟨εₘₐₓ, Cmean * (5324 : ℝ) ^ (2 : ℕ) * Csieve, X₀,
    hεₘₐₓ, mul_pos (mul_pos hCmean (sq_pos_of_pos (by norm_num))) hCsieve,
    hX₀, ?_⟩
  intro X alpha ε T hX
  dsimp only
  intro hε hεUpper halphaLower halphaUpper hTLower hTUpper hN hT
    hsupportLower hsupportUpper
  have hXthree : 3 ≤ X := hX₀.trans hX
  have hXpos : 0 < X := by linarith
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hP₁pos : 0 < Real.log X ^ alpha :=
    Real.rpow_pos_of_pos hlogXpos alpha
  let P₁ : ℝ := Real.log X ^ alpha
  let N : ℝ := 4 * X / P₁
  let aminor : ℕ → ℂ := sectionFiveMinorantCoefficient X P₁ ε
  let brough : ℕ → ℂ := sectionFiveRoughCoefficient X P₁
  have heq24 :
      ∀ ε' : ℝ, 0 < ε' → ε' ≤ εₘₐₓ →
        ∀ X' : ℝ, 3 ≤ X' → ∀ n : ℕ,
          2 * X' ^ (1 / 2 : ℝ) ≤ (n : ℝ) →
          (n : ℝ) ≤ 3 * X' →
            |matomakiTeravainenMinorant X' ε' n| ≤
              sectionFiveMinorantMajorant X' *
                matomakiTeravainenRoughIndicator n
                  (X' ^ (2 / 11 : ℝ)) := by
    intro ε' hε' hε'Upper X' hX' n hnLower hnUpper
    simpa only [sectionFiveMinorantMajorant] using
      hequationTwoFour ε' hε' hε'Upper X' hX' n hnLower hnUpper
  have hcoeffK : ∀ n : ℕ,
      ‖aminor n‖ ≤ sectionFiveMinorantMajorant X * ‖brough n‖ := by
    intro n
    exact sectionFiveMinorantCoefficient_norm_le_of_equationTwoFour
      hXthree hP₁pos hε hεUpper heq24 hsupportLower hsupportUpper n
  have hKle : sectionFiveMinorantMajorant X ≤ 5324 :=
    sectionFiveMinorantMajorant_le hXthree
  have hcoeff : ∀ n : ℕ, ‖aminor n‖ ≤ (5324 : ℝ) * ‖brough n‖ := by
    intro n
    exact (hcoeffK n).trans
      (mul_le_mul_of_nonneg_right hKle (norm_nonneg _))
  have henergy := coefficientEnergy_le (K := (5324 : ℝ))
    hcoeff (N := N)
  have hcorrelation := shiftedCorrelation_le (K := (5324 : ℝ))
    (by norm_num) hcoeff (N := N) (T := T)
  have hTnonneg : 0 ≤ T := zero_le_one.trans hT
  have hmeanApplied := hmeanBound N T aminor hN hT
  have hsieveApplied := hsieveBound X alpha T hX halphaLower
    halphaUpper hTLower hTUpper
  have hlineChange :
      (∫ t in Set.Icc (-T) T,
          ‖perronMinorantPolynomial
              (matomakiTeravainenMinorant X ε) X P₁
              (onePlusIT t)‖ ^ (2 : ℕ)) =
        ∫ t in Set.Icc (-T) T,
          ‖matomakiTeravainenInitialDirichletPolynomial aminor N
              ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ) := by
    apply integral_congr_ae
    filter_upwards with t
    rw [initialPolynomial_sectionFiveMinorantCoefficient_eq
      X P₁ ε t hXpos hP₁pos]
  dsimp only [P₁, N, aminor, brough] at hmeanApplied henergy hcorrelation
  dsimp only [P₁, N, aminor, brough] at hsieveApplied hlineChange
  rw [hlineChange]
  calc
    (∫ t in Set.Icc (-T) T,
        ‖matomakiTeravainenInitialDirichletPolynomial
            (sectionFiveMinorantCoefficient X (Real.log X ^ alpha) ε)
            (4 * X / Real.log X ^ alpha)
            ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)) ≤
        Cmean *
          (T * (∑ n ∈ natOpenClosedInterval 0
                (4 * X / Real.log X ^ alpha),
              ‖sectionFiveMinorantCoefficient X
                  (Real.log X ^ alpha) ε n‖ ^ (2 : ℕ)) +
            T * matomakiTeravainenShiftedCorrelation
              (sectionFiveMinorantCoefficient X (Real.log X ^ alpha) ε)
              (4 * X / Real.log X ^ alpha) T) := hmeanApplied
    _ ≤ Cmean *
        ((5324 : ℝ) ^ (2 : ℕ) *
          (T * (∑ n ∈ natOpenClosedInterval 0
                (4 * X / Real.log X ^ alpha),
              ‖sectionFiveRoughCoefficient X
                  (Real.log X ^ alpha) n‖ ^ (2 : ℕ)) +
            T * matomakiTeravainenShiftedCorrelation
              (sectionFiveRoughCoefficient X (Real.log X ^ alpha))
              (4 * X / Real.log X ^ alpha) T)) := by
      apply mul_le_mul_of_nonneg_left _ hCmean.le
      calc
        T * (∑ n ∈ natOpenClosedInterval 0
              (4 * X / Real.log X ^ alpha),
            ‖sectionFiveMinorantCoefficient X
                (Real.log X ^ alpha) ε n‖ ^ (2 : ℕ)) +
            T * matomakiTeravainenShiftedCorrelation
              (sectionFiveMinorantCoefficient X (Real.log X ^ alpha) ε)
              (4 * X / Real.log X ^ alpha) T ≤
          T * ((5324 : ℝ) ^ (2 : ℕ) *
              ∑ n ∈ natOpenClosedInterval 0
                (4 * X / Real.log X ^ alpha),
              ‖sectionFiveRoughCoefficient X
                  (Real.log X ^ alpha) n‖ ^ (2 : ℕ)) +
            T * ((5324 : ℝ) ^ (2 : ℕ) *
              matomakiTeravainenShiftedCorrelation
                (sectionFiveRoughCoefficient X (Real.log X ^ alpha))
                (4 * X / Real.log X ^ alpha) T) :=
          add_le_add
            (mul_le_mul_of_nonneg_left henergy hTnonneg)
            (mul_le_mul_of_nonneg_left hcorrelation hTnonneg)
        _ = (5324 : ℝ) ^ (2 : ℕ) *
          (T * (∑ n ∈ natOpenClosedInterval 0
                (4 * X / Real.log X ^ alpha),
              ‖sectionFiveRoughCoefficient X
                  (Real.log X ^ alpha) n‖ ^ (2 : ℕ)) +
            T * matomakiTeravainenShiftedCorrelation
              (sectionFiveRoughCoefficient X (Real.log X ^ alpha))
              (4 * X / Real.log X ^ alpha) T) := by ring
    _ ≤ Cmean * ((5324 : ℝ) ^ (2 : ℕ) *
        (Csieve *
          (T * Real.log X ^ alpha / (X * Real.log X) +
            1 / Real.log X ^ (2 : ℕ)))) := by
      apply mul_le_mul_of_nonneg_left _ hCmean.le
      apply mul_le_mul_of_nonneg_left hsieveApplied
      positivity
    _ = (Cmean * (5324 : ℝ) ^ (2 : ℕ) * Csieve) *
          (T * Real.log X ^ alpha / (X * Real.log X) +
            1 / Real.log X ^ (2 : ℕ)) := by ring

/-- Convenience form of the actual source-range minorant mean square from
the project's explicit input bundle. -/
theorem sectionFiveMinorant_meanSquare_of_inputs (inputs : ExternalInputs) :
    ∃ εₘₐₓ C X₀ : ℝ,
      0 < εₘₐₓ ∧ 0 < C ∧ 3 ≤ X₀ ∧
      ∀ X alpha ε T : ℝ, X₀ ≤ X →
        let c : ℝ := 21 / 10
        let h : ℝ := (Real.log X) ^ c
        let P₁ : ℝ := (Real.log X) ^ alpha
        let N : ℝ := 4 * X / P₁
        0 < ε → ε ≤ εₘₐₓ →
        c - 1 - 1 / 10000 ≤ alpha → alpha ≤ c - 1 →
        X / h ≤ T → T ≤ X →
        1 ≤ N → 1 ≤ T →
        2 * X ^ (1 / 2 : ℝ) ≤ X / (2 * P₁) →
        4 * X / P₁ ≤ 3 * X →
        (∫ t in Set.Icc (-T) T,
            ‖perronMinorantPolynomial
                (matomakiTeravainenMinorant X ε) X P₁
                (onePlusIT t)‖ ^ (2 : ℕ)) ≤
          C *
            (T * P₁ / (X * Real.log X) +
              1 / (Real.log X) ^ (2 : ℕ)) :=
  sectionFiveMinorant_meanSquare_of_sources
    inputs.matomakiTeravainenLemmaThreeThree
    inputs.matomakiTeravainenSectionFiveRoughSieve
    inputs.matomakiTeravainenEquationTwoFour

/-- The remaining elementary height conditions in Lemma 3.3 also hold
eventually at the printed scale `h=(log X)^(2.1)`. -/
theorem eventually_one_le_sectionFive_minimumHeight :
    ∀ᶠ X : ℝ in Filter.atTop,
      1 ≤ X / (Real.log X) ^ (21 / 10 : ℝ) := by
  have hsmall := Asymptotics.isLittleO_iff.1
    (isLittleO_log_rpow_rpow_atTop (21 / 10 : ℝ)
      (by norm_num : (0 : ℝ) < 1))
    zero_lt_one
  filter_upwards [hsmall, Filter.eventually_gt_atTop (1 : ℝ)] with X hX hXone
  have hlogNonneg : 0 ≤ Real.log X := Real.log_nonneg hXone.le
  have hXnonneg : 0 ≤ X := by linarith
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlogNonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg hXnonneg _), one_mul,
    Real.rpow_one] at hX
  exact (one_le_div (Real.rpow_pos_of_pos (Real.log_pos hXone) _)).2 hX

/-- Source-faithful, assumption-free packaging of all elementary support and
height conditions.  This is the complete minorant mean-square estimate in
the exact parameter window printed in MT23. -/
theorem sectionFiveMinorant_meanSquare_printedRange_of_sources
    (hmean : MatomakiTeravainenLemmaThreeThreeStatement)
    (hsieve : MatomakiTeravainenSectionFiveRoughSieveStatement)
    (hequationTwoFour : MatomakiTeravainenEquationTwoFourStatement) :
    ∃ εₘₐₓ C X₀ : ℝ,
      0 < εₘₐₓ ∧ 0 < C ∧ 3 ≤ X₀ ∧
      ∀ X alpha ε T : ℝ, X₀ ≤ X →
        let c : ℝ := 21 / 10
        let h : ℝ := (Real.log X) ^ c
        let P₁ : ℝ := (Real.log X) ^ alpha
        0 < ε → ε ≤ εₘₐₓ →
        c - 1 - 1 / 10000 ≤ alpha → alpha ≤ c - 1 →
        X / h ≤ T → T ≤ X →
        (∫ t in Set.Icc (-T) T,
            ‖perronMinorantPolynomial
                (matomakiTeravainenMinorant X ε) X P₁
                (onePlusIT t)‖ ^ (2 : ℕ)) ≤
          C *
            (T * P₁ / (X * Real.log X) +
              1 / (Real.log X) ^ (2 : ℕ)) := by
  obtain ⟨εₘₐₓ, C, Xsource, hεₘₐₓ, hC, hXsource, hsource⟩ :=
    sectionFiveMinorant_meanSquare_of_sources hmean hsieve hequationTwoFour
  obtain ⟨Xgeometry, hgeometry⟩ := Filter.eventually_atTop.1
    (eventually_sectionFiveSupport_inside_equationTwoFour_range.and
      eventually_one_le_sectionFive_minimumHeight)
  let X₀ : ℝ := max Xsource Xgeometry
  refine ⟨εₘₐₓ, C, X₀, hεₘₐₓ, hC,
    hXsource.trans (le_max_left _ _), ?_⟩
  intro X alpha ε T hX
  dsimp only
  intro hε hεUpper halphaLower halphaUpper hTLower hTUpper
  have hXsource' : Xsource ≤ X := (le_max_left _ _).trans hX
  have hXgeometry' : Xgeometry ≤ X := (le_max_right _ _).trans hX
  obtain ⟨hsupport, hminimumHeight⟩ := hgeometry X hXgeometry'
  obtain ⟨hP₁pos, hsupportLower, hsupportUpper⟩ :=
    hsupport alpha halphaLower halphaUpper
  have hT : 1 ≤ T := hminimumHeight.trans hTLower
  have hXthree : 3 ≤ X := hXsource.trans hXsource'
  have hXone : 1 ≤ X := by linarith
  have hsqrtOne : 1 ≤ X ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow hXone (by norm_num)
  have hN : 1 ≤ 4 * X / Real.log X ^ alpha := by
    have hscaled := mul_le_mul_of_nonneg_left hsupportLower
      (by norm_num : (0 : ℝ) ≤ 8)
    have hidentity :
        8 * (X / (2 * Real.log X ^ alpha)) =
          4 * X / Real.log X ^ alpha := by ring
    rw [hidentity] at hscaled
    nlinarith
  exact hsource X alpha ε T hXsource' hε hεUpper halphaLower
    halphaUpper hTLower hTUpper hN hT hsupportLower hsupportUpper

/-- Printed-range convenience form from the explicit input bundle. -/
theorem sectionFiveMinorant_meanSquare_printedRange_of_inputs
    (inputs : ExternalInputs) :
    ∃ εₘₐₓ C X₀ : ℝ,
      0 < εₘₐₓ ∧ 0 < C ∧ 3 ≤ X₀ ∧
      ∀ X alpha ε T : ℝ, X₀ ≤ X →
        let c : ℝ := 21 / 10
        let h : ℝ := (Real.log X) ^ c
        let P₁ : ℝ := (Real.log X) ^ alpha
        0 < ε → ε ≤ εₘₐₓ →
        c - 1 - 1 / 10000 ≤ alpha → alpha ≤ c - 1 →
        X / h ≤ T → T ≤ X →
        (∫ t in Set.Icc (-T) T,
            ‖perronMinorantPolynomial
                (matomakiTeravainenMinorant X ε) X P₁
                (onePlusIT t)‖ ^ (2 : ℕ)) ≤
          C *
            (T * P₁ / (X * Real.log X) +
              1 / (Real.log X) ^ (2 : ℕ)) :=
  sectionFiveMinorant_meanSquare_printedRange_of_sources
    inputs.matomakiTeravainenLemmaThreeThree
    inputs.matomakiTeravainenSectionFiveRoughSieve
    inputs.matomakiTeravainenEquationTwoFour

/-- A uniformly small factor can be pulled out of the squared norm of a
product. -/
theorem norm_mul_sq_le_of_norm_le
    {A B : ℂ} {bound : ℝ} (hbound : 0 ≤ bound)
    (hA : ‖A‖ ≤ bound) :
    ‖A * B‖ ^ 2 ≤ bound ^ 2 * ‖B‖ ^ 2 := by
  have hprod : ‖A‖ * ‖B‖ ≤ bound * ‖B‖ :=
    mul_le_mul_of_nonneg_right hA (norm_nonneg B)
  have hsq : (‖A‖ * ‖B‖) ^ 2 ≤ (bound * ‖B‖) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (norm_nonneg A) (norm_nonneg B))
      (mul_nonneg hbound (norm_nonneg B))).2 hprod
  simpa [norm_mul, mul_pow] using hsq

/-- Integrated form of the small-factor estimate on a measurable set.  The
integrability assumptions are precisely those needed by Mathlib's monotone
integral theorem and are discharged later for finite Dirichlet polynomials. -/
theorem setIntegral_norm_mul_sq_le_of_norm_le
    {E : Set ℝ} (hE : MeasurableSet E)
    {A B : ℝ → ℂ} {bound : ℝ} (hbound : 0 ≤ bound)
    (hA : ∀ t ∈ E, ‖A t‖ ≤ bound)
    (hleft : IntegrableOn (fun t ↦ ‖A t * B t‖ ^ 2) E)
    (hright : IntegrableOn (fun t ↦ bound ^ 2 * ‖B t‖ ^ 2) E) :
    (∫ t in E, ‖A t * B t‖ ^ 2) ≤
      bound ^ 2 * ∫ t in E, ‖B t‖ ^ 2 := by
  calc
    (∫ t in E, ‖A t * B t‖ ^ 2) ≤
        ∫ t in E, bound ^ 2 * ‖B t‖ ^ 2 :=
      setIntegral_mono_on hleft hright hE fun t ht ↦
        norm_mul_sq_le_of_norm_le hbound (hA t ht)
    _ = bound ^ 2 * ∫ t in E, ‖B t‖ ^ 2 := by
      rw [integral_const_mul]

/-- Squaring the paper's small-prime-polynomial threshold gives exactly the
factor `P^(-ε/5)`. -/
theorem smallPrimeThreshold_sq {P ε : ℝ} (hP : 0 < P) :
    (P ^ (-ε / 10)) ^ (2 : ℕ) = P ^ (-ε / 5) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hP.le]
  congr 1
  ring

/-- Pointwise complement-of-`U` estimate in the paper's normalization. -/
theorem norm_product_sq_le_smallPrimeFactor
    {P ε : ℝ} (hP : 0 < P) {A B : ℂ}
    (hsmall : ‖A‖ ≤ P ^ (-ε / 10)) :
    ‖A * B‖ ^ 2 ≤ P ^ (-ε / 5) * ‖B‖ ^ 2 := by
  have h := norm_mul_sq_le_of_norm_le
    (A := A) (B := B) (Real.rpow_nonneg hP.le _) hsmall
  rwa [smallPrimeThreshold_sq hP] at h

/-- Integrated complement-of-`U` estimate with the precise power
`P^(-ε/5)`. -/
theorem complementOfU_integral_bound
    {E : Set ℝ} (hE : MeasurableSet E)
    {P ε : ℝ} (hP : 0 < P) {A B : ℝ → ℂ}
    (hsmall : ∀ t ∈ E, ‖A t‖ ≤ P ^ (-ε / 10))
    (hleft : IntegrableOn (fun t ↦ ‖A t * B t‖ ^ 2) E)
    (hright : IntegrableOn
      (fun t ↦ (P ^ (-ε / 10)) ^ 2 * ‖B t‖ ^ 2) E) :
    (∫ t in E, ‖A t * B t‖ ^ 2) ≤
      P ^ (-ε / 5) * ∫ t in E, ‖B t‖ ^ 2 := by
  have h := setIntegral_norm_mul_sq_le_of_norm_le hE
    (Real.rpow_nonneg hP.le _) hsmall hleft hright
  rwa [smallPrimeThreshold_sq hP] at h

/-! ## Specialization to the Perron product -/

/-- The source's small-prime-polynomial region, denoted `mathcal T` in
MT23, Section 5 (it is the complement of the large-value set `mathcal U`). -/
def sectionFiveSmallPrimeSet (X P ε T : ℝ) : Set ℝ :=
  Set.Icc (X ^ (1 / 1000 : ℝ)) T ∩
    {t : ℝ | ‖primeDirichletPolynomial P (onePlusIT t)‖ ≤
      P ^ (-ε / 10)}

/-- A finite Dirichlet polynomial whose support omits zero is continuous on
the line `1+it`. -/
theorem continuous_dirichletPolynomial_onePlusIT_of_zero_not_mem_completion
    (a : ℕ → ℂ) (S : Finset ℕ) (hS : 0 ∉ S) :
    Continuous (fun t : ℝ ↦ dirichletPolynomial a S (onePlusIT t)) := by
  unfold dirichletPolynomial onePlusIT
  apply continuous_finsetSum
  intro n hn
  apply Continuous.const_mul
  apply (show Continuous (fun t : ℝ ↦ -(1 + (t : ℂ) * Complex.I)) by
    fun_prop).const_cpow
  left
  exact_mod_cast (Nat.ne_zero_iff_zero_lt.mpr
    (Nat.pos_of_ne_zero (fun h ↦ hS (h ▸ hn))))

/-- Continuity of the dyadic prime polynomial on the line `1+it`. -/
theorem continuous_primeDirichletPolynomial_onePlusIT_completion (P : ℝ) :
    Continuous (fun t : ℝ ↦ primeDirichletPolynomial P (onePlusIT t)) := by
  unfold primeDirichletPolynomial
  exact continuous_dirichletPolynomial_onePlusIT_of_zero_not_mem_completion
    _ _ (by
      intro hzero
      have hprime := (Finset.mem_filter.mp hzero).2
      exact Nat.not_prime_zero hprime)

/-- Continuity of the Perron minorant polynomial on the line `1+it`. -/
theorem continuous_perronMinorantPolynomial_onePlusIT_completion
    (weight : ℕ → ℝ) (X P : ℝ) :
    Continuous (fun t : ℝ ↦
      perronMinorantPolynomial weight X P (onePlusIT t)) := by
  unfold perronMinorantPolynomial
  exact continuous_dirichletPolynomial_onePlusIT_of_zero_not_mem_completion
    _ _ (by simp [natOpenClosedInterval])

/-- The exact small-factor argument, with all measurability and
integrability obligations discharged for the finite Perron polynomials. -/
theorem sectionFiveSmallPrimeSet_integral_le_symmetricMeanSquare
    {weight : ℕ → ℝ} {X P ε T : ℝ}
    (hX : 0 ≤ X) (hP : 0 < P) (hT : 0 ≤ T) :
    (∫ t in sectionFiveSmallPrimeSet X P ε T,
        ‖perronProduct weight X P t‖ ^ (2 : ℕ)) ≤
      P ^ (-ε / 5) *
        ∫ t in Set.Icc (-T) T,
          ‖perronMinorantPolynomial weight X P (onePlusIT t)‖ ^
            (2 : ℕ) := by
  let A : ℝ → ℂ := fun t ↦ primeDirichletPolynomial P (onePlusIT t)
  let B : ℝ → ℂ := fun t ↦
    perronMinorantPolynomial weight X P (onePlusIT t)
  let E : Set ℝ := sectionFiveSmallPrimeSet X P ε T
  have hAcont : Continuous A :=
    continuous_primeDirichletPolynomial_onePlusIT_completion P
  have hBcont : Continuous B :=
    continuous_perronMinorantPolynomial_onePlusIT_completion weight X P
  have hE : MeasurableSet E := by
    apply MeasurableSet.inter measurableSet_Icc
    exact measurableSet_le hAcont.norm.measurable measurable_const
  have hEsub : E ⊆ Set.Icc (-T) T := by
    intro t ht
    have htInterval := ht.1
    have hTzero : -T ≤ 0 := by linarith
    have hlowerNonneg : 0 ≤ X ^ (1 / 1000 : ℝ) :=
      Real.rpow_nonneg hX _
    exact ⟨hTzero.trans (hlowerNonneg.trans htInterval.1), htInterval.2⟩
  have hsmall : ∀ t ∈ E, ‖A t‖ ≤ P ^ (-ε / 10) := by
    intro t ht
    exact ht.2
  have hleft : IntegrableOn (fun t ↦ ‖A t * B t‖ ^ 2) E :=
    ((hAcont.mul hBcont).norm.pow 2).integrableOn_Icc.mono_set hEsub
  have hright : IntegrableOn
      (fun t ↦ (P ^ (-ε / 10)) ^ 2 * ‖B t‖ ^ 2) E :=
    (continuous_const.mul (hBcont.norm.pow 2)).integrableOn_Icc.mono_set hEsub
  have hsmallIntegral := complementOfU_integral_bound hE hP hsmall
    hleft hright
  have hBfull : IntegrableOn (fun t ↦ ‖B t‖ ^ 2) (Set.Icc (-T) T) :=
    (hBcont.norm.pow 2).integrableOn_Icc
  have hBmono : (∫ t in E, ‖B t‖ ^ 2) ≤
      ∫ t in Set.Icc (-T) T, ‖B t‖ ^ 2 := by
    exact setIntegral_mono_set hBfull
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
      (Filter.Eventually.of_forall hEsub)
  change (∫ t in E, ‖A t * B t‖ ^ (2 : ℕ)) ≤ _
  calc
    (∫ t in E, ‖A t * B t‖ ^ (2 : ℕ)) ≤
        P ^ (-ε / 5) * ∫ t in E, ‖B t‖ ^ (2 : ℕ) := hsmallIntegral
    _ ≤ P ^ (-ε / 5) *
        ∫ t in Set.Icc (-T) T, ‖B t‖ ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hBmono (Real.rpow_nonneg hP.le _)

/-- Full complement-of-`U` product estimate in the exact printed parameter
range, obtained solely from the three cited MT23 inputs and elementary
finite-polynomial analysis. -/
theorem sectionFiveSmallPrime_productIntegral_printedRange_of_sources
    (hmean : MatomakiTeravainenLemmaThreeThreeStatement)
    (hsieve : MatomakiTeravainenSectionFiveRoughSieveStatement)
    (hequationTwoFour : MatomakiTeravainenEquationTwoFourStatement) :
    ∃ εₘₐₓ C X₀ : ℝ,
      0 < εₘₐₓ ∧ 0 < C ∧ 3 ≤ X₀ ∧
      ∀ X alpha ε T : ℝ, X₀ ≤ X →
        let c : ℝ := 21 / 10
        let h : ℝ := (Real.log X) ^ c
        let P₁ : ℝ := (Real.log X) ^ alpha
        0 < ε → ε ≤ εₘₐₓ →
        c - 1 - 1 / 10000 ≤ alpha → alpha ≤ c - 1 →
        X / h ≤ T → T ≤ X →
        (∫ t in sectionFiveSmallPrimeSet X P₁ ε T,
            ‖perronProduct (matomakiTeravainenMinorant X ε)
                X P₁ t‖ ^ (2 : ℕ)) ≤
          C * P₁ ^ (-ε / 5) *
            (T * P₁ / (X * Real.log X) +
              1 / (Real.log X) ^ (2 : ℕ)) := by
  obtain ⟨εₘₐₓ, C, X₀, hεₘₐₓ, hC, hX₀, hmeanSquare⟩ :=
    sectionFiveMinorant_meanSquare_printedRange_of_sources
      hmean hsieve hequationTwoFour
  refine ⟨εₘₐₓ, C, X₀, hεₘₐₓ, hC, hX₀, ?_⟩
  intro X alpha ε T hX
  dsimp only
  intro hε hεUpper halphaLower halphaUpper hTLower hTUpper
  have hXthree : 3 ≤ X := hX₀.trans hX
  have hXnonneg : 0 ≤ X := by linarith
  have hlogXpos : 0 < Real.log X := Real.log_pos (by linarith)
  have hP₁pos : 0 < Real.log X ^ alpha :=
    Real.rpow_pos_of_pos hlogXpos alpha
  have hheightPos : 0 < Real.log X ^ (21 / 10 : ℝ) :=
    Real.rpow_pos_of_pos hlogXpos _
  have hTpos : 0 < T :=
    (div_pos (by linarith) hheightPos).trans_le hTLower
  have hminor := hmeanSquare X alpha ε T hX hε hεUpper halphaLower
    halphaUpper hTLower hTUpper
  have hproduct := sectionFiveSmallPrimeSet_integral_le_symmetricMeanSquare
    (weight := matomakiTeravainenMinorant X ε)
    (ε := ε)
    hXnonneg hP₁pos hTpos.le
  calc
    (∫ t in sectionFiveSmallPrimeSet X (Real.log X ^ alpha) ε T,
        ‖perronProduct (matomakiTeravainenMinorant X ε)
            X (Real.log X ^ alpha) t‖ ^ (2 : ℕ)) ≤
      (Real.log X ^ alpha) ^ (-ε / 5) *
        ∫ t in Set.Icc (-T) T,
          ‖perronMinorantPolynomial
              (matomakiTeravainenMinorant X ε) X
              (Real.log X ^ alpha) (onePlusIT t)‖ ^ (2 : ℕ) := hproduct
    _ ≤ (Real.log X ^ alpha) ^ (-ε / 5) *
        (C *
          (T * Real.log X ^ alpha / (X * Real.log X) +
            1 / Real.log X ^ (2 : ℕ))) :=
      mul_le_mul_of_nonneg_left hminor
        (Real.rpow_nonneg hP₁pos.le _)
    _ = C * (Real.log X ^ alpha) ^ (-ε / 5) *
          (T * Real.log X ^ alpha / (X * Real.log X) +
            1 / Real.log X ^ (2 : ℕ)) := by ring

/-- Bundle form of the completed printed-range complement estimate. -/
theorem sectionFiveSmallPrime_productIntegral_printedRange_of_inputs
    (inputs : ExternalInputs) :
    ∃ εₘₐₓ C X₀ : ℝ,
      0 < εₘₐₓ ∧ 0 < C ∧ 3 ≤ X₀ ∧
      ∀ X alpha ε T : ℝ, X₀ ≤ X →
        let c : ℝ := 21 / 10
        let h : ℝ := (Real.log X) ^ c
        let P₁ : ℝ := (Real.log X) ^ alpha
        0 < ε → ε ≤ εₘₐₓ →
        c - 1 - 1 / 10000 ≤ alpha → alpha ≤ c - 1 →
        X / h ≤ T → T ≤ X →
        (∫ t in sectionFiveSmallPrimeSet X P₁ ε T,
            ‖perronProduct (matomakiTeravainenMinorant X ε)
                X P₁ t‖ ^ (2 : ℕ)) ≤
          C * P₁ ^ (-ε / 5) *
            (T * P₁ / (X * Real.log X) +
              1 / (Real.log X) ^ (2 : ℕ)) :=
  sectionFiveSmallPrime_productIntegral_printedRange_of_sources
    inputs.matomakiTeravainenLemmaThreeThree
    inputs.matomakiTeravainenSectionFiveRoughSieve
    inputs.matomakiTeravainenEquationTwoFour

def complementOfUModule : ProofModule :=
  { name := "Completion.ComplementOfU"
    paperLocation := "Proof of Proposition 7.1, treatment of the set T"
    purpose :=
      "Prove the actual minorant mean square and small-prime-set product estimate in MT23's exact printed range. The wider exponent window is handled in Final/ComplementU.lean with the labelled extension E3."
    dependsOn :=
      [ "Completion.PerronTarget",
        "Completion.RoughCoefficientTransfer",
        "Assumptions.matomakiTeravainenEquationTwoFour",
        "Assumptions.matomakiTeravainenLemmaThreeThree",
        "Assumptions.matomakiTeravainenSectionFiveRoughSieve" ]
    status := .superseded }

end

end Completion
end ExactSemiprimes
