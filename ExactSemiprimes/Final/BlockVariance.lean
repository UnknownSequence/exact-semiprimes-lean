import ExactSemiprimes.Final.DirichletTarget

/-!
# Proposition 7.1: the block variance

For a prime block `P` with `(log X)^(1925/1763+η) ≤ P ≤ (log X)^(c-1)`,
`h = (log X)^c / 2` and `h₁ = X^(99/100)`,

`(1/X) ∫_X^{2X} |S_P(x,h)/h - S_P(x,h₁)/h₁|² dx ≪ (log X)^(-2-ε/10)`.

This is the labelled extension (E1) (the Parseval/Perron reduction of
[MR16, Lemma 14], [Ter16, Lemma 1], [MT23, Lemma 3.1]) at the cutoff
`T₀ = X^(1/1000)`, fed with the Dirichlet-polynomial target
`Final.blockTarget_uniform` and the coefficient bound `5324` of
`Final.PerronTail`.
-/

namespace ExactSemiprimes
namespace Final

open Filter Real MeasureTheory

noncomputable section

theorem rpow_thousandth_le_div {X L c : ℝ} (hX1 : 1 < X) (hLc : 0 < L ^ c)
    (hLcX : L ^ c ≤ X ^ (1 / 2 : ℝ)) :
    X ^ (1 / 1000 : ℝ) ≤ X / (L ^ c / 2) := by
  have hXpos : 0 < X := by linarith
  have hsq : X = X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hXpos]; norm_num
  have hsqpos : 0 < X ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have h1 : X ^ (1 / 2 : ℝ) ≤ X / (L ^ c / 2) := by
    rw [le_div_iff₀ (by positivity)]
    calc X ^ (1 / 2 : ℝ) * (L ^ c / 2) ≤ X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hsqpos.le; linarith
      _ = X := hsq.symm
  have h2 : X ^ (1 / 1000 : ℝ) ≤ X ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num)
  linarith

theorem long_le_div_cube {X : ℝ} (hX1 : 1 < X) :
    X ^ (99 / 100 : ℝ) ≤ X / (X ^ (1 / 1000 : ℝ)) ^ (3 : ℕ) := by
  have hXpos : 0 < X := by linarith
  have h3 : (X ^ (1 / 1000 : ℝ)) ^ (3 : ℕ) = X ^ (3 / 1000 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hXpos.le]; norm_num
  rw [h3]
  have h4 : X / X ^ (3 / 1000 : ℝ) = X ^ (997 / 1000 : ℝ) := by
    rw [show (997 / 1000 : ℝ) = 1 - 3 / 1000 by norm_num, Real.rpow_sub hXpos,
      Real.rpow_one]
  rw [h4]
  exact Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num)

/-- **Proposition 7.1**, uniformly over the block window. -/
theorem blockVariance_uniform (inputs : ExternalInputs) (ext : ParameterExtensionInputs)
    {c : ℝ} (hc2 : 2 < c) (hc : c ≤ 21 / 10) :
    ∀ η : ℝ, 0 < η → ∃ εₘₐₓ : ℝ, 0 < εₘₐₓ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℕ in atTop, ∀ P : ℝ,
        (Real.log (X : ℝ)) ^ (1925 / 1763 + η) ≤ P → P ≤ (Real.log (X : ℝ)) ^ (c - 1) →
        matomakiTeravainenShortLongVariance (matomakiTeravainenMinorant (X : ℝ) ε)
            (X : ℝ) P ((Real.log (X : ℝ)) ^ c / 2) ((X : ℝ) ^ (99 / 100 : ℝ)) ≤
          C * (Real.log (X : ℝ)) ^ (-(2 + ε / 10)) := by
  intro η hη
  obtain ⟨CE, hCE, hE1⟩ := ext.generalParsevalReduction
  obtain ⟨εT, hεT, hT⟩ := blockTarget_uniform inputs ext hc2 hc η hη
  obtain ⟨ε24, hε24, heq24⟩ := inputs.matomakiTeravainenEquationTwoFour
  refine ⟨min (min εT ε24) 1, by positivity, ?_⟩
  intro ε hε hεle
  have hεT' : ε ≤ εT := hεle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hε24' : ε ≤ ε24 := hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε1 : ε ≤ 1 := hεle.trans (min_le_right _ _)
  obtain ⟨CT, hCT, hTev⟩ := hT ε hε hεT'
  refine ⟨CE * (1 + 2 * CT), by positivity, ?_⟩
  have hlogNat : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgeo := tendsto_natCast_atTop_atTop.eventually
    Completion.eventually_perronSupport_inside_equationTwoFour_range_wide
  have hXe : ∀ᶠ X : ℕ in atTop, Real.exp 1 < (X : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  have hPz := eventually_const_mul_log_rpow_le_rpow 2 (11 / 10) (c := 1 / 10) (by norm_num)
  have hLc := eventually_const_mul_log_rpow_le_rpow 1 (21 / 10) (c := 1 / 2) (by norm_num)
  have hK := eventually_const_mul_log_rpow_le_rpow ((5324 : ℝ) ^ (2 : ℕ)) 3
    (c := 1 / 1000) (by norm_num)
  filter_upwards [hTev, hgeo, hXe, hPz, hLc, hK, hlogNat.eventually_ge_atTop 2,
    eventually_ge_atTop 3] with X hTX hgeoX hXeX hPzX hLcX hKX hlog2 hX3
  intro P hPlo hPhi
  have hX3' : (3 : ℝ) ≤ X := by exact_mod_cast hX3
  have hXpos : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) < X := by linarith
  set L := Real.log (X : ℝ) with hL
  have hL1 : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hLP : L ≤ P := by
    calc L = L ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ L ^ (1925 / 1763 + η) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ ≤ P := hPlo
  have hPpos : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hP11 : P ≤ L ^ (11 / 10 : ℝ) :=
    hPhi.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  have hLc1 : L ≤ L ^ c := by
    calc L = L ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ L ^ c := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hLcpos : 0 < L ^ c := by linarith
  have hLcX : L ^ c ≤ (X : ℝ) ^ (1 / 2 : ℝ) := by
    have : L ^ c ≤ L ^ (21 / 10 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 hc
    have h1 : 1 * L ^ (21 / 10 : ℝ) ≤ (X : ℝ) ^ (1 / 2 : ℝ) := hLcX
    linarith
  have hh1 : 1 ≤ L ^ c / 2 := by linarith
  have hhlong : L ^ c / 2 ≤ (X : ℝ) ^ (99 / 100 : ℝ) := by
    have : (X : ℝ) ^ (1 / 2 : ℝ) ≤ (X : ℝ) ^ (99 / 100 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num)
    linarith
  have hT01 : 1 ≤ (X : ℝ) ^ (1 / 1000 : ℝ) := Real.one_le_rpow hX1.le (by norm_num)
  have hT0pos : 0 < (X : ℝ) ^ (1 / 1000 : ℝ) := by linarith
  -- the coefficient bound
  obtain ⟨_, hsupLo, hsupHi⟩ := hgeoX (scaleExponent (X : ℝ) P)
    (le_scaleExponent_of_rpow_le hXeX hPpos (by rw [Real.rpow_one]; exact hLP))
    (scaleExponent_le_of_le_rpow hXeX hPpos hP11)
  rw [rpow_scaleExponent hXeX hPpos] at hsupLo hsupHi
  have hPzX' : 2 * P < (X : ℝ) ^ (2 / 11 : ℝ) := by
    have h1 : (X : ℝ) ^ (1 / 10 : ℝ) < (X : ℝ) ^ (2 / 11 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt hX1 (by norm_num)
    have h0 : 2 * L ^ (11 / 10 : ℝ) ≤ (X : ℝ) ^ (1 / 10 : ℝ) := hPzX
    linarith
  have hcoeff : ∀ m ∈ Completion.perronProductSupport (X : ℝ) P,
      ‖Completion.perronProductCoefficient (matomakiTeravainenMinorant (X : ℝ) ε)
        (X : ℝ) P m‖ ≤ 5324 := fun m _ ↦
    minorant_productCoefficient_le_5324 hX3' hPpos hε hε24' heq24 hsupLo hsupHi hPzX' m
  -- the low-frequency term
  have hsave0 : 0 ≤ L ^ (-(2 + ε / 10)) := Real.rpow_nonneg hLpos.le _
  have hlow : (5324 : ℝ) ^ (2 : ℕ) / (X : ℝ) ^ (1 / 1000 : ℝ) ≤ L ^ (-(2 + ε / 10)) := by
    have hL3 : L ^ (2 + ε / 10) ≤ L ^ (3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have hK' : (5324 : ℝ) ^ (2 : ℕ) * L ^ (3 : ℝ) ≤ (X : ℝ) ^ (1 / 1000 : ℝ) := hKX
    rw [Real.rpow_neg hLpos.le, div_le_iff₀ hT0pos]
    have hpos : 0 < L ^ (2 + ε / 10) := Real.rpow_pos_of_pos hLpos _
    rw [← div_eq_inv_mul, le_div_iff₀ hpos]
    nlinarith
  obtain ⟨hmid, htail⟩ := hTX P hPlo hPhi
  have hvar := hE1 (matomakiTeravainenMinorant (X : ℝ) ε) (X : ℝ) P (L ^ c / 2)
    ((X : ℝ) ^ (99 / 100 : ℝ)) ((X : ℝ) ^ (1 / 1000 : ℝ)) 5324 hX3' hP1 hT01 hh1 hhlong
    (long_le_div_cube hX1) (rpow_thousandth_le_div hX1 hLcpos hLcX) (by norm_num) hcoeff
    (CT * L ^ (-(2 + ε / 10))) (CT * L ^ (-(2 + ε / 10))) hmid htail
  calc _ ≤ CE * ((5324 : ℝ) ^ (2 : ℕ) / (X : ℝ) ^ (1 / 1000 : ℝ) +
        CT * L ^ (-(2 + ε / 10)) + CT * L ^ (-(2 + ε / 10))) := hvar
    _ ≤ CE * (L ^ (-(2 + ε / 10)) + CT * L ^ (-(2 + ε / 10)) +
        CT * L ^ (-(2 + ε / 10))) := by gcongr
    _ = CE * (1 + 2 * CT) * L ^ (-(2 + ε / 10)) := by ring

end

end Final
end ExactSemiprimes
