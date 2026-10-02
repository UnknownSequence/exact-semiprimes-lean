import ExactSemiprimes.Completion.GeneralPerronReduction

/-!
# Elementary Perron-kernel identities and bounds

This file formalizes the elementary kernel layer in the proof of
Matomäki--Radziwiłł, Lemma 14.  It does not use a Perron inversion theorem:
the results are identities and estimates for the kernel which occurs after
such an inversion has been made.
-/

namespace ExactSemiprimes
namespace Completion

open MeasureTheory

noncomputable section

/-- The unnormalised Perron kernel for the interval `(x,x+h]`. -/
def perronIncrementKernel (x h t : ℝ) : ℂ :=
  (((x + h : ℝ) : ℂ) ^ (onePlusIT t) -
      (x : ℂ) ^ (onePlusIT t)) / onePlusIT t

/-- The kernel appropriate to the average over `(x,x+h]`. -/
def normalizedPerronKernel (x h t : ℝ) : ℂ :=
  perronIncrementKernel x h t / (h : ℂ)

/-- The pure Mellin phase `x^{it}`. -/
def perronPhase (x t : ℝ) : ℂ :=
  (x : ℂ) ^ ((t : ℂ) * Complex.I)

theorem onePlusIT_ne_zero (t : ℝ) : onePlusIT t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [onePlusIT] at hre

@[simp]
theorem onePlusIT_re (t : ℝ) : (onePlusIT t).re = 1 := by
  simp [onePlusIT]

@[simp]
theorem imaginaryExponent_re (t : ℝ) :
    (((t : ℂ) * Complex.I).re) = 0 := by
  simp

/-- Exact antiderivative identity behind the Perron interval kernel. -/
theorem integral_perronPhase_eq_incrementKernel (x h t : ℝ) :
    (∫ u : ℝ in x..x + h, perronPhase u t) =
      perronIncrementKernel x h t := by
  have hint := integral_cpow
    (a := x) (b := x + h) (r := (t : ℂ) * Complex.I)
    (Or.inl (by simp : (-1 : ℝ) < (((t : ℂ) * Complex.I).re)))
  simpa [perronPhase, perronIncrementKernel, onePlusIT, add_comm,
    add_left_comm, add_assoc] using hint

/-- The normalized kernel is exactly the average of the Mellin phase. -/
theorem normalizedPerronKernel_eq_average
    (x h t : ℝ) :
    normalizedPerronKernel x h t =
      (∫ u : ℝ in x..x + h, perronPhase u t) / (h : ℂ) := by
  rw [integral_perronPhase_eq_incrementKernel]
  rfl

/-- A Mellin phase has unit norm on the positive real axis. -/
@[simp]
theorem norm_perronPhase {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖perronPhase x t‖ = 1 := by
  rw [perronPhase, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

/-- The normalized interval kernel is bounded by one. -/
theorem norm_normalizedPerronKernel_le_one
    {x h t : ℝ} (hx : 0 < x) (hh : 0 < h) :
    ‖normalizedPerronKernel x h t‖ ≤ 1 := by
  rw [normalizedPerronKernel_eq_average, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hh]
  have hpos : ∀ u ∈ Set.uIoc x (x + h), 0 < u := by
    intro u hu
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hh.le)] at hu
    exact hx.trans hu.1
  have hnorm :
      ‖∫ u : ℝ in x..x + h, perronPhase u t‖ ≤ 1 * |x + h - x| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    simp [norm_perronPhase (hpos u hu) t]
  have hnorm' :
      ‖∫ u : ℝ in x..x + h, perronPhase u t‖ ≤ h := by
    simpa [abs_of_pos hh] using hnorm
  exact (div_le_iff₀ hh).2 (by simpa using hnorm')

/-- On a positive interval, the Mellin phase is Lipschitz with the sharp
local derivative majorant `|t|/x`.  This is the elementary estimate used to
cancel the low-frequency pieces of two normalized Perron kernels. -/
theorem norm_perronPhase_sub_le
    {x u t : ℝ} (hx : 0 < x) (hxu : x ≤ u) :
    ‖perronPhase u t - perronPhase x t‖ ≤
      |t| / x * (u - x) := by
  by_cases ht : t = 0
  · subst t
    simp [perronPhase]
  let r : ℂ := (t : ℂ) * Complex.I
  have hr : r ≠ 0 := by
    simp [r, ht]
  have hdiff : ∀ y ∈ Set.Icc x u,
      DifferentiableAt ℝ (fun z : ℝ ↦ (z : ℂ) ^ r) y := by
    intro y hy
    have hypos : 0 < y := hx.trans_le hy.1
    exact (hasDerivAt_ofReal_cpow_const hypos.ne' hr).differentiableAt
  have hderiv : ∀ y ∈ Set.Icc x u,
      ‖deriv (fun z : ℝ ↦ (z : ℂ) ^ r) y‖ ≤ |t| / x := by
    intro y hy
    have hypos : 0 < y := hx.trans_le hy.1
    rw [Complex.deriv_ofReal_cpow_const hypos.ne' hr, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hypos]
    have hrnorm : ‖r‖ = |t| := by
      simp [r, Real.norm_eq_abs]
    have hrexponent : (r - 1).re = -1 := by
      simp [r]
    rw [hrnorm, hrexponent, Real.rpow_neg_one]
    exact mul_le_mul_of_nonneg_left
      (by simpa [one_div] using one_div_le_one_div_of_le hx hy.1)
      (abs_nonneg t)
  have hbound := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.Icc x u) hdiff hderiv (convex_Icc x u)
    (⟨le_rfl, hxu⟩ : x ∈ Set.Icc x u)
    (⟨hxu, le_rfl⟩ : u ∈ Set.Icc x u)
  simpa [perronPhase, r, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hxu)] using hbound

/-- At low frequency, the normalized Perron kernel differs from the common
phase `x^{it}` by at most `|t|h/x`. -/
theorem norm_normalizedPerronKernel_sub_phase_le
    {x h t : ℝ} (hx : 0 < x) (hh : 0 < h) :
    ‖normalizedPerronKernel x h t - perronPhase x t‖ ≤
      |t| / x * h := by
  have hphase : IntervalIntegrable (fun u : ℝ ↦ perronPhase u t)
      MeasureTheory.volume x (x + h) := by
    simpa [perronPhase] using
      (intervalIntegral.intervalIntegrable_cpow'
        (a := x) (b := x + h) (r := (t : ℂ) * Complex.I)
        (by simp : (-1 : ℝ) < (((t : ℂ) * Complex.I).re)))
  have hrepr :
      normalizedPerronKernel x h t - perronPhase x t =
        (∫ u : ℝ in x..x + h,
          (perronPhase u t - perronPhase x t)) / (h : ℂ) := by
    rw [normalizedPerronKernel_eq_average,
      intervalIntegral.integral_sub hphase intervalIntegrable_const,
      intervalIntegral.integral_const]
    rw [show x + h - x = h by ring]
    simp only [Complex.real_smul]
    field_simp [hh.ne']
  rw [hrepr, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have hpoint : ∀ u ∈ Set.uIoc x (x + h),
      ‖perronPhase u t - perronPhase x t‖ ≤ |t| / x * h := by
    intro u hu
    rw [Set.uIoc_of_le (le_add_of_nonneg_right hh.le)] at hu
    calc
      ‖perronPhase u t - perronPhase x t‖ ≤
          |t| / x * (u - x) :=
        norm_perronPhase_sub_le hx hu.1.le
      _ ≤ |t| / x * h := by
        apply mul_le_mul_of_nonneg_left
        · simpa [add_comm] using sub_le_iff_le_add.mpr hu.2
        · positivity
  have hint :
      ‖∫ u : ℝ in x..x + h,
          (perronPhase u t - perronPhase x t)‖ ≤
        (|t| / x * h) * |x + h - x| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  have hint' :
      ‖∫ u : ℝ in x..x + h,
          (perronPhase u t - perronPhase x t)‖ ≤
        (|t| / x * h) * h := by
    simpa [abs_of_pos hh] using hint
  exact (div_le_iff₀ hh).2 (by simpa [mul_assoc] using hint')

/-- Consequently two normalized interval kernels of lengths `h₁,h₂`
cancel at low frequency. -/
theorem norm_normalizedPerronKernel_sub_le
    {x h₁ h₂ t T₀ : ℝ}
    (hx : 0 < x) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    (ht : |t| ≤ T₀) :
    ‖normalizedPerronKernel x h₁ t -
        normalizedPerronKernel x h₂ t‖ ≤
      T₀ / x * (h₁ + h₂) := by
  calc
    ‖normalizedPerronKernel x h₁ t -
        normalizedPerronKernel x h₂ t‖ =
        ‖(normalizedPerronKernel x h₁ t - perronPhase x t) -
          (normalizedPerronKernel x h₂ t - perronPhase x t)‖ := by
      apply congrArg norm
      ring
    _ ≤
        ‖normalizedPerronKernel x h₁ t - perronPhase x t‖ +
          ‖normalizedPerronKernel x h₂ t - perronPhase x t‖ := by
      exact norm_sub_le _ _
    _ ≤ (|t| / x * h₁) + (|t| / x * h₂) :=
      add_le_add
        (norm_normalizedPerronKernel_sub_phase_le hx hh₁)
        (norm_normalizedPerronKernel_sub_phase_le hx hh₂)
    _ ≤ (T₀ / x * h₁) + (T₀ / x * h₂) := by
      have hxnonneg : 0 ≤ x := hx.le
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right ht hxnonneg) hh₁.le)
        (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right ht hxnonneg) hh₂.le)
    _ = T₀ / x * (h₁ + h₂) := by ring

/-- The complementary high-frequency estimate comes directly from the two
endpoints in the Perron kernel. -/
theorem norm_normalizedPerronKernel_le_endpoint
    {x h t : ℝ} (hx : 0 < x) (hh : 0 < h) (ht : t ≠ 0) :
    ‖normalizedPerronKernel x h t‖ ≤
      (2 * x + h) / (h * |t|) := by
  have hxh : 0 < x + h := by linarith
  have htpos : 0 < |t| := abs_pos.mpr ht
  have hspos : 0 < ‖onePlusIT t‖ := norm_pos_iff.mpr (onePlusIT_ne_zero t)
  have him : |t| ≤ ‖onePlusIT t‖ := by
    have := Complex.abs_im_le_norm (onePlusIT t)
    simpa [onePlusIT] using this
  have hnum :
      ‖(((x + h : ℝ) : ℂ) ^ (onePlusIT t) -
          (x : ℂ) ^ (onePlusIT t))‖ ≤ 2 * x + h := by
    calc
      ‖(((x + h : ℝ) : ℂ) ^ (onePlusIT t) -
          (x : ℂ) ^ (onePlusIT t))‖ ≤
          ‖((x + h : ℝ) : ℂ) ^ (onePlusIT t)‖ +
            ‖(x : ℂ) ^ (onePlusIT t)‖ := norm_sub_le _ _
      _ = (x + h) + x := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxh,
          Complex.norm_cpow_eq_rpow_re_of_pos hx,
          onePlusIT_re, Real.rpow_one, Real.rpow_one]
      _ = 2 * x + h := by ring
  rw [normalizedPerronKernel, perronIncrementKernel, norm_div, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  calc
    ‖(((x + h : ℝ) : ℂ) ^ (onePlusIT t) -
          (x : ℂ) ^ (onePlusIT t))‖ / ‖onePlusIT t‖ / h ≤
        (2 * x + h) / ‖onePlusIT t‖ / h := by
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hnum hspos.le) hh.le
    _ ≤ (2 * x + h) / |t| / h := by
      apply div_le_div_of_nonneg_right _ hh.le
      exact div_le_div_of_nonneg_left (by linarith) htpos him
    _ = (2 * x + h) / (h * |t|) := by
      field_simp [hh.ne', ht]

/-- The standard `min(1, endpoint/frequency)` Perron-kernel majorant. -/
theorem norm_normalizedPerronKernel_le_min
    {x h t : ℝ} (hx : 0 < x) (hh : 0 < h) (ht : t ≠ 0) :
    ‖normalizedPerronKernel x h t‖ ≤
      min 1 ((2 * x + h) / (h * |t|)) := by
  exact le_min (norm_normalizedPerronKernel_le_one hx hh)
    (norm_normalizedPerronKernel_le_endpoint hx hh ht)

/-- A corresponding high-frequency estimate for the difference of two
normalized kernels. -/
theorem norm_normalizedPerronKernel_sub_le_endpoint
    {x h₁ h₂ t : ℝ}
    (hx : 0 < x) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (ht : t ≠ 0) :
    ‖normalizedPerronKernel x h₁ t -
        normalizedPerronKernel x h₂ t‖ ≤
      (2 * x + h₁) / (h₁ * |t|) +
        (2 * x + h₂) / (h₂ * |t|) := by
  exact (norm_sub_le _ _).trans
    (add_le_add
      (norm_normalizedPerronKernel_le_endpoint hx hh₁ ht)
      (norm_normalizedPerronKernel_le_endpoint hx hh₂ ht))

def perronKernelBoundsModule : ProofModule :=
  { name := "Completion.PerronKernelBounds"
    paperLocation :=
      "Matomäki--Radziwiłł, Lemma 14: the Perron interval kernel"
    purpose :=
      "Prove the exact kernel integral identity and its elementary unit bound. The Perron reduction itself is the labelled extension E1."
    dependsOn := ["Completion.GeneralPerronReduction"]
    status := .superseded }

end

end Completion
end ExactSemiprimes
