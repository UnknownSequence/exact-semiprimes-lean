import ExactSemiprimes.Completion.PerronKernelBounds
import ExactSemiprimes.Completion.PerronFiniteSupportBounds

/-!
# Low-frequency cancellation in the Perron reduction

This file formalizes the low-frequency calculation in
Matomäki--Radziwiłł, Lemma 14.  The two normalized interval kernels have
the same leading phase, so their difference gains `T₀(h+h_long)/x`.
Together with the exact finite-support coefficient bound, this gives an
explicit `O(K/T₀)` pointwise contribution under
`h_long ≤ X/T₀³`.
-/

namespace ExactSemiprimes
namespace Completion

open MeasureTheory

noncomputable section

/-- The low-frequency part of the difference between the two normalized
Perron reconstructions (with the harmless factor `1/(2π)` omitted). -/
def perronLowFrequencyDifference
    (weight : ℕ → ℝ) (X P x h hlong T₀ : ℝ) : ℂ :=
  ∫ t : ℝ in (-T₀)..T₀,
    perronProduct weight X P t *
      (normalizedPerronKernel x h t -
        normalizedPerronKernel x hlong t)

/-- The direct low-frequency estimate, before using the upper bound on the
long interval. -/
theorem norm_perronLowFrequencyDifference_le
    {weight : ℕ → ℝ} {X P x h hlong T₀ K : ℝ}
    (hX : 0 < X) (hP : 0 < P) (hx : X ≤ x)
    (hh : 0 < h) (hhlong : 0 < hlong) (hT₀ : 0 ≤ T₀)
    (hK : 0 ≤ K)
    (hcoeff : ∀ m ∈ perronProductSupport X P,
      ‖perronProductCoefficient weight X P m‖ ≤ K) :
    ‖perronLowFrequencyDifference weight X P x h hlong T₀‖ ≤
      32 * K * T₀ ^ (2 : ℕ) * (h + hlong) / X := by
  have hxpos : 0 < x := hX.trans_le hx
  have hsum : 0 ≤ h + hlong := by positivity
  have hpoint : ∀ t ∈ Set.uIoc (-T₀) T₀,
      ‖perronProduct weight X P t *
        (normalizedPerronKernel x h t -
          normalizedPerronKernel x hlong t)‖ ≤
        16 * K * (T₀ / X * (h + hlong)) := by
    intro t htmem
    have horder : -T₀ ≤ T₀ := by linarith
    rw [Set.uIoc_of_le horder] at htmem
    have ht : |t| ≤ T₀ := (abs_le).2 ⟨htmem.1.le, htmem.2⟩
    have hkernel := norm_normalizedPerronKernel_sub_le
      hxpos hh hhlong ht
    have hscale : T₀ / x * (h + hlong) ≤
        T₀ / X * (h + hlong) := by
      apply mul_le_mul_of_nonneg_right _ hsum
      exact div_le_div_of_nonneg_left hT₀ hX hx
    rw [norm_mul]
    calc
      ‖perronProduct weight X P t‖ *
          ‖normalizedPerronKernel x h t -
            normalizedPerronKernel x hlong t‖ ≤
          (16 * K) * (T₀ / x * (h + hlong)) := by
        exact mul_le_mul
          (norm_perronProduct_le_sixteen_mul hX hP hK hcoeff)
          hkernel (norm_nonneg _) (by positivity)
      _ ≤ (16 * K) * (T₀ / X * (h + hlong)) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
  have hint :
      ‖∫ t : ℝ in (-T₀)..T₀,
        perronProduct weight X P t *
          (normalizedPerronKernel x h t -
            normalizedPerronKernel x hlong t)‖ ≤
        (16 * K * (T₀ / X * (h + hlong))) *
          |T₀ - (-T₀)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  unfold perronLowFrequencyDifference
  calc
    ‖∫ t : ℝ in (-T₀)..T₀,
        perronProduct weight X P t *
          (normalizedPerronKernel x h t -
            normalizedPerronKernel x hlong t)‖ ≤
        (16 * K * (T₀ / X * (h + hlong))) *
          |T₀ - (-T₀)| := hint
    _ = 32 * K * T₀ ^ (2 : ℕ) * (h + hlong) / X := by
      rw [abs_of_nonneg (by linarith : 0 ≤ T₀ - (-T₀))]
      ring

/-- Under the long-interval condition from the Parseval lemma, the entire
low-frequency contribution is at most `64K/T₀`. -/
theorem norm_perronLowFrequencyDifference_le_over_cutoff
    {weight : ℕ → ℝ} {X P x h hlong T₀ K : ℝ}
    (hX : 0 < X) (hP : 0 < P) (hx : X ≤ x)
    (hh : 0 < h) (hhlong : 0 < hlong) (hhle : h ≤ hlong)
    (hT₀ : 0 < T₀) (hK : 0 ≤ K)
    (hlongUpper : hlong ≤ X / T₀ ^ (3 : ℕ))
    (hcoeff : ∀ m ∈ perronProductSupport X P,
      ‖perronProductCoefficient weight X P m‖ ≤ K) :
    ‖perronLowFrequencyDifference weight X P x h hlong T₀‖ ≤
      64 * K / T₀ := by
  have hdirect := norm_perronLowFrequencyDifference_le
    hX hP hx hh hhlong hT₀.le hK hcoeff
  calc
    ‖perronLowFrequencyDifference weight X P x h hlong T₀‖ ≤
        32 * K * T₀ ^ (2 : ℕ) * (h + hlong) / X := hdirect
    _ ≤ 32 * K * T₀ ^ (2 : ℕ) * (2 * hlong) / X := by
      apply div_le_div_of_nonneg_right _ hX.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ ≤ 32 * K * T₀ ^ (2 : ℕ) *
          (2 * (X / T₀ ^ (3 : ℕ))) / X := by
      apply div_le_div_of_nonneg_right _ hX.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hlongUpper (by norm_num)
    _ = 64 * K / T₀ := by
      field_simp [hX.ne', hT₀.ne']
      ring

def perronLowFrequencyModule : ProofModule :=
  { name := "Completion.PerronLowFrequency"
    paperLocation :=
      "Matomäki--Radziwiłł, Lemma 14: expansion and cancellation for `|t|≤T₀`"
    purpose :=
      "Prove an explicit `64K/T₀` bound for the complete low-frequency Perron-kernel difference."
    dependsOn :=
      ["Completion.PerronKernelBounds",
        "Completion.PerronFiniteSupportBounds"]
    status := .proved }

end

end Completion
end ExactSemiprimes
