import ExactSemiprimes.Completion.GeneralPerronReduction

/-!
# Finite-support bounds for the Perron product

The product polynomial is supported in `(X/2,8X]`.  Thus a uniform bound
`K` for its convolution coefficients gives an absolute pointwise bound
`16K` on the line `Re(s)=1`.  This is the finite algebraic input needed in
the low-frequency part of the Parseval argument.
-/

namespace ExactSemiprimes
namespace Completion

noncomputable section

/-- The literal convolution support lies in `(X/2,8X]`. -/
theorem perronProductSupport_mem_range
    {X P : ℝ} (hX : 0 < X) (hP : 0 < P) {m : ℕ}
    (hm : m ∈ perronProductSupport X P) :
    X / 2 < (m : ℝ) ∧ (m : ℝ) ≤ 8 * X := by
  classical
  rcases Finset.mem_image.mp hm with ⟨pn, hpn, rfl⟩
  rcases Finset.mem_product.mp hpn with ⟨hp, hn⟩
  have hpRange := (mem_dyadicInterval hP.le).mp
    (Finset.mem_filter.mp hp).1
  have hnRange := (mem_natOpenClosedInterval
    (by positivity : 0 ≤ X / (2 * P))
    (by positivity : 0 ≤ 4 * X / P)).mp hn
  have hnpos : 0 < (pn.2 : ℝ) :=
    (div_pos hX (mul_pos (by norm_num) hP)).trans hnRange.1
  constructor
  · have hfirst : X / 2 < P * (pn.2 : ℝ) := by
      apply (div_lt_iff₀ (show 0 < (2 : ℝ) by norm_num)).2
      have hscaled := (div_lt_iff₀ (show 0 < 2 * P by positivity)).1 hnRange.1
      nlinarith
    have hsecond : P * (pn.2 : ℝ) <
        (pn.1 : ℝ) * (pn.2 : ℝ) :=
      mul_lt_mul_of_pos_right hpRange.1 hnpos
    simpa [Nat.cast_mul] using hfirst.trans hsecond
  · have hmul : (pn.1 : ℝ) * (pn.2 : ℝ) ≤
        (2 * P) * (4 * X / P) := by
      exact mul_le_mul hpRange.2 hnRange.2 hnpos.le (by positivity)
    have hidentity : (2 * P) * (4 * X / P) = 8 * X := by
      field_simp [hP.ne']
      ring
    simpa [Nat.cast_mul, hidentity] using hmul

/-- The number of possible product indices is at most the length of the
ambient interval `(X/2,8X]`. -/
theorem perronProductSupport_card_cast_le
    {X P : ℝ} (hX : 0 < X) (hP : 0 < P) :
    ((perronProductSupport X P).card : ℝ) ≤ 8 * X := by
  classical
  let ambient : Finset ℕ := natOpenClosedInterval (X / 2) (8 * X)
  have hsubset : perronProductSupport X P ⊆ ambient := by
    intro m hm
    have hmRange := perronProductSupport_mem_range hX hP hm
    exact (mem_natOpenClosedInterval (by positivity) (by positivity)).2 hmRange
  have hcard : (perronProductSupport X P).card ≤ ambient.card :=
    Finset.card_le_card hsubset
  have hambient : ambient.card ≤ ⌊8 * X⌋₊ := by
    simp only [ambient, natOpenClosedInterval, Nat.card_Ioc]
    omega
  calc
    ((perronProductSupport X P).card : ℝ) ≤ (ambient.card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ (⌊8 * X⌋₊ : ℝ) := by exact_mod_cast hambient
    _ ≤ 8 * X := Nat.floor_le (by positivity)

/-- A coefficient bound on the finite support gives a uniform pointwise
bound for the product polynomial on `Re(s)=1`. -/
theorem norm_perronProduct_le_sixteen_mul
    {weight : ℕ → ℝ} {X P K t : ℝ}
    (hX : 0 < X) (hP : 0 < P) (hK : 0 ≤ K)
    (hcoeff : ∀ m ∈ perronProductSupport X P,
      ‖perronProductCoefficient weight X P m‖ ≤ K) :
    ‖perronProduct weight X P t‖ ≤ 16 * K := by
  rw [perronProduct_eq_convolutionPolynomial]
  unfold dirichletPolynomial
  have hterm : ∀ m ∈ perronProductSupport X P,
      ‖perronProductCoefficient weight X P m *
          (m : ℂ) ^ (-onePlusIT t)‖ ≤ K * (2 / X) := by
    intro m hm
    have hmRange := perronProductSupport_mem_range hX hP hm
    have hmposReal : 0 < (m : ℝ) := by linarith
    have hmpos : 0 < m := by exact_mod_cast hmposReal
    have hcpow :
        ‖(m : ℂ) ^ (-onePlusIT t)‖ = (m : ℝ)⁻¹ := by
      rw [← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos hmposReal]
      simp [onePlusIT, Real.rpow_neg_one]
    rw [norm_mul, hcpow]
    have hinv : (m : ℝ)⁻¹ ≤ 2 / X := by
      have hhalf : 0 < X / 2 := by positivity
      have := (inv_le_inv₀ hmposReal hhalf).2 hmRange.1.le
      simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm,
        mul_assoc] using this
    exact mul_le_mul (hcoeff m hm) hinv (inv_nonneg.mpr hmposReal.le) hK
  calc
    ‖∑ m ∈ perronProductSupport X P,
        perronProductCoefficient weight X P m *
          (m : ℂ) ^ (-onePlusIT t)‖ ≤
        ∑ m ∈ perronProductSupport X P,
          ‖perronProductCoefficient weight X P m *
            (m : ℂ) ^ (-onePlusIT t)‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ perronProductSupport X P, K * (2 / X) :=
      Finset.sum_le_sum hterm
    _ = ((perronProductSupport X P).card : ℝ) * (K * (2 / X)) := by
      simp
    _ ≤ (8 * X) * (K * (2 / X)) := by
      exact mul_le_mul_of_nonneg_right
        (perronProductSupport_card_cast_le hX hP) (by positivity)
    _ = 16 * K := by field_simp [hX.ne']; ring

def perronFiniteSupportBoundsModule : ProofModule :=
  { name := "Completion.PerronFiniteSupportBounds"
    paperLocation :=
      "Finite support and coefficient bookkeeping preceding the low-frequency part of Matomäki--Radziwiłł, Lemma 14"
    purpose :=
      "Place the convolution support in `(X/2,8X]` and derive the uniform `16K` bound for the Perron product."
    dependsOn := ["Completion.GeneralPerronReduction"]
    status := .proved }

end

end Completion
end ExactSemiprimes
