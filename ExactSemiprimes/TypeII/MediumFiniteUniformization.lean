import ExactSemiprimes.TypeII.MediumRangeCardinality

/-!
# Finite uniformization of medium-branch parameters

The powered medium Type-II argument first produces a positive saving and,
after the coefficient scale is fixed, a multiplicative constant and a
starting height for each bounded convolution order.  This file replaces
those order-dependent data by one positive minimum saving and two common
maxima.
-/

namespace ExactSemiprimes
namespace TypeII

noncomputable section

/-- The infimum of finitely many strictly positive real values, indexed by a
nonempty finset, is strictly positive and lies below every indexed value. -/
theorem finite_inf'_positive_and_le
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 < f i) :
    0 < s.inf' hs f ∧ ∀ i ∈ s, s.inf' hs f ≤ f i := by
  constructor
  · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf' hs f
    rw [heq]
    exact hf i hi
  · intro i hi
    exact Finset.inf'_le f hi

/-- The supremum of finitely many positive constants and starting heights is
a positive common constant and a common starting height at least one. -/
theorem finite_sup'_positive_one_le_and_bounds
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (C T₀ : ι → ℝ)
    (hC : ∀ i ∈ s, 0 < C i)
    (hT₀ : ∀ i ∈ s, 1 ≤ T₀ i) :
    0 < s.sup' hs C ∧ 1 ≤ s.sup' hs T₀ ∧
      ∀ i ∈ s, C i ≤ s.sup' hs C ∧ T₀ i ≤ s.sup' hs T₀ := by
  have hs' := hs
  obtain ⟨i, hi⟩ := hs'
  have hCi : C i ≤ s.sup' hs C := Finset.le_sup' C hi
  have hTi : T₀ i ≤ s.sup' hs T₀ := Finset.le_sup' T₀ hi
  refine ⟨(hC i hi).trans_le hCi, (hT₀ i hi).trans hTi, ?_⟩
  intro j hj
  exact ⟨Finset.le_sup' C hj, Finset.le_sup' T₀ hj⟩

/-- Simultaneously uniformize a positive saving and, after an arbitrary
parameter `a` has been fixed, a positive multiplicative constant and a
starting height at least one.

This matches the hybrid-density quantifier order: the saving is chosen
before `a`, whereas the constant and height may depend on `a`.  The target
predicate only has to be monotone under decreasing the saving and increasing
the two auxiliary parameters. -/
theorem finite_uniformize_positive_saving_and_parameters
    {ι α : Type*} (s : Finset ι) (hs : s.Nonempty)
    (Q : ι → ℝ → α → ℝ → ℝ → Prop)
    (hlocal : ∀ i ∈ s,
      ∃ κ : ℝ, 0 < κ ∧
        ∀ a : α, ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧ Q i κ a C T₀)
    (hsaving : ∀ i ∈ s, ∀ a : α,
      ∀ {κ₀ κ C T₀ : ℝ},
        0 < C → 1 ≤ T₀ →
        0 < κ₀ → κ₀ ≤ κ → Q i κ a C T₀ → Q i κ₀ a C T₀)
    (hparameters : ∀ i ∈ s, ∀ a : α, ∀ κ : ℝ,
      ∀ {C T₀ C' T₀' : ℝ},
        0 < C → 1 ≤ T₀ → 0 < C' → 1 ≤ T₀' →
        Q i κ a C T₀ → C ≤ C' → T₀ ≤ T₀' → Q i κ a C' T₀') :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧
      ∀ a : α, ∃ C₀ T₀ : ℝ, 0 < C₀ ∧ 1 ≤ T₀ ∧
        ∀ i ∈ s, Q i κ₀ a C₀ T₀ := by
  classical
  let κ : ι → ℝ := fun i ↦
    if hi : i ∈ s then Classical.choose (hlocal i hi) else 1
  have hκpos : ∀ i ∈ s, 0 < κ i := by
    intro i hi
    simp only [κ, dite_eq_left hi]
    exact (Classical.choose_spec (hlocal i hi)).1
  have hκlocal : ∀ i ∈ s, ∀ a : α,
      ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧ Q i (κ i) a C T₀ := by
    intro i hi a
    simp only [κ, dite_eq_left hi]
    exact (Classical.choose_spec (hlocal i hi)).2 a
  let κ₀ : ℝ := s.inf' hs κ
  have hκ₀data : 0 < κ₀ ∧ ∀ i ∈ s, κ₀ ≤ κ i := by
    simpa only [κ₀] using finite_inf'_positive_and_le s hs κ hκpos
  refine ⟨κ₀, hκ₀data.1, ?_⟩
  intro a
  let C : ι → ℝ := fun i ↦
    if hi : i ∈ s then Classical.choose (hκlocal i hi a) else 1
  let T₀i : ι → ℝ := fun i ↦
    if hi : i ∈ s then
      Classical.choose (Classical.choose_spec (hκlocal i hi a))
    else 1
  have hCpos : ∀ i ∈ s, 0 < C i := by
    intro i hi
    simp only [C, dite_eq_left hi]
    exact (Classical.choose_spec
      (Classical.choose_spec (hκlocal i hi a))).1
  have hT₀one : ∀ i ∈ s, 1 ≤ T₀i i := by
    intro i hi
    simp only [T₀i, dite_eq_left hi]
    exact (Classical.choose_spec
      (Classical.choose_spec (hκlocal i hi a))).2.1
  have hQi : ∀ i ∈ s, Q i (κ i) a (C i) (T₀i i) := by
    intro i hi
    simp only [C, T₀i, dite_eq_left hi]
    exact (Classical.choose_spec
      (Classical.choose_spec (hκlocal i hi a))).2.2
  let C₀ : ℝ := s.sup' hs C
  let T₀ : ℝ := s.sup' hs T₀i
  have hsup := finite_sup'_positive_one_le_and_bounds
    s hs C T₀i hCpos hT₀one
  refine ⟨C₀, T₀, ?_, ?_, ?_⟩
  · simpa only [C₀] using hsup.1
  · simpa only [T₀] using hsup.2.1
  · intro i hi
    have hQsmall : Q i κ₀ a (C i) (T₀i i) :=
      hsaving i hi a (hCpos i hi) (hT₀one i hi)
        hκ₀data.1 (hκ₀data.2 i hi) (hQi i hi)
    apply hparameters i hi a κ₀
      (hCpos i hi) (hT₀one i hi) hsup.1 hsup.2.1 hQsmall
    · simpa only [C₀] using hsup.2.2 i hi |>.1
    · simpa only [T₀] using hsup.2.2 i hi |>.2

/-- The bounded set of convolution orders used by finite uniformization. -/
def boundedOrders (K : ℕ) : Finset ℕ := Finset.Icc 1 K

theorem boundedOrders_nonempty {K : ℕ} (hK : 1 ≤ K) :
    (boundedOrders K).Nonempty := by
  exact Finset.nonempty_Icc.mpr hK

theorem mem_boundedOrders {K ell : ℕ} :
    ell ∈ boundedOrders K ↔ 1 ≤ ell ∧ ell ≤ K := by
  exact Finset.mem_Icc

/-- Orders together with slice indices `j < ell`.  This is available when
parameters vary with both pieces of discrete data. -/
def boundedOrderSlicePairs (K : ℕ) : Finset (ℕ × ℕ) :=
  ((boundedOrders K).product (Finset.range K)).filter fun p ↦ p.2 < p.1

theorem boundedOrderSlicePairs_nonempty {K : ℕ} (hK : 1 ≤ K) :
    (boundedOrderSlicePairs K).Nonempty := by
  have hKpos : 0 < K := Nat.zero_lt_of_lt hK
  refine ⟨(1, 0), ?_⟩
  simp [boundedOrderSlicePairs, mem_boundedOrders, hK, hKpos]

theorem mem_boundedOrderSlicePairs {K ell j : ℕ} :
    (ell, j) ∈ boundedOrderSlicePairs K ↔
      1 ≤ ell ∧ ell ≤ K ∧ j < ell := by
  constructor
  · intro h
    have hp := Finset.mem_filter.mp h
    have hproduct := Finset.mem_product.mp hp.1
    exact ⟨(mem_boundedOrders.mp hproduct.1).1,
      (mem_boundedOrders.mp hproduct.1).2, hp.2⟩
  · rintro ⟨hell1, hellK, hjell⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨mem_boundedOrders.mpr ⟨hell1, hellK⟩, ?_⟩, hjell⟩
    exact Finset.mem_range.mpr (hjell.trans_le hellK)

/-! ## Specialization to the prepared powered medium branch -/

/-- The universal tail of `MediumPreparedPoweredFirstBranchStatement`, with
the coefficient scale and its lower bound represented by a subtype. -/
def MediumPreparedPoweredAt
    (thresholdLoss B eps : ℝ) (ell : ℕ) (κ : ℝ)
    (A : {x : ℝ // 1 ≤ x}) (C T₀ : ℝ) : Prop :=
  ∀ (T : ℝ) (M P : ℕ) (tau₁ tau₂ : ℝ) (a₁ : ℕ → ℂ)
      (R : Finset ℝ),
    T₀ ≤ T → 1 ≤ M → 1 ≤ P →
    T ^ (9 / 11 - 10 * eps) ≤ (P : ℝ) →
    (P : ℝ) ≤ T ^ (1 - eps / 10) →
    10 * eps ≤ tau₁ →
    tau₁ ≤ 17 / 70 - thresholdLoss * eps →
    tau₁ ≤ tau₂ →
    IsDivisorBoundedByConstant B A.1 a₁ →
    IsOneSpaced (↑R : Set ℝ) →
    (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
    (∀ t ∈ R,
      (P : ℝ) ^ (-tau₁) <
        ‖dyadicDirichletPolynomial
          (powerConvolutionCoefficient a₁
            (dyadicInterval (M : ℝ)) ell)
          (P : ℝ) (onePlusIT t)‖) →
    (R.card : ℝ) ≤ C * T ^ (2 * min tau₁ tau₂ - κ)

/-- For each fixed upper order `K`, one `κ`, `C`, and `T₀` work for every
`1 ≤ ell ≤ K`.  This is a purely finite uniformization of the existing
prepared branch and introduces no new analytic input. -/
theorem mediumPreparedPoweredFirstBranch_uniform_boundedOrders
    (hPrepared : MediumPreparedPoweredFirstBranchStatement) :
    ∃ thresholdLoss : ℝ, 0 < thresholdLoss ∧
      ∀ K : ℕ, 1 ≤ K →
        ∀ B : ℝ, 0 ≤ B →
          ∀ eps : ℝ, 0 < eps → eps ≤ 1 / 1000 →
            ∃ κ : ℝ, 0 < κ ∧
              ∀ A : ℝ, ∀ hA : 1 ≤ A,
                ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧
                  ∀ ell : ℕ, 1 ≤ ell → ell ≤ K →
                    MediumPreparedPoweredAt
                      thresholdLoss B eps ell κ ⟨A, hA⟩ C T₀ := by
  classical
  obtain ⟨thresholdLoss, hthresholdLoss, hPrepared⟩ := hPrepared
  refine ⟨thresholdLoss, hthresholdLoss, ?_⟩
  intro K hK B hB eps heps hepsSmall
  let s : Finset ℕ := boundedOrders K
  have hs : s.Nonempty := by
    simpa only [s] using boundedOrders_nonempty hK
  let Scale := {A : ℝ // 1 ≤ A}
  let Q : ℕ → ℝ → Scale → ℝ → ℝ → Prop := fun ell κ A C T₀ ↦
    MediumPreparedPoweredAt thresholdLoss B eps ell κ A C T₀
  have hlocal : ∀ ell ∈ s,
      ∃ κ : ℝ, 0 < κ ∧
        ∀ A : Scale, ∃ C T₀ : ℝ, 0 < C ∧ 1 ≤ T₀ ∧ Q ell κ A C T₀ := by
    intro ell hell
    have hellBounds : 1 ≤ ell ∧ ell ≤ K := by
      exact mem_boundedOrders.mp (by simpa only [s] using hell)
    obtain ⟨κ, hκ, hdata⟩ :=
      hPrepared ell hellBounds.1 B hB eps heps hepsSmall
    refine ⟨κ, hκ, ?_⟩
    intro A
    obtain ⟨C, T₀, hC, hT₀, htail⟩ := hdata A.1 A.2
    exact ⟨C, T₀, hC, hT₀, by
      simpa only [Q, MediumPreparedPoweredAt] using htail⟩
  have hsaving : ∀ ell ∈ s, ∀ A : Scale,
      ∀ {κ₀ κ C T₀ : ℝ},
        0 < C → 1 ≤ T₀ →
        0 < κ₀ → κ₀ ≤ κ → Q ell κ A C T₀ → Q ell κ₀ A C T₀ := by
    intro ell hell A κ₀ κ C T₀ hC hT₀ hκ₀ hκle hQ
      T M P tau₁ tau₂ a₁ R hT hM hP hPlower hPupper
      htau₁lower htau₁upper horder ha₁ hspaced hR hlarge
    have hbound := hQ T M P tau₁ tau₂ a₁ R hT hM hP hPlower hPupper
      htau₁lower htau₁upper horder ha₁ hspaced hR hlarge
    have hTone : 1 ≤ T := hT₀.trans hT
    have hexponent :
        2 * min tau₁ tau₂ - κ ≤ 2 * min tau₁ tau₂ - κ₀ := by
      linarith
    have hpower :
        T ^ (2 * min tau₁ tau₂ - κ) ≤
          T ^ (2 * min tau₁ tau₂ - κ₀) :=
      Real.rpow_le_rpow_of_exponent_le hTone hexponent
    exact hbound.trans (mul_le_mul_of_nonneg_left hpower hC.le)
  have hparameters : ∀ ell ∈ s, ∀ A : Scale, ∀ κ : ℝ,
      ∀ {C T₀ C' T₀' : ℝ},
        0 < C → 1 ≤ T₀ → 0 < C' → 1 ≤ T₀' →
        Q ell κ A C T₀ → C ≤ C' → T₀ ≤ T₀' → Q ell κ A C' T₀' := by
    intro ell hell A κ C T₀ C' T₀' hC hT₀ hC' hT₀' hQ hCC' hT₀T₀'
      T M P tau₁ tau₂ a₁ R hT hM hP hPlower hPupper
      htau₁lower htau₁upper horder ha₁ hspaced hR hlarge
    have hbound := hQ T M P tau₁ tau₂ a₁ R (hT₀T₀'.trans hT)
      hM hP hPlower hPupper htau₁lower htau₁upper horder
      ha₁ hspaced hR hlarge
    exact hbound.trans
      (mul_le_mul_of_nonneg_right hCC'
        (Real.rpow_nonneg ((zero_le_one.trans hT₀').trans hT)
          (2 * min tau₁ tau₂ - κ)))
  obtain ⟨κ, hκ, huniform⟩ :=
    finite_uniformize_positive_saving_and_parameters
      s hs Q hlocal hsaving hparameters
  refine ⟨κ, hκ, ?_⟩
  intro A hA
  obtain ⟨C, T₀, hC, hT₀, htail⟩ :=
    huniform (⟨A, hA⟩ : Scale)
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro ell hell1 hellK
  exact htail ell (by
    simpa only [s] using mem_boundedOrders.mpr ⟨hell1, hellK⟩)

def mediumFiniteUniformizationModule : ProofModule :=
  { name := "TypeII.MediumFiniteUniformization"
    paperLocation :=
      "Proof of Proposition 5.1, powered R₂ branch: uniform constants"
    purpose :=
      "Take a positive finite minimum of the order-dependent power savings and finite maxima of the constants and starting heights, preserving the hybrid-density quantifier order for every bounded convolution power."
    dependsOn := ["TypeII.MediumRangeCardinality"]
    status := .proved }

end

end TypeII
end ExactSemiprimes
