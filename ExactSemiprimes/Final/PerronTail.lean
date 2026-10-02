import ExactSemiprimes.Completion.PerronFiniteSupportBounds
import ExactSemiprimes.Completion.ComplementOfU

/-!
# Large heights: the mean value theorem and the unique small prime factor

For heights `T ≥ X` the Perron product is handled by the ordinary mean value
theorem ([MT23, Lemma 3.2] = [IK04, Theorem 9.1]).  The decisive point
(paper, proof of Proposition 7.1) is that the minorant `ρ⁻` is supported on
`X^(2/11)`-rough integers, so a product `m = p n` with `p ∼ P` small has a
*unique* such factorization; hence every convolution coefficient is bounded
by the absolute constant `5324`, not by `≍ P`.
-/

namespace ExactSemiprimes
namespace Final

open Filter Real MeasureTheory
open scoped BigOperators

noncomputable section

/-! ## The minorant is supported on rough integers -/

theorem roughIndicator_eq_zero_of_dvd {p m : ℕ} {z : ℝ} (hp : p.Prime)
    (hpz : (p : ℝ) < z) (hpm : p ∣ m) :
    matomakiTeravainenRoughIndicator m z = 0 := by
  classical
  unfold matomakiTeravainenRoughIndicator
  exact ite_eq_right (fun h ↦ h p hp hpz hpm)

theorem roughIndicator_div_eq_zero {p n d : ℕ} {z : ℝ} (hp : p.Prime)
    (hpz : (p : ℝ) < z) (hpn : p ∣ n) (hdn : d ∣ n) (hcop : Nat.Coprime p d) :
    matomakiTeravainenRoughIndicator (n / d) z = 0 := by
  apply roughIndicator_eq_zero_of_dvd hp hpz
  obtain ⟨k, hk⟩ := hdn
  have hdpos : 0 < d ∨ d = 0 := by omega
  rcases hdpos with hd | hd
  · rw [hk, Nat.mul_div_cancel_left _ hd]
    rw [hk] at hpn
    exact (Nat.Coprime.dvd_of_dvd_mul_left hcop hpn)
  · subst hd; simp at hk; subst hk; simp

theorem coprime_of_prime_lt_le {p q : ℕ} {z : ℝ} (hp : p.Prime) (hq : q.Prime)
    (hpz : (p : ℝ) < z) (hzq : z ≤ (q : ℝ)) : Nat.Coprime p q := by
  rw [Nat.coprime_primes hp hq]
  intro h
  subst h
  linarith

/-- If a prime `p < z` divides `n`, the four-term minorant vanishes at `n`. -/
theorem matomakiTeravainenMinorant_eq_zero_of_small_prime_dvd
    {X ε : ℝ} {n p : ℕ} (hp : p.Prime)
    (hpz : (p : ℝ) < X ^ (2 / 11 : ℝ)) (hpn : p ∣ n) :
    matomakiTeravainenMinorant X ε n = 0 := by
  classical
  unfold matomakiTeravainenMinorant
  simp only
  have h0 : matomakiTeravainenRoughIndicator n (X ^ (2 / 11 : ℝ)) = 0 :=
    roughIndicator_eq_zero_of_dvd hp hpz hpn
  have h1 : (∑ q ∈ Finset.range (n + 1),
      if q.Prime ∧ X ^ (2 / 11 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) < 2 * X ^ (1 / 2 : ℝ) ∧ q ∣ n
      then matomakiTeravainenRoughIndicator (n / q) (X ^ (2 / 11 : ℝ)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    split_ifs with hq
    · exact roughIndicator_div_eq_zero hp hpz hpn hq.2.2.2
        (coprime_of_prime_lt_le hp hq.1 hpz hq.2.1)
    · rfl
  have h2 : (∑ q₁ ∈ Finset.range (n + 1), ∑ q₂ ∈ Finset.range (n + 1),
      if q₁.Prime ∧ q₂.Prime ∧ X ^ (2 / 11 : ℝ) ≤ (q₂ : ℝ) ∧ (q₂ : ℝ) < (q₁ : ℝ) ∧
          (q₁ : ℝ) < X ^ (1 / 4 - 2 * ε) ∧
          (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) < X ^ (1 - 2 * ε) ∧ q₁ * q₂ ∣ n
      then matomakiTeravainenRoughIndicator (n / (q₁ * q₂)) (X ^ (2 / 11 : ℝ))
      else 0) = 0 := by
    apply Finset.sum_eq_zero; intro q₁ _
    apply Finset.sum_eq_zero; intro q₂ _
    split_ifs with hq
    · obtain ⟨hq₁, hq₂, hzq₂, hq₂q₁, _, _, hdvd⟩ := hq
      apply roughIndicator_div_eq_zero hp hpz hpn hdvd
      exact Nat.Coprime.mul_right
        (coprime_of_prime_lt_le hp hq₁ hpz (hzq₂.trans hq₂q₁.le))
        (coprime_of_prime_lt_le hp hq₂ hpz hzq₂)
    · rfl
  have h3 : (∑ q₁ ∈ Finset.range (n + 1), ∑ q₂ ∈ Finset.range (n + 1),
      ∑ q₃ ∈ Finset.range (n + 1),
      if q₁.Prime ∧ q₂.Prime ∧ q₃.Prime ∧ X ^ (2 / 11 : ℝ) ≤ (q₃ : ℝ) ∧
          (q₃ : ℝ) < (q₂ : ℝ) ∧ (q₂ : ℝ) < (q₁ : ℝ) ∧
          (q₁ : ℝ) < X ^ (1 / 4 - 2 * ε) ∧
          (q₁ : ℝ) * (q₂ : ℝ) ^ (4 : ℕ) < X ^ (1 - 2 * ε) ∧ q₁ * q₂ * q₃ ∣ n
      then matomakiTeravainenRoughIndicator (n / (q₁ * q₂ * q₃)) (X ^ (2 / 11 : ℝ))
      else 0) = 0 := by
    apply Finset.sum_eq_zero; intro q₁ _
    apply Finset.sum_eq_zero; intro q₂ _
    apply Finset.sum_eq_zero; intro q₃ _
    split_ifs with hq
    · obtain ⟨hq₁, hq₂, hq₃, hzq₃, hq₃q₂, hq₂q₁, _, _, hdvd⟩ := hq
      apply roughIndicator_div_eq_zero hp hpz hpn hdvd
      exact Nat.Coprime.mul_right (Nat.Coprime.mul_right
        (coprime_of_prime_lt_le hp hq₁ hpz ((hzq₃.trans hq₃q₂.le).trans hq₂q₁.le))
        (coprime_of_prime_lt_le hp hq₂ hpz (hzq₃.trans hq₃q₂.le)))
        (coprime_of_prime_lt_le hp hq₃ hpz hzq₃)
    · rfl
  rw [h0, h1, h2, h3]
  ring

/-! ## Unique factorization through the small prime -/

/-- If the weight is supported on integers with no prime factor in
`(P,2P]`, each product coefficient comes from at most one factorization. -/
theorem norm_perronProductCoefficient_le_of_rough
    (w : ℕ → ℝ) (X P K : ℝ) (m : ℕ) (hK : 0 ≤ K)
    (hw : ∀ n ∈ natOpenClosedInterval (X / (2 * P)) (4 * X / P),
      ‖(w n : ℂ)‖ ≤ K)
    (hrough : ∀ n ∈ natOpenClosedInterval (X / (2 * P)) (4 * X / P),
      w n ≠ 0 → ∀ p ∈ dyadicPrimes P, ¬ p ∣ n) :
    ‖Completion.perronProductCoefficient w X P m‖ ≤ K := by
  classical
  let S₁ : Finset ℕ := dyadicPrimes P
  let S₂ : Finset ℕ := natOpenClosedInterval (X / (2 * P)) (4 * X / P)
  let fiber : Finset (ℕ × ℕ) := (S₁.product S₂).filter (fun pn ↦ pn.1 * pn.2 = m)
  let fiber' : Finset (ℕ × ℕ) := fiber.filter (fun pn ↦ (1 : ℂ) * (w pn.2 : ℂ) ≠ 0)
  have hsum : (∑ pn ∈ fiber, (1 : ℂ) * (w pn.2 : ℂ)) =
      ∑ pn ∈ fiber', (1 : ℂ) * (w pn.2 : ℂ) := by
    rw [Finset.sum_filter_ne_zero]
  have hcard : fiber'.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have haf := Finset.mem_filter.mp ha'.1
    have hbf := Finset.mem_filter.mp hb'.1
    have haprod := Finset.mem_product.mp haf.1
    have hbprod := Finset.mem_product.mp hbf.1
    have hapr : a.1.Prime := (Finset.mem_filter.mp haprod.1).2
    have hbpr : b.1.Prime := (Finset.mem_filter.mp hbprod.1).2
    have hwa : w a.2 ≠ 0 := by
      intro h; apply ha'.2; simp [h]
    have hwb : w b.2 ≠ 0 := by
      intro h; apply hb'.2; simp [h]
    have heq : a.1 * a.2 = b.1 * b.2 := haf.2.trans hbf.2.symm
    by_cases hab : a.1 = b.1
    · apply Prod.ext hab
      apply Nat.mul_left_cancel hapr.pos
      rw [heq, hab]
    · exfalso
      -- `b.1` divides `a.1 * a.2` but not `a.1`, hence divides `a.2`.
      have hdvd : b.1 ∣ a.1 * a.2 := ⟨b.2, heq⟩
      have hcop : Nat.Coprime b.1 a.1 := (Nat.coprime_primes hbpr hapr).mpr (Ne.symm hab)
      have hdvd2 : b.1 ∣ a.2 := hcop.dvd_of_dvd_mul_left hdvd
      exact hrough a.2 haprod.2 hwa b.1 hbprod.1 hdvd2
  unfold Completion.perronProductCoefficient Sparse.binaryConvolutionCoefficient
  change ‖∑ pn ∈ fiber, (1 : ℂ) * (w pn.2 : ℂ)‖ ≤ K
  rw [hsum]
  calc ‖∑ pn ∈ fiber', (1 : ℂ) * (w pn.2 : ℂ)‖
      ≤ ∑ pn ∈ fiber', ‖(1 : ℂ) * (w pn.2 : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _pn ∈ fiber', K := by
        apply Finset.sum_le_sum
        intro pn hpn
        have hmem := (Finset.mem_product.mp
          (Finset.mem_filter.mp (Finset.mem_filter.mp hpn).1).1).2
        simpa using hw pn.2 hmem
    _ = (fiber'.card : ℝ) * K := by simp
    _ ≤ 1 * K := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hK
    _ = K := one_mul K

/-! ## Changing to the zero line -/

theorem dirichletPolynomial_onePlusIT_eq_initial
    (a : ℕ → ℂ) (S : Finset ℕ) {N : ℝ} (hN : 0 ≤ N)
    (hS : ∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ N) (t : ℝ) :
    dirichletPolynomial a S (onePlusIT t) =
      matomakiTeravainenInitialDirichletPolynomial
        (fun n ↦ if n ∈ S then a n / (n : ℂ) else 0) N ((t : ℂ) * Complex.I) := by
  classical
  have hsubset : S ⊆ natOpenClosedInterval 0 N := by
    intro n hn
    rw [mem_natOpenClosedInterval (le_refl 0) hN]
    exact ⟨by exact_mod_cast (hS n hn).1, (hS n hn).2⟩
  simp only [matomakiTeravainenInitialDirichletPolynomial, dirichletPolynomial]
  rw [← Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro n hn
    have hnpos := (hS n hn).1
    have hnzero : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hnpos)
    have hexponent : -onePlusIT t = (-1 : ℂ) + (-((t : ℂ) * Complex.I)) := by
      simp only [onePlusIT]; ring
    simp only [hn, ↓reduceIte]
    rw [hexponent, Complex.cpow_add _ _ hnzero, Complex.cpow_neg_one]
    field_simp
  · intro n _ hnS
    simp [hnS]

/-! ## Mean square of the Perron product over `[-T,T]` -/

/-- Mean value theorem for the Perron product, assuming a coefficient bound
`K` on its support. -/
theorem perronProduct_meanSquare_le
    {CMV : ℝ} (hCMV : 0 < CMV)
    (hMV : ∀ (N T : ℝ) (a : ℕ → ℂ), 1 ≤ N → 1 ≤ T →
      |(∫ t in Set.Icc (-T) T,
          ‖matomakiTeravainenInitialDirichletPolynomial a N
              ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)) -
        2 * T * (∑ n ∈ natOpenClosedInterval 0 N, ‖a n‖ ^ (2 : ℕ))| ≤
      CMV * N * (∑ n ∈ natOpenClosedInterval 0 N, ‖a n‖ ^ (2 : ℕ)))
    (w : ℕ → ℝ) {X P K T : ℝ} (hX : 1 ≤ X) (hP : 0 < P) (_hK : 0 ≤ K)
    (hT : 1 ≤ T)
    (hcoeff : ∀ m ∈ Completion.perronProductSupport X P,
      ‖Completion.perronProductCoefficient w X P m‖ ≤ K) :
    (∫ t in Set.Icc (-T) T,
        ‖Completion.perronProduct w X P t‖ ^ (2 : ℕ)) ≤
      (2 * T + CMV * (8 * X)) * (32 * K ^ 2 / X) := by
  classical
  have hXpos : 0 < X := by linarith
  set S := Completion.perronProductSupport X P with hSdef
  set b := Completion.perronProductCoefficient w X P with hbdef
  have hSrange : ∀ m ∈ S, 0 < m ∧ (m : ℝ) ≤ 8 * X := by
    intro m hm
    have h := Completion.perronProductSupport_mem_range hXpos hP hm
    refine ⟨?_, h.2⟩
    have : (0 : ℝ) < m := lt_trans (by positivity) h.1
    exact_mod_cast this
  let a : ℕ → ℂ := fun n ↦ if n ∈ S then b n / (n : ℂ) else 0
  have hline : ∀ t : ℝ, Completion.perronProduct w X P t =
      matomakiTeravainenInitialDirichletPolynomial a (8 * X)
        ((t : ℂ) * Complex.I) := by
    intro t
    rw [Completion.perronProduct_eq_convolutionPolynomial]
    exact dirichletPolynomial_onePlusIT_eq_initial b S (by positivity) hSrange t
  have hint : (∫ t in Set.Icc (-T) T, ‖Completion.perronProduct w X P t‖ ^ (2 : ℕ)) =
      ∫ t in Set.Icc (-T) T, ‖matomakiTeravainenInitialDirichletPolynomial a (8 * X)
        ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ) := by
    congr 1; funext t; rw [hline t]
  -- the coefficient energy
  have henergy : (∑ n ∈ natOpenClosedInterval 0 (8 * X), ‖a n‖ ^ (2 : ℕ)) ≤
      32 * K ^ 2 / X := by
    have hsub : S ⊆ natOpenClosedInterval 0 (8 * X) := by
      intro m hm
      rw [mem_natOpenClosedInterval (le_refl 0) (by positivity)]
      exact ⟨by exact_mod_cast (hSrange m hm).1, (hSrange m hm).2⟩
    have hzero : ∀ n ∈ natOpenClosedInterval 0 (8 * X), n ∉ S → ‖a n‖ ^ (2 : ℕ) = 0 := by
      intro n _ hn; simp [a, hn]
    rw [← Finset.sum_subset hsub hzero]
    have hterm : ∀ m ∈ S, ‖a m‖ ^ (2 : ℕ) ≤ 4 * K ^ 2 / X ^ 2 := by
      intro m hm
      have hmr := Completion.perronProductSupport_mem_range hXpos hP hm
      have hmpos : (0 : ℝ) < m := lt_trans (by positivity) hmr.1
      simp only [a, hm, ↓reduceIte, norm_div, Complex.norm_natCast]
      rw [div_pow]
      have hbm := hcoeff m hm
      have hb2 : ‖b m‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbm 2
      have hm2 : (X / 2) ^ 2 ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hmr.1.le 2
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc (∑ m ∈ S, ‖a m‖ ^ (2 : ℕ)) ≤ ∑ _m ∈ S, 4 * K ^ 2 / X ^ 2 := Finset.sum_le_sum hterm
      _ = (S.card : ℝ) * (4 * K ^ 2 / X ^ 2) := by simp
      _ ≤ (8 * X) * (4 * K ^ 2 / X ^ 2) :=
          mul_le_mul_of_nonneg_right (Completion.perronProductSupport_card_cast_le hXpos hP)
            (by positivity)
      _ = 32 * K ^ 2 / X := by field_simp; ring
  have hmv := hMV (8 * X) T a (by linarith) hT
  rw [hint]
  have hE0 : 0 ≤ ∑ n ∈ natOpenClosedInterval 0 (8 * X), ‖a n‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg (fun _ _ ↦ by positivity)
  have h1 := (abs_le.mp hmv).2
  have h2 : 2 * T * (∑ n ∈ natOpenClosedInterval 0 (8 * X), ‖a n‖ ^ (2 : ℕ)) +
      CMV * (8 * X) * (∑ n ∈ natOpenClosedInterval 0 (8 * X), ‖a n‖ ^ (2 : ℕ)) =
      (2 * T + CMV * (8 * X)) *
        (∑ n ∈ natOpenClosedInterval 0 (8 * X), ‖a n‖ ^ (2 : ℕ)) := by ring
  have h3 := mul_le_mul_of_nonneg_left henergy
    (by positivity : (0 : ℝ) ≤ 2 * T + CMV * (8 * X))
  linarith

/-! ## The minorant product coefficients are bounded by `5324` -/

theorem minorant_productCoefficient_le_5324
    {X P ε εₘₐₓ : ℝ} (hX : 3 ≤ X) (hP : 0 < P) (hε : 0 < ε) (hεmax : ε ≤ εₘₐₓ)
    (heq24 : ∀ ε : ℝ, 0 < ε → ε ≤ εₘₐₓ →
      ∀ X : ℝ, 3 ≤ X → ∀ n : ℕ,
        2 * X ^ (1 / 2 : ℝ) ≤ (n : ℝ) → (n : ℝ) ≤ 3 * X →
          |matomakiTeravainenMinorant X ε n| ≤
            Completion.sectionFiveMinorantMajorant X *
              matomakiTeravainenRoughIndicator n (X ^ (2 / 11 : ℝ)))
    (hlower : 2 * X ^ (1 / 2 : ℝ) ≤ X / (2 * P))
    (hupper : 4 * X / P ≤ 3 * X)
    (hPz : 2 * P < X ^ (2 / 11 : ℝ)) (m : ℕ) :
    ‖Completion.perronProductCoefficient (matomakiTeravainenMinorant X ε) X P m‖ ≤
      5324 := by
  apply norm_perronProductCoefficient_le_of_rough _ X P 5324 m (by norm_num)
  · exact Completion.minorant_norm_le_5324_on_perronSupport hX hP hε hεmax heq24
      hlower hupper
  · intro n _ hw p hp hpn
    apply hw
    have hpr : p.Prime := (Finset.mem_filter.mp hp).2
    have hprange := (mem_dyadicInterval hP.le).mp (Finset.mem_filter.mp hp).1
    exact matomakiTeravainenMinorant_eq_zero_of_small_prime_dvd hpr
      (lt_of_le_of_lt hprange.2 hPz) hpn

/-! ## The remainder of the decomposition -/

theorem remainder_meanSquare_le
    {CMV : ℝ} (hCMV : 0 < CMV)
    (hMV : ∀ (N T : ℝ) (a : ℕ → ℂ), 1 ≤ N → 1 ≤ T →
      |(∫ t in Set.Icc (-T) T,
          ‖matomakiTeravainenInitialDirichletPolynomial a N
              ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ)) -
        2 * T * (∑ n ∈ natOpenClosedInterval 0 N, ‖a n‖ ^ (2 : ℕ))| ≤
      CMV * N * (∑ n ∈ natOpenClosedInterval 0 N, ‖a n‖ ^ (2 : ℕ)))
    (c : ℕ → ℂ) {Y Bc T : ℝ} (hY : 1 ≤ Y) (hT : 1 ≤ T)
    (hc : (∑ n ∈ natOpenClosedInterval (Y / 4) (8 * Y), ‖c n‖ ^ (2 : ℕ)) ≤ Bc) :
    (∫ t in Set.Icc (-T) T,
        ‖dirichletPolynomial c (natOpenClosedInterval (Y / 4) (8 * Y))
          (onePlusIT t)‖ ^ (2 : ℕ)) ≤
      (2 * T + CMV * (8 * Y)) * (16 * Bc / Y ^ 2) := by
  classical
  have hYpos : 0 < Y := by linarith
  set S := natOpenClosedInterval (Y / 4) (8 * Y) with hSdef
  have hSrange : ∀ m ∈ S, 0 < m ∧ (m : ℝ) ≤ 8 * Y := by
    intro m hm
    have h := (mem_natOpenClosedInterval (by positivity) (by positivity)).mp hm
    refine ⟨?_, h.2⟩
    have : (0 : ℝ) < m := lt_trans (by positivity) h.1
    exact_mod_cast this
  let a : ℕ → ℂ := fun n ↦ if n ∈ S then c n / (n : ℂ) else 0
  have hint : (∫ t in Set.Icc (-T) T,
        ‖dirichletPolynomial c S (onePlusIT t)‖ ^ (2 : ℕ)) =
      ∫ t in Set.Icc (-T) T, ‖matomakiTeravainenInitialDirichletPolynomial a (8 * Y)
        ((t : ℂ) * Complex.I)‖ ^ (2 : ℕ) := by
    congr 1; funext t
    rw [dirichletPolynomial_onePlusIT_eq_initial c S (by positivity) hSrange t]
  have henergy : (∑ n ∈ natOpenClosedInterval 0 (8 * Y), ‖a n‖ ^ (2 : ℕ)) ≤
      16 * Bc / Y ^ 2 := by
    have hsub : S ⊆ natOpenClosedInterval 0 (8 * Y) := by
      intro m hm
      rw [mem_natOpenClosedInterval (le_refl 0) (by positivity)]
      exact ⟨by exact_mod_cast (hSrange m hm).1, (hSrange m hm).2⟩
    have hzero : ∀ n ∈ natOpenClosedInterval 0 (8 * Y), n ∉ S →
        ‖a n‖ ^ (2 : ℕ) = 0 := by
      intro n _ hn; simp [a, hn]
    rw [← Finset.sum_subset hsub hzero]
    have hterm : ∀ m ∈ S, ‖a m‖ ^ (2 : ℕ) ≤ (16 / Y ^ 2) * ‖c m‖ ^ (2 : ℕ) := by
      intro m hm
      have hmr := (mem_natOpenClosedInterval (by positivity) (by positivity)).mp hm
      have hmpos : (0 : ℝ) < m := lt_trans (by positivity) hmr.1
      simp only [a, hm, ↓reduceIte, norm_div, Complex.norm_natCast]
      rw [div_pow]
      have hm2 : (Y / 4) ^ 2 ≤ (m : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hmr.1.le 2
      rw [div_le_iff₀ (by positivity)]
      have hc0 : 0 ≤ ‖c m‖ ^ 2 := by positivity
      have : 16 / Y ^ 2 * (m : ℝ) ^ 2 ≥ 1 := by
        rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith
      nlinarith
    calc (∑ m ∈ S, ‖a m‖ ^ (2 : ℕ)) ≤ ∑ m ∈ S, (16 / Y ^ 2) * ‖c m‖ ^ (2 : ℕ) :=
          Finset.sum_le_sum hterm
      _ = (16 / Y ^ 2) * ∑ m ∈ S, ‖c m‖ ^ (2 : ℕ) := by rw [Finset.mul_sum]
      _ ≤ (16 / Y ^ 2) * Bc := mul_le_mul_of_nonneg_left hc (by positivity)
      _ = 16 * Bc / Y ^ 2 := by ring
  have hmv := hMV (8 * Y) T a (by linarith) hT
  rw [hint]
  have hE0 : 0 ≤ ∑ n ∈ natOpenClosedInterval 0 (8 * Y), ‖a n‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg (fun _ _ ↦ by positivity)
  have h1 := (abs_le.mp hmv).2
  have h3 := mul_le_mul_of_nonneg_left henergy
    (by positivity : (0 : ℝ) ≤ 2 * T + CMV * (8 * Y))
  nlinarith

end

end Final
end ExactSemiprimes
