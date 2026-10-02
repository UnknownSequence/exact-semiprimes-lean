import ExactSemiprimes.Assumptions

/-! # Passage from one-spaced large values to a measurable set -/

namespace ExactSemiprimes
namespace Hybrid

noncomputable section

open Set MeasureTheory
open scoped ENNReal

/-!
The analytic large-values estimates in the paper count finite one-spaced
sets, whereas their applications integrate over a set of ordinates.  This
file keeps the two logically distinct ingredients visible:

* a completely elementary maximal-separated-set covering argument; and
* an optional sampling hypothesis saying that every point of a target set
  lies within distance one of a point in a sampled set.

The second item is a theorem hypothesis, not an imported axiom.  In the
same-threshold application it is automatic (take the same point).  If one
wants to sample a lower threshold by a stronger threshold, proving that
hypothesis is precisely the local analytic persistence obligation.
-/

/-- Every point of `E` has a representative in `S` at real distance at most
one.  This is the exact local sampling/persistence property used below. -/
def HasUnitSampling (E S : Set ℝ) : Prop :=
  ∀ t ∈ E, ∃ u ∈ S, |t - u| ≤ 1

theorem hasUnitSampling_self (E : Set ℝ) : HasUnitSampling E E := by
  intro t ht
  exact ⟨t, ht, by simp⟩

/-- Explicit thresholded version of the local sampling obligation.  The
target threshold and the sampled threshold are deliberately independent. -/
def HasUnitLargeValueSampling (A : ℂ → ℂ) (T Vtarget Vsample : ℝ) : Prop :=
  HasUnitSampling (largeValueSet A T Vtarget) (largeValueSet A T Vsample)

theorem hasUnitLargeValueSampling_same (A : ℂ → ℂ) (T V : ℝ) :
    HasUnitLargeValueSampling A T V V :=
  hasUnitSampling_self _

/-! ## Explicit regularity of a dyadic Dirichlet polynomial -/

/-- The exact Lipschitz constant obtained by differentiating the individual
terms of a dyadic Dirichlet polynomial on `Re(s)=1`.  It retains every
coefficient and logarithmic factor, rather than hiding them in `O`-notation. -/
def dyadicDirichletLipschitzConstant (a : ℕ → ℂ) (N : ℝ) : ℝ :=
  ∑ n ∈ dyadicInterval N,
    ‖a n‖ * (Real.log (n : ℝ) / (n : ℝ))

/-- On the line `1+it`, a single Dirichlet monomial is a circle map of
radius `1/n` and angular speed `log n`. -/
theorem cpow_neg_onePlusIT_eq_circleMap {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (n : ℂ) ^ (-onePlusIT t) =
      circleMap 0 ((n : ℝ)⁻¹) (-t * Real.log (n : ℝ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Nat.ne_of_gt hn))]
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    exact (Complex.ofReal_log (Nat.cast_nonneg n)).symm
  rw [hlog]
  have hexponent :
      (Real.log (n : ℝ) : ℂ) * -onePlusIT t =
        ((-Real.log (n : ℝ) : ℝ) : ℂ) +
          ((-t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [onePlusIT] <;> ring
  rw [hexponent, Complex.exp_add]
  rw [← Complex.ofReal_exp, Real.exp_neg,
    Real.exp_log (Nat.cast_pos.mpr hn)]
  simp [circleMap]

/-- Lipschitz estimate for one monomial. -/
theorem norm_cpow_neg_onePlusIT_sub_le {n : ℕ} (hn : 0 < n)
    (t u : ℝ) :
    ‖(n : ℂ) ^ (-onePlusIT t) - (n : ℂ) ^ (-onePlusIT u)‖ ≤
      (Real.log (n : ℝ) / (n : ℝ)) * |t - u| := by
  rw [cpow_neg_onePlusIT_eq_circleMap hn t,
    cpow_neg_onePlusIT_eq_circleMap hn u]
  have h := (lipschitzWith_circleMap 0 ((n : ℝ)⁻¹)).norm_sub_le
    (-t * Real.log (n : ℝ)) (-u * Real.log (n : ℝ))
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  rw [Real.coe_nnabs, abs_of_nonneg (inv_nonneg.mpr hnreal.le),
    Real.norm_eq_abs] at h
  calc
    ‖circleMap 0 (↑n)⁻¹ (-t * Real.log ↑n) -
        circleMap 0 (↑n)⁻¹ (-u * Real.log ↑n)‖
        ≤ (n : ℝ)⁻¹ * |-t * Real.log (n : ℝ) -
            (-u * Real.log (n : ℝ))| := h
    _ = Real.log (n : ℝ) / (n : ℝ) * |t - u| := by
      rw [show -t * Real.log (n : ℝ) - (-u * Real.log (n : ℝ)) =
        -(t - u) * Real.log (n : ℝ) by ring]
      rw [abs_mul, abs_neg, abs_of_nonneg hlog]
      field_simp

/-- The exact finite-sum Lipschitz estimate. -/
theorem dyadicDirichletPolynomial_lipschitz_bound
    {a : ℕ → ℂ} {N : ℝ} (hN : 0 ≤ N) (t u : ℝ) :
    ‖dyadicDirichletPolynomial a N (onePlusIT t) -
        dyadicDirichletPolynomial a N (onePlusIT u)‖ ≤
      dyadicDirichletLipschitzConstant a N * |t - u| := by
  simp only [dyadicDirichletPolynomial, dirichletPolynomial]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ n ∈ dyadicInterval N,
        (a n * (n : ℂ) ^ (-onePlusIT t) -
          a n * (n : ℂ) ^ (-onePlusIT u))‖
      ≤ ∑ n ∈ dyadicInterval N,
          ‖a n * (n : ℂ) ^ (-onePlusIT t) -
            a n * (n : ℂ) ^ (-onePlusIT u)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ dyadicInterval N,
          (‖a n‖ * (Real.log (n : ℝ) / (n : ℝ))) * |t - u| := by
      gcongr with n hn
      have hnrange := (mem_dyadicInterval hN).mp hn
      have hnpos : 0 < n := by
        exact_mod_cast lt_of_le_of_lt hN hnrange.1
      rw [show a n * (n : ℂ) ^ (-onePlusIT t) -
          a n * (n : ℂ) ^ (-onePlusIT u) =
        a n * ((n : ℂ) ^ (-onePlusIT t) -
          (n : ℂ) ^ (-onePlusIT u)) by ring, norm_mul]
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left
        (norm_cpow_neg_onePlusIT_sub_le hnpos t u) (norm_nonneg (a n))
    _ = dyadicDirichletLipschitzConstant a N * |t - u| := by
      rw [dyadicDirichletLipschitzConstant, Finset.sum_mul]

theorem dyadicDirichletLipschitzConstant_nonneg
    {a : ℕ → ℂ} {N : ℝ} (hN : 0 ≤ N) :
    0 ≤ dyadicDirichletLipschitzConstant a N := by
  apply Finset.sum_nonneg
  intro n hn
  have hnrange := (mem_dyadicInterval hN).mp hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast lt_of_le_of_lt hN hnrange.1
  exact mul_nonneg (norm_nonneg _)
    (div_nonneg (Real.log_natCast_nonneg n) hnpos.le)

/-- A coarse version displaying separately the number of terms, a uniform
coefficient bound, the logarithm of the dyadic length, and `1/N`. -/
theorem dyadicDirichletLipschitzConstant_le_card_mul_uniformCoefficient
    {a : ℕ → ℂ} {N Q : ℝ}
    (hN : 1 ≤ N) (hQ : 0 ≤ Q)
    (ha : ∀ n ∈ dyadicInterval N, ‖a n‖ ≤ Q) :
    dyadicDirichletLipschitzConstant a N ≤
      ((dyadicInterval N).card : ℝ) *
        (Q * (Real.log (2 * N) / N)) := by
  rw [dyadicDirichletLipschitzConstant]
  calc
    (∑ n ∈ dyadicInterval N,
        ‖a n‖ * (Real.log (n : ℝ) / (n : ℝ))) ≤
      ∑ _n ∈ dyadicInterval N,
        Q * (Real.log (2 * N) / N) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnrange := (mem_dyadicInterval (by linarith : 0 ≤ N)).mp hn
      have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast lt_of_le_of_lt (by linarith : 0 ≤ N) hnrange.1
      have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
      have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
      have hlog2N : 0 ≤ Real.log (2 * N) :=
        Real.log_nonneg (by nlinarith)
      have hlogle : Real.log (n : ℝ) ≤ Real.log (2 * N) :=
        Real.log_le_log hnpos hnrange.2
      have hfrac : Real.log (n : ℝ) / (n : ℝ) ≤
          Real.log (2 * N) / N :=
        div_le_div₀ hlog2N hlogle hNpos hnrange.1.le
      calc
        ‖a n‖ * (Real.log (n : ℝ) / (n : ℝ)) ≤
            Q * (Real.log (n : ℝ) / (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (ha n hn)
            (div_nonneg hlogn hnpos.le)
        _ ≤ Q * (Real.log (2 * N) / N) :=
          mul_le_mul_of_nonneg_left hfrac hQ
    _ = ((dyadicInterval N).card : ℝ) *
        (Q * (Real.log (2 * N) / N)) := by simp

/-- The nonnegative real Lipschitz constant packaged as an `NNReal`. -/
def dyadicDirichletLipschitzNNConstant
    (a : ℕ → ℂ) (N : ℝ) (hN : 0 ≤ N) : NNReal :=
  ⟨dyadicDirichletLipschitzConstant a N,
    dyadicDirichletLipschitzConstant_nonneg hN⟩

theorem lipschitzWith_dyadicDirichletPolynomial_onePlusIT
    {a : ℕ → ℂ} {N : ℝ} (hN : 0 ≤ N) :
    LipschitzWith (dyadicDirichletLipschitzNNConstant a N hN)
      (fun t : ℝ ↦ dyadicDirichletPolynomial a N (onePlusIT t)) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  change dist _ _ ≤ dyadicDirichletLipschitzConstant a N * dist t u
  simpa [Complex.dist_eq, Real.dist_eq] using
    dyadicDirichletPolynomial_lipschitz_bound (a := a) hN t u

/-- Derivative norm bound implied by the global Lipschitz estimate. -/
theorem norm_deriv_dyadicDirichletPolynomial_onePlusIT_le
    {a : ℕ → ℂ} {N : ℝ} (hN : 0 ≤ N) (t : ℝ) :
    ‖deriv (fun u : ℝ ↦
        dyadicDirichletPolynomial a N (onePlusIT u)) t‖ ≤
      dyadicDirichletLipschitzConstant a N := by
  have h := norm_deriv_le_of_lipschitz
    (lipschitzWith_dyadicDirichletPolynomial_onePlusIT (a := a) hN)
    (x₀ := t)
  change ‖deriv (fun u : ℝ ↦
    dyadicDirichletPolynomial a N (onePlusIT u)) t‖ ≤
      dyadicDirichletLipschitzConstant a N at h
  exact h

/-- A value above `Vtarget` remains above `Vsample` throughout a radius
`δ` whenever the displayed Lipschitz loss fits in the threshold gap. -/
theorem dyadicDirichletPolynomial_threshold_persistence
    {a : ℕ → ℂ} {N Vtarget Vsample δ t u : ℝ}
    (hN : 0 ≤ N)
    (hgap : dyadicDirichletLipschitzConstant a N * δ ≤
      Vtarget - Vsample)
    (ht : Vtarget <
      ‖dyadicDirichletPolynomial a N (onePlusIT t)‖)
    (htu : |t - u| ≤ δ) :
    Vsample < ‖dyadicDirichletPolynomial a N (onePlusIT u)‖ := by
  have hlip :=
    dyadicDirichletPolynomial_lipschitz_bound (a := a) hN t u
  have hslope0 :=
    dyadicDirichletLipschitzConstant_nonneg (a := a) hN
  have hdiff :
      ‖dyadicDirichletPolynomial a N (onePlusIT t) -
        dyadicDirichletPolynomial a N (onePlusIT u)‖ ≤
        Vtarget - Vsample := by
    exact hlip.trans <|
      (mul_le_mul_of_nonneg_left htu hslope0).trans hgap
  have htriangle :
      ‖dyadicDirichletPolynomial a N (onePlusIT t)‖ ≤
        ‖dyadicDirichletPolynomial a N (onePlusIT t) -
          dyadicDirichletPolynomial a N (onePlusIT u)‖ +
        ‖dyadicDirichletPolynomial a N (onePlusIT u)‖ := by
    calc
      _ = ‖(dyadicDirichletPolynomial a N (onePlusIT t) -
          dyadicDirichletPolynomial a N (onePlusIT u)) +
          dyadicDirichletPolynomial a N (onePlusIT u)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  linarith

/-! ## Maximal one-spaced selections -/

/-- A metric set whose distinct points are more than one apart is
one-spaced in the paper's weak (`≥ 1`) convention. -/
theorem isOneSpaced_of_metric_isSeparated_one {R : Set ℝ}
    (hR : Metric.IsSeparated (1 : ENNReal) R) : IsOneSpaced R := by
  intro x hx y hy hxy
  have hdist : 1 < dist x y := by
    have h := hR hx hy hxy
    simpa [edist_dist] using h
  simpa [Real.dist_eq] using hdist.le

/-- A bounded set of ordinates admits a finite, one-spaced subset which is a
unit cover.  The chosen set is Mathlib's maximal separated set; maximality is
used only through its covering theorem. -/
theorem exists_finite_oneSpaced_unitCover {E : Set ℝ} {T : ℝ}
    (hE : E ⊆ Set.Icc 0 T) :
    ∃ R : Finset ℝ,
      (↑R : Set ℝ) ⊆ E ∧
      IsOneSpaced (↑R : Set ℝ) ∧
      Metric.IsCover (1 : NNReal) E (↑R : Set ℝ) := by
  have htot : TotallyBounded E :=
    (isCompact_Icc.totallyBounded).subset hE
  obtain ⟨N, _hNE, hNfinite, hNcover⟩ :=
    Metric.exists_finite_isCover_of_totallyBounded
      (s := E) (ε := (1 / 2 : NNReal)) (by norm_num) htot
  have hext_ne_top :
      Metric.externalCoveringNumber (1 / 2 : NNReal) E ≠ ⊤ := by
    apply ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hNfinite)
    exact hNcover.externalCoveringNumber_le_encard
  have hpack_le :
      Metric.packingNumber (1 : NNReal) E ≤
        Metric.externalCoveringNumber (1 / 2 : NNReal) E := by
    simpa using
      Metric.packingNumber_two_mul_le_externalCoveringNumber
        (1 / 2 : NNReal) E
  have hpack_ne_top : Metric.packingNumber (1 : NNReal) E ≠ ⊤ :=
    ne_top_of_le_ne_top hext_ne_top hpack_le
  let M : Set ℝ := Metric.maximalSeparatedSet (1 : NNReal) E
  have hMfinite : M.Finite := by
    rw [← Set.encard_ne_top_iff]
    rw [Metric.encard_maximalSeparatedSet hpack_ne_top]
    exact hpack_ne_top
  let R : Finset ℝ := hMfinite.toFinset
  refine ⟨R, ?_, ?_, ?_⟩
  · simpa [R, M] using
      (Metric.maximalSeparatedSet_subset :
        Metric.maximalSeparatedSet (1 : NNReal) E ⊆ E)
  · apply isOneSpaced_of_metric_isSeparated_one
    simpa [R, M] using
      (Metric.isSeparated_maximalSeparatedSet (A := E) (ε := (1 : NNReal)))
  · simpa [R, M] using Metric.isCover_maximalSeparatedSet hpack_ne_top

/-- The explicit regularity bound closes the threshold-changing sampling
step for a finite dyadic Dirichlet polynomial.  A maximal unit net of
`[0,T]` supplies the sample point; the Lipschitz loss lowers `Vtarget` to
`Vsample`. -/
theorem hasUnitLargeValueSampling_dyadicDirichletPolynomial
    {a : ℕ → ℂ} {N T Vtarget Vsample : ℝ}
    (hN : 0 ≤ N)
    (hgap : dyadicDirichletLipschitzConstant a N ≤
      Vtarget - Vsample) :
    HasUnitLargeValueSampling
      (dyadicDirichletPolynomial a N) T Vtarget Vsample := by
  obtain ⟨R, hRsub, _hRspace, hRcover⟩ :=
    exists_finite_oneSpaced_unitCover
      (E := Set.Icc (0 : ℝ) T) (T := T) Subset.rfl
  intro t ht
  obtain ⟨u, huR, htuEdist⟩ := hRcover ht.1
  have htu : |t - u| ≤ 1 := by
    simpa [edist_dist, Real.dist_eq] using htuEdist
  have husample :
      Vsample < ‖dyadicDirichletPolynomial a N (onePlusIT u)‖ :=
    dyadicDirichletPolynomial_threshold_persistence hN
      (by simpa using hgap) ht.2 htu
  exact ⟨u, ⟨hRsub huR, husample⟩, htu⟩

/-! ## Measure of finite covers -/

/-- A finite unit-ball cover on the real line has volume at most twice the
number of its centres. -/
theorem volume_le_two_mul_card_of_unitCover {E : Set ℝ} (R : Finset ℝ)
    (hcover : Metric.IsCover (1 : NNReal) E (↑R : Set ℝ)) :
    volume E ≤ 2 * (R.card : ENNReal) := by
  calc
    volume E ≤ volume (⋃ r ∈ R, Metric.closedBall r (1 : ℝ)) :=
      measure_mono hcover.subset_iUnion_closedBall
    _ ≤ ∑ r ∈ R, volume (Metric.closedBall r (1 : ℝ)) :=
      measure_biUnion_finset_le R _
    _ = 2 * (R.card : ENNReal) := by simp [mul_comm]

/-- If `E` is sampled within distance one by a set which is itself covered
by unit balls centred at `R`, then radius-two balls around `R` cover `E`. -/
theorem radiusTwoCover_of_unitSampling_of_unitCover
    {E S : Set ℝ} {R : Finset ℝ}
    (hsample : HasUnitSampling E S)
    (hcover : Metric.IsCover (1 : NNReal) S (↑R : Set ℝ)) :
    E ⊆ ⋃ r ∈ R, Metric.closedBall r (2 : ℝ) := by
  intro t ht
  obtain ⟨u, huS, htu⟩ := hsample t ht
  obtain ⟨r, hrR, hur⟩ := hcover huS
  have htu' : dist t u ≤ 1 := by simpa [Real.dist_eq] using htu
  have hur' : dist u r ≤ 1 := by
    simpa [edist_dist] using hur
  have htr : dist t r ≤ 2 := by
    calc
      dist t r ≤ dist t u + dist u r := dist_triangle _ _ _
      _ ≤ 1 + 1 := add_le_add htu' hur'
      _ = 2 := by norm_num
  exact Set.mem_iUnion.2
    ⟨r, Set.mem_iUnion.2 ⟨hrR, Metric.mem_closedBall.mpr htr⟩⟩

/-- The corresponding radius-two cover has volume at most four times the
number of centres. -/
theorem volume_le_four_mul_card_of_unitSampling_of_unitCover
    {E S : Set ℝ} (R : Finset ℝ)
    (hsample : HasUnitSampling E S)
    (hcover : Metric.IsCover (1 : NNReal) S (↑R : Set ℝ)) :
    volume E ≤ 4 * (R.card : ENNReal) := by
  calc
    volume E ≤ volume (⋃ r ∈ R, Metric.closedBall r (2 : ℝ)) :=
      measure_mono (radiusTwoCover_of_unitSampling_of_unitCover hsample hcover)
    _ ≤ ∑ r ∈ R, volume (Metric.closedBall r (2 : ℝ)) :=
      measure_biUnion_finset_le R _
    _ = 4 * (R.card : ENNReal) := by
      simp [mul_comm]
      ring

/-! ## Cardinality bounds imply volume bounds -/

/-- Direct maximal-selection bridge.  No continuity or local persistence is
needed when the discrete estimate is available at exactly the threshold
defining `E`: the maximal one-spaced subset is selected inside `E` itself. -/
theorem volume_le_of_uniform_oneSpaced_card_bound
    {E : Set ℝ} {T C : ℝ}
    (hE : E ⊆ Set.Icc 0 T)
    (hcard : ∀ R : Finset ℝ,
      (↑R : Set ℝ) ⊆ E → IsOneSpaced (↑R : Set ℝ) →
        (R.card : ℝ) ≤ C) :
    volume E ≤ ENNReal.ofReal (2 * C) := by
  obtain ⟨R, hRE, hRspace, hRcover⟩ :=
    exists_finite_oneSpaced_unitCover hE
  have hRC : (R.card : ℝ) ≤ C := hcard R hRE hRspace
  calc
    volume E ≤ 2 * (R.card : ENNReal) :=
      volume_le_two_mul_card_of_unitCover R hRcover
    _ = ENNReal.ofReal (2 * (R.card : ℝ)) := by simp
    _ ≤ ENNReal.ofReal (2 * C) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith

/-- Same-threshold specialization in the exact shape used after a discrete
large-values theorem: its interval and size hypotheses are merely unpacked
from membership in `largeValueSet`. -/
theorem volume_largeValueSet_le_of_uniform_card_bound
    {A : ℂ → ℂ} {T V C : ℝ}
    (hcard : ∀ R : Finset ℝ,
      IsOneSpaced (↑R : Set ℝ) →
      (∀ t ∈ R, t ∈ Set.Icc (0 : ℝ) T) →
      (∀ t ∈ R, V < ‖A (onePlusIT t)‖) →
      (R.card : ℝ) ≤ C) :
    volume (largeValueSet A T V) ≤ ENNReal.ofReal (2 * C) := by
  apply volume_le_of_uniform_oneSpaced_card_bound
  · intro t ht
    exact ht.1
  · intro R hRsubset hRspace
    exact hcard R hRspace
      (fun t ht ↦ (hRsubset ht).1)
      (fun t ht ↦ (hRsubset ht).2)

/-- Sampled-threshold bridge.  The local sampling property is explicit: it
is the only analytic input beyond a uniform discrete cardinality bound. -/
theorem volume_le_of_sampling_and_uniform_oneSpaced_card_bound
    {E S : Set ℝ} {T C : ℝ}
    (hS : S ⊆ Set.Icc 0 T)
    (hsample : HasUnitSampling E S)
    (hcard : ∀ R : Finset ℝ,
      (↑R : Set ℝ) ⊆ S → IsOneSpaced (↑R : Set ℝ) →
        (R.card : ℝ) ≤ C) :
    volume E ≤ ENNReal.ofReal (4 * C) := by
  obtain ⟨R, hRS, hRspace, hRcover⟩ :=
    exists_finite_oneSpaced_unitCover hS
  have hRC : (R.card : ℝ) ≤ C := hcard R hRS hRspace
  calc
    volume E ≤ 4 * (R.card : ENNReal) :=
      volume_le_four_mul_card_of_unitSampling_of_unitCover R hsample hRcover
    _ = ENNReal.ofReal (4 * (R.card : ℝ)) := by simp
    _ ≤ ENNReal.ofReal (4 * C) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith

/-- Specialization of the sampled bridge to the paper's large-value sets.
If `Vtarget = Vsample`, the sampling hypothesis is discharged by
`hasUnitLargeValueSampling_same`. -/
theorem volume_largeValueSet_le_of_sampling_and_card_bound
    {A : ℂ → ℂ} {T Vtarget Vsample C : ℝ}
    (hsample : HasUnitLargeValueSampling A T Vtarget Vsample)
    (hcard : ∀ R : Finset ℝ,
      (∀ t ∈ R, t ∈ largeValueSet A T Vsample) →
      IsOneSpaced (↑R : Set ℝ) → (R.card : ℝ) ≤ C) :
    volume (largeValueSet A T Vtarget) ≤ ENNReal.ofReal (4 * C) := by
  refine volume_le_of_sampling_and_uniform_oneSpaced_card_bound
    (E := largeValueSet A T Vtarget) (S := largeValueSet A T Vsample)
    (T := T) (hS := ?_) (hsample := hsample) (hcard := ?_)
  · intro t ht
    exact ht.1
  · intro R hRS hRspace
    exact hcard R (fun t ht ↦ hRS ht) hRspace

/-- Fully internal threshold-changing discrete-to-measure passage for a
dyadic Dirichlet polynomial.  The threshold loss is the explicit coefficient
sum `dyadicDirichletLipschitzConstant`; the only remaining input is the
discrete cardinality estimate at the sampled threshold. -/
theorem volume_dyadicDirichletLargeValueSet_le_of_card_bound
    {a : ℕ → ℂ} {N T Vtarget Vsample C : ℝ}
    (hN : 0 ≤ N)
    (hgap : dyadicDirichletLipschitzConstant a N ≤
      Vtarget - Vsample)
    (hcard : ∀ R : Finset ℝ,
      (∀ t ∈ R,
        t ∈ largeValueSet (dyadicDirichletPolynomial a N) T Vsample) →
      IsOneSpaced (↑R : Set ℝ) → (R.card : ℝ) ≤ C) :
    volume
        (largeValueSet (dyadicDirichletPolynomial a N) T Vtarget) ≤
      ENNReal.ofReal (4 * C) := by
  exact volume_largeValueSet_le_of_sampling_and_card_bound
    (hasUnitLargeValueSampling_dyadicDirichletPolynomial hN hgap) hcard

def discreteToMeasureModule : ProofModule :=
  { name := "Hybrid.DiscreteToMeasure"
    paperLocation := "Final sentence of Lemma 4.3"
    purpose :=
      "Apply a finite maximal one-spaced cover and prove the threshold-changing local sampling bound for finite dyadic Dirichlet polynomials."
    dependsOn :=
      ["Definitions", "Mathlib maximal-separated-set covering and circle-map Lipschitz bound"]
    status := .proved }

end

end Hybrid
end ExactSemiprimes
