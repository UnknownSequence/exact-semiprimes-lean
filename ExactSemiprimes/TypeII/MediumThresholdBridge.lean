import ExactSemiprimes.TypeII.OpenClosedDyadicSlices

/-!
# Threshold shift for the powered medium branch

The endpoint-compatible slice selection loses a factor `1/ell`.  This file
absorbs that finite loss into an explicit shift of the large-value exponent
and supplies the natural-valued slice base required by the prepared hybrid
density statement.
-/

namespace ExactSemiprimes
namespace TypeII

open Filter

noncomputable section

/-- If a positive integral power is split into `ell` pieces, the factor
`1/ell` can be absorbed by increasing the large-value exponent by `delta`,
provided `P^delta ≥ ell`. -/
theorem poweredSlice_threshold_shift
    {M P V W tau delta : ℝ} {ell : ℕ}
    (hell : 1 ≤ ell) (hM : 0 < M)
    (hscale : M ^ ell ≤ P)
    (htau : 0 ≤ tau)
    (habsorb : (ell : ℝ) ≤ P ^ delta)
    (hlarge : M ^ (-tau) < V)
    (hslice : V ^ ell / (ell : ℝ) ≤ W) :
    P ^ (-(tau + delta)) < W := by
  have hellReal : 0 < (ell : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hell)
  have hMpow : 0 < M ^ ell := pow_pos hM ell
  have hP : 0 < P := hMpow.trans_le hscale
  have hPtau : P ^ (-tau) ≤ M ^ (-tau * (ell : ℝ)) := by
    calc
      P ^ (-tau) ≤ (M ^ ell) ^ (-tau) :=
        Real.rpow_le_rpow_of_nonpos hMpow hscale (by linarith)
      _ = M ^ (-tau * (ell : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
        congr 1
        ring
  have hPdelta : P ^ (-delta) ≤ 1 / (ell : ℝ) := by
    rw [Real.rpow_neg hP.le]
    simpa only [one_div] using one_div_le_one_div_of_le hellReal habsorb
  have hpowerLarge :
      M ^ (-tau * (ell : ℝ)) < V ^ ell := by
    calc
      M ^ (-tau * (ell : ℝ)) = (M ^ (-tau)) ^ ell := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
      _ < V ^ ell :=
        pow_lt_pow_left₀ hlarge (Real.rpow_nonneg hM.le _) (by omega)
  calc
    P ^ (-(tau + delta)) = P ^ (-tau) * P ^ (-delta) := by
      rw [show -(tau + delta) = -tau + -delta by ring,
        Real.rpow_add hP]
    _ ≤ M ^ (-tau * (ell : ℝ)) * P ^ (-delta) :=
      mul_le_mul_of_nonneg_right hPtau (Real.rpow_nonneg hP.le _)
    _ ≤ M ^ (-tau * (ell : ℝ)) * (1 / (ell : ℝ)) :=
      mul_le_mul_of_nonneg_left hPdelta (Real.rpow_nonneg hM.le _)
    _ < V ^ ell / (ell : ℝ) := by
      simpa [div_eq_mul_inv, one_div] using
        mul_lt_mul_of_pos_right hpowerLarge (inv_pos.mpr hellReal)
    _ ≤ W := hslice

/-- Pointwise endpoint-compatible selection with the exact exponent shift.
The only extra size hypothesis is that `(M^ell)^delta` absorbs the finite
`ell`-slice pigeonhole loss. -/
theorem exists_large_poweredOpenClosedDyadicPolynomial_shiftedThreshold
    (a : ℕ → ℂ) {S : Finset ℕ} {M tau delta : ℝ} {ell : ℕ}
    (hM : 0 < M) (hell : 1 ≤ ell)
    (hS : ∀ n ∈ S, InDyadicRange M n)
    (htau : 0 ≤ tau) (hdelta : 0 ≤ delta)
    (habsorb : (ell : ℝ) ≤ (M ^ ell) ^ delta)
    (s : ℂ)
    (hlarge : M ^ (-tau) < ‖dirichletPolynomial a S s‖) :
    ∃ j < ell,
      (((2 : ℝ) ^ j * M ^ ell) ^ (-(tau + delta))) <
        ‖dyadicDirichletPolynomial
          (powerConvolutionCoefficient a S ell)
          ((2 : ℝ) ^ j * M ^ ell) s‖ := by
  obtain ⟨j, hj, hslice⟩ :=
    exists_large_poweredOpenClosedDyadicPolynomial a hM hell hS s
  refine ⟨j, hj, ?_⟩
  have hMpow : 0 < M ^ ell := pow_pos hM ell
  have htwoPow : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hscale : M ^ ell ≤ (2 : ℝ) ^ j * M ^ ell := by
    calc
      M ^ ell = 1 * M ^ ell := by ring
      _ ≤ (2 : ℝ) ^ j * M ^ ell :=
        mul_le_mul_of_nonneg_right htwoPow hMpow.le
  have habsorb' :
      (ell : ℝ) ≤ (((2 : ℝ) ^ j * M ^ ell) : ℝ) ^ delta := by
    exact habsorb.trans
      (Real.rpow_le_rpow hMpow.le hscale hdelta)
  apply poweredSlice_threshold_shift hell hM hscale htau habsorb'
    hlarge
  simpa only [norm_pow] using hslice

/-- Real-scale specialization matching the interval data of the prepared
medium branch: the original polynomial and the convolution coefficients are
both cut out by the same open--closed dyadic interval.  The natural-valued
slice base used by that statement is supplied below. -/
theorem exists_large_poweredDyadicPolynomial_shiftedThreshold
    (a : ℕ → ℂ) {M tau delta : ℝ} {ell : ℕ}
    (hM : 0 < M) (hell : 1 ≤ ell)
    (htau : 0 ≤ tau) (hdelta : 0 ≤ delta)
    (habsorb : (ell : ℝ) ≤ (M ^ ell) ^ delta)
    (s : ℂ)
    (hlarge : M ^ (-tau) <
      ‖dyadicDirichletPolynomial a M s‖) :
    ∃ j < ell,
      (((2 : ℝ) ^ j * M ^ ell) ^ (-(tau + delta))) <
        ‖dyadicDirichletPolynomial
          (powerConvolutionCoefficient a (dyadicInterval M) ell)
          ((2 : ℝ) ^ j * M ^ ell) s‖ := by
  exact exists_large_poweredOpenClosedDyadicPolynomial_shiftedThreshold
    a hM hell
    (fun n hn ↦ (mem_dyadicInterval hM.le).mp hn)
    htau hdelta habsorb s hlarge

/-- The selected natural dyadic index always gives a real scale between
`M^ell` and `(2M)^ell`. -/
theorem openClosedSliceBase_bounds
    {M : ℝ} {ell j : ℕ} (hM : 0 ≤ M) (hj : j < ell) :
    M ^ ell ≤ (2 : ℝ) ^ j * M ^ ell ∧
      (2 : ℝ) ^ j * M ^ ell ≤ (2 * M) ^ ell := by
  have hMpow : 0 ≤ M ^ ell := pow_nonneg hM ell
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have htwo : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ ell :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt hj)
  constructor
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hone hMpow
  · rw [mul_pow]
    exact mul_le_mul_of_nonneg_right htwo hMpow

/-! ## Natural slice bases used by the prepared hybrid branch -/

/-- The natural base of the `j`th powered slice. -/
def naturalOpenClosedSliceBase (M ell j : ℕ) : ℕ :=
  2 ^ j * M ^ ell

/-- Casting the natural slice base gives exactly the real scale appearing in
the endpoint-compatible polynomial identity. -/
@[simp, norm_cast]
theorem cast_naturalOpenClosedSliceBase (M ell j : ℕ) :
    (naturalOpenClosedSliceBase M ell j : ℝ) =
      (2 : ℝ) ^ j * (M : ℝ) ^ ell := by
  simp [naturalOpenClosedSliceBase]

/-- A positive integral base gives a positive natural slice base. -/
theorem one_le_naturalOpenClosedSliceBase
    {M ell j : ℕ} (hM : 1 ≤ M) :
    1 ≤ naturalOpenClosedSliceBase M ell j := by
  exact one_le_mul (one_le_pow₀ (by omega : 1 ≤ (2 : ℕ)))
    (one_le_pow₀ hM)

/-- Natural-scale support bounds for the slice chosen by an index `j<ell`.
These are the integral counterparts of `openClosedSliceBase_bounds`. -/
theorem naturalOpenClosedSliceBase_bounds
    {M ell j : ℕ} (hj : j < ell) :
    M ^ ell ≤ naturalOpenClosedSliceBase M ell j ∧
      naturalOpenClosedSliceBase M ell j ≤ (2 * M) ^ ell := by
  have hone : (1 : ℕ) ≤ 2 ^ j := one_le_pow₀ (by omega)
  have htwo : 2 ^ j ≤ 2 ^ ell :=
    pow_le_pow_right' (by omega : (1 : ℕ) ≤ 2) (Nat.le_of_lt hj)
  constructor
  · simpa [naturalOpenClosedSliceBase] using
      (mul_le_mul_left hone (M ^ ell))
  · rw [naturalOpenClosedSliceBase, mul_pow]
    exact mul_le_mul_left htwo (M ^ ell)

/-- Full natural-scale version of the pointwise selector.  It returns a
natural `P`, its defining identity, the positivity and support bounds
required by the prepared branch, and the shifted large-value inequality at
the literal base `(P : ℝ)`. -/
theorem exists_large_poweredDyadicPolynomial_shiftedThreshold_naturalScale
    (a : ℕ → ℂ) {M ell : ℕ} {tau delta : ℝ}
    (hM : 1 ≤ M) (hell : 1 ≤ ell)
    (htau : 0 ≤ tau) (hdelta : 0 ≤ delta)
    (habsorb : (ell : ℝ) ≤ (((M : ℝ) ^ ell) ^ delta))
    (s : ℂ)
    (hlarge : (M : ℝ) ^ (-tau) <
      ‖dyadicDirichletPolynomial a (M : ℝ) s‖) :
    ∃ j < ell, ∃ P : ℕ,
      P = naturalOpenClosedSliceBase M ell j ∧
      1 ≤ P ∧
      M ^ ell ≤ P ∧
      P ≤ (2 * M) ^ ell ∧
      (P : ℝ) ^ (-(tau + delta)) <
        ‖dyadicDirichletPolynomial
          (powerConvolutionCoefficient a (dyadicInterval (M : ℝ)) ell)
          (P : ℝ) s‖ := by
  have hMReal : 0 < (M : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  obtain ⟨j, hj, hslice⟩ :=
    exists_large_poweredDyadicPolynomial_shiftedThreshold a hMReal hell
      htau hdelta habsorb s hlarge
  have hbounds := naturalOpenClosedSliceBase_bounds (M := M) hj
  refine ⟨j, hj, naturalOpenClosedSliceBase M ell j, rfl,
    one_le_naturalOpenClosedSliceBase hM, hbounds.1, hbounds.2, ?_⟩
  simpa only [cast_naturalOpenClosedSliceBase] using hslice

/-- It is enough to absorb the number of slices already at the unpowered
base.  This reduces the remaining asymptotic input to the transparent
inequality `ell ≤ M^delta`. -/
theorem ell_le_poweredScale_rpow_of_ell_le_base_rpow
    {M delta : ℝ} {ell : ℕ}
    (hell : 1 ≤ ell) (hM : 0 ≤ M)
    (habsorbBase : (ell : ℝ) ≤ M ^ delta) :
    (ell : ℝ) ≤ (M ^ ell) ^ delta := by
  have hellOne : (1 : ℝ) ≤ (ell : ℝ) := by
    exact_mod_cast hell
  have hbaseOne : (1 : ℝ) ≤ M ^ delta :=
    hellOne.trans habsorbBase
  calc
    (ell : ℝ) ≤ M ^ delta := habsorbBase
    _ ≤ (M ^ delta) ^ ell :=
      le_self_pow₀ hbaseOne
        (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hell))
    _ = M ^ (delta * (ell : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hM]
    _ = M ^ ((ell : ℝ) * delta) := by ring_nf
    _ = (M ^ ell) ^ delta := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hM]

/-- The exponent shift stays inside a hybrid-density window if the
unshifted exponent starts `delta` below its upper endpoint. -/
theorem shiftedThreshold_mem_window
    {lower upper tau delta : ℝ}
    (hdelta : 0 ≤ delta)
    (hlower : lower ≤ tau)
    (hupper : tau ≤ upper - delta) :
    lower ≤ tau + delta ∧ tau + delta ≤ upper := by
  constructor <;> linarith

/-! ## Uniform eventual absorption of the finite slice loss -/

/-- A fixed finite number of powered slices is eventually absorbed at every
base above `T^alpha`.  The cutoff in `T` is chosen before `M` and `ell`, so
the conclusion is uniform over all `ell ≤ K` and all such bases. -/
theorem eventually_ell_le_base_rpow_of_height_lower_bound
    (K : ℕ) {alpha delta : ℝ}
    (halpha : 0 < alpha) (hdelta : 0 < delta) :
    ∀ᶠ T : ℝ in atTop, ∀ (M : ℝ) (ell : ℕ),
      T ^ alpha ≤ M → ell ≤ K → (ell : ℝ) ≤ M ^ delta := by
  have hproduct : 0 < alpha * delta := mul_pos halpha hdelta
  have hK : ∀ᶠ T : ℝ in atTop, (K : ℝ) ≤ T ^ (alpha * delta) :=
    (tendsto_rpow_atTop hproduct).eventually_ge_atTop (K : ℝ)
  filter_upwards [hK, eventually_ge_atTop (1 : ℝ)] with T hKT hT
  intro M ell hTM hellK
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hellKReal : (ell : ℝ) ≤ (K : ℝ) := by
    exact_mod_cast hellK
  have hmonotone : (T ^ alpha) ^ delta ≤ M ^ delta :=
    Real.rpow_le_rpow (Real.rpow_nonneg hTpos.le alpha) hTM hdelta.le
  calc
    (ell : ℝ) ≤ (K : ℝ) := hellKReal
    _ ≤ T ^ (alpha * delta) := hKT
    _ = (T ^ alpha) ^ delta := by
      rw [Real.rpow_mul hTpos.le]
    _ ≤ M ^ delta := hmonotone

/-- Powered-scale form of the preceding theorem, matching the absorption
hypothesis of the medium threshold-shift selector. -/
theorem eventually_ell_le_poweredScale_rpow_of_height_lower_bound
    (K : ℕ) {alpha delta : ℝ}
    (halpha : 0 < alpha) (hdelta : 0 < delta) :
    ∀ᶠ T : ℝ in atTop, ∀ (M : ℝ) (ell : ℕ),
      T ^ alpha ≤ M → 1 ≤ ell → ell ≤ K →
        (ell : ℝ) ≤ (M ^ ell) ^ delta := by
  have hbase :=
    eventually_ell_le_base_rpow_of_height_lower_bound K halpha hdelta
  filter_upwards [hbase, eventually_ge_atTop (1 : ℝ)] with T hbaseT hT
  intro M ell hTM hell hellK
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hMnonneg : 0 ≤ M :=
    (Real.rpow_nonneg hTpos.le alpha).trans hTM
  exact ell_le_poweredScale_rpow_of_ell_le_base_rpow hell hMnonneg
    (hbaseT M ell hTM hellK)

/-- For fixed `eps > 0` and an order cap `K`, every base
`M ≥ T^(eps/5)` eventually absorbs the `ell`-slice loss through any fixed
positive shift `delta`, uniformly for `ell ≤ K`. -/
theorem eventually_ell_le_poweredScale_rpow_medium
    (K : ℕ) {eps delta : ℝ}
    (heps : 0 < eps) (hdelta : 0 < delta) :
    ∀ᶠ T : ℝ in atTop, ∀ (M : ℝ) (ell : ℕ),
      T ^ (eps / 5) ≤ M → 1 ≤ ell → ell ≤ K →
        (ell : ℝ) ≤ (M ^ ell) ^ delta := by
  exact eventually_ell_le_poweredScale_rpow_of_height_lower_bound K
    (by positivity : 0 < eps / 5) hdelta

/-- Exact bounded-order specialization used after the ceiling estimate
`ell ≤ ceil(5 / eps)` in the powered medium branch. -/
theorem eventually_ell_le_poweredScale_rpow_medium_ceil
    {eps delta : ℝ} (heps : 0 < eps) (hdelta : 0 < delta) :
    ∀ᶠ T : ℝ in atTop, ∀ (M : ℝ) (ell : ℕ),
      T ^ (eps / 5) ≤ M → 1 ≤ ell → ell ≤ ⌈5 / eps⌉₊ →
        (ell : ℝ) ≤ (M ^ ell) ^ delta := by
  exact eventually_ell_le_poweredScale_rpow_medium ⌈5 / eps⌉₊
    heps hdelta

def mediumThresholdBridgeModule : ProofModule :=
  { name := "TypeII.MediumThresholdBridge"
    paperLocation :=
      "Proof of Proposition 5.1, powered R₂ branch: slice threshold"
    purpose :=
      "Absorb the 1/ell slice-selection loss uniformly into an explicit exponent shift, convert the selected real scale into the natural dyadic base required by the hybrid-density theorem, and prove the needed eventual bound uniformly over all bounded powers."
    dependsOn := ["TypeII.OpenClosedDyadicSlices"]
    status := .proved }

end

end TypeII
end ExactSemiprimes
