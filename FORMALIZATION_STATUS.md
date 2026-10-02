# Lean formalization status

Checked with Lean 4.34.0 and Mathlib v4.34.0
(commit `5ed2965256430c3649e86755f9576b54eca72435`).

## Headline

The paper's two main results are proved end to end:

| Paper | Lean theorem (`ExactSemiprimes/MainTheorem.lean`) | Statement type |
|---|---|---|
| Theorem 1.2 (exponent `2.092`, with `c₀ (log x)^1.092` prime products in the window `((log x)^1.091, (log x)^1.092]`) | `ExactSemiprimes.mainTheorem_exponent_2092` | `ExternalInputs → ParameterExtensionInputs → Results.CleanTheoremStatement` |
| Theorem 1.3 (every `c > 3688/1763`, and the prime-window count for `c ≤ 2.1`) | `ExactSemiprimes.mainTheorem_parameter` | `ExternalInputs → ParameterExtensionInputs → Results.ParameterTheoremStatement` |

The hypotheses are the 21 cited published theorems of `ExternalInputs`
(13 of which are actually used) and the 5 labelled parameter extensions of
`ParameterExtensionInputs`; see `ASSUMPTIONS.md`.

## Build and trust audit

- Every module compiles (102 modules, including the root
  `ExactSemiprimes.lean`, `ExactSemiprimes/MainTheorem.lean` and
  `ExactSemiprimes/Audit.lean`), without warnings.
- The project contains no `sorry` or `admit` and declares no Lean `axiom`.
- No global inhabitant of `ExternalInputs` or `ParameterExtensionInputs` is
  postulated.
- `lake env lean ExactSemiprimes/Audit.lean` prints

  ```text
  'ExactSemiprimes.mainTheorem_exponent_2092' depends on axioms: [propext, Classical.choice, Quot.sound]
  'ExactSemiprimes.mainTheorem_parameter' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

  together with the list of hypothesis fields actually used by the proof
  term (13 fields of `ExternalInputs`, all 5 of `ParameterExtensionInputs`).

## The improvement in one paragraph

A Type II convolution `M₁M₂` has `M₁ = X^θ` with `θ ≤ 2/11` and
`M₂ ≈ X^(1-θ)`.  On a medium large-value bin `|M_j| ≈ M_j^(-σ_j)`:

- if `σ₁ ≤ σ₂` and `σ₁ < 1/4 - O(ε)`, power `M₁` five or six times into
  `[X^(5/6), X)` and use the Guth--Maynard long-polynomial bound;
- if `σ₂ < σ₁` and `σ₂` is below the Guth--Maynard threshold
  `(3-8θ)/(10(1-2θ))` (or `1/4` for `θ ≤ 1/6`) for polynomials of length
  `X^(1-θ)`, use the density bound for `M₂` directly;
- otherwise the two Heath-Brown branches close as soon as
  `a > 1925/1763`, by the identity
  `(5-8σ₁)θ + 2σ₂(1-θ) = 4θ(1-2σ₁) + θ(1-2σ₂) + 2σ₂`.

The extremal configuration is `θ = 2/11`, `σ₂ = 17/70`,
`σ₁ = 517/1925`, `a = 1925/1763`, where both branches are saturated.  With
one threshold `17/70` for both factors the same argument gives only
`a > 35/32`.

## Route of the proof

| Paper | Lean |
|---|---|
| Lemma 4.3 (Guth--Maynard density estimate, length-dependent thresholds) | `Hybrid/`, in particular `Hybrid/RefinedDensity.lean` |
| Proposition 5.1 (Type II, threshold `17/70`) | `TypeII/`, ending in `TypeII/FullTypeIIEstimate.lean` |
| Section 6.1 (sparse Heath-Brown branches) | `Sparse/`, `Completion/TypeIIAnalyticPartition.lean` |
| Section 6.1, uniformity over a window of `a` (Hildebrand--Tenenbaum by subdivision) | `Final/SparseUniform.lean` |
| Sections 6.2--6.3 (density cases (a), (b) and the sparse regions A, B1, B2) | `Final/TypeIIDensityBins.lean` |
| Type II components on `𝒰`, uniformly over the blocks | `Final/TypeIIComponent.lean` |
| Type I and Type I/II components | labelled extensions E4, E5 (`Extensions.lean`) |
| Complement of `𝒰` | `Final/ComplementU.lean` (MT23 Lemma 3.3, (2.4), extension E3) |
| Heights `T ≥ X`, coefficient bound `5324` | `Final/PerronTail.lean` |
| Proposition 7.1: decomposition on `𝒰` and the Dirichlet-polynomial target | `Final/DirichletTarget.lean` |
| Proposition 7.1: block variance `≪ (log X)^(-2-ε/10)` | `Final/BlockVariance.lean` (extension E1) |
| Section 7.2: integrability, Chebyshev, union bound, disjoint blocks, prime-pair injection | `Final/Counting.lean` |
| Section 7.2: long averages (extension E2), exceptional set on `[X,2X]`, dyadic majorant | `Final/Assembly.lean` |
| Theorem 1.3 from the dyadic statement | `Results/ParameterTheorem.lean` (with `Completion/DyadicGlobalization.lean`, `Completion/IntervalMonotonicity.lean`) |
| Section 7.3 and Theorem 1.2 | `Results/CleanTheorem.lean` (the rational checks are repeated in `Results/ExplicitExponentArithmetic.lean`) |

Seventy-eight of the project's modules lie on the dependency path of the main
theorem (computed by walking the proof term).

## Modules off the critical path

The project also contains alternative routes that the final proof does not
need.  They compile and contain no `sorry`.

- `Completion/TypeIClosure.lean`, `Completion/TypeIOverIIClosure.lean`,
  `Completion/TypeIComponentClosure.lean`, the `TypeI*FiniteSlice*`,
  `TypeIFirstFactorMoment`, `TypeIPrimePowerEnergy`,
  `TypeIOverIICompositeMeanValue`, and `FiniteSliceInsertedCauchy` modules:
  partial derivations of the Type I and Type I/II bounds from the
  Deshouillers--Iwaniec and Watt inputs (the final proof uses E4, E5);
- `Completion/HarmanScaleArithmetic.lean`, `HarmanNumericPaperScale.lean`,
  `HarmanDyadicEventual.lean`: towards MT23 (5.6) from Harman's Lemma 1.5
  (the final proof uses the cited (5.6));
- `Completion/PerronKernelBounds.lean`, `PerronLowFrequency.lean`,
  `PerronCumulativeBounds.lean`, `ComponentAssembly.lean`,
  `ChebyshevPassage.lean`: an earlier interface to the Perron reduction and
  the variance-to-count passage (the final proof uses E1 and `Final/`);
- `Sparse/EndpointAlgebra.lean`, `Sparse/EndpointSaturation.lean`,
  `Sparse/ResidualRange.lean`: the arithmetic of the single-threshold
  endpoint `a > 35/32`, kept for comparison;
- `Results/ExplicitExponentArithmetic.lean`: stand-alone rational checks
  (the same inequalities are proved inline on the critical path);
- `Results/PreviousStateOfArt.lean`: the MT23 exponent `2.1`, recorded for
  comparison only.

Each module has a `ProofModule` record.  Eight `Completion/` modules whose
originally announced end statement was replaced by another route
(`PerronTarget`, `GeneralPerronReduction`, `PerronKernelBounds`,
`ParameterizedReduction`, `ComponentAssembly`, `ComplementOfU`,
`TypeIOverIIClosure`, `TypeIIClosure`) have the status `.superseded`, and
their `purpose` names the module of the final proof that replaces them; some
of them still contribute lemmas to the final proof.  All other records are
`.proved`, except the two hypothesis bundles (`.externalAssumption`) and
`PreviousStateOfArt` (`.comparisonOnly`).  The authoritative check is
`Audit.lean`, not the status records.

## Building

```text
lake exe cache get
lake build                                 # builds the root and everything it imports
lake env lean ExactSemiprimes/Audit.lean   # trust audit
```

`ExactSemiprimes/Final/TypeIIComponent.lean` takes several minutes and raises
`maxHeartbeats` locally for one lemma.
