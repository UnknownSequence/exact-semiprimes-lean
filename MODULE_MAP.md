# Paper-to-Lean module map

Paper: `paper/exact_semiprimes_exponent_2092.tex`.  Modules off the critical
path of the main theorem are marked *(alternative route)*; see
`FORMALIZATION_STATUS.md`.

| Paper location | Lean module |
|---|---|
| Lemma 4.3, coefficient normalization | `Hybrid/NormalizeCoefficients.lean` |
| Lemma 4.3, lower length range | `Hybrid/LowerRangeExponents.lean` |
| Lemma 4.3, upper length range | `Hybrid/UpperRangeExponents.lean` |
| Lemma 4.3, discrete-to-measure passage | `Hybrid/DiscreteToMeasure.lean` |
| Proposition 5.1, unit-cell/parity integral discretization | `Hybrid/IntegralDiscretization.lean` |
| Lemma 4.3 at the shortest length `T^(9/11)` (threshold `17/70`) | `Hybrid/HybridDensity.lean` |
| Lemma 4.3, length-dependent thresholds `s(η)` | `Hybrid/RefinedDensity.lean` |
| Proposition 5.1, length checks | `TypeII/PolynomialLengthRanges.lean` |
| Proposition 5.1, partition | `TypeII/LargeValuePartition.lean` |
| Proposition 5.1, extreme ranges | `TypeII/ExtremeRanges.lean` |
| Proposition 5.1, powered polynomial | `TypeII/PoweredPolynomial.lean` |
| Proposition 5.1, powered discrete mean value (IK04, Theorem 9.4) | `TypeII/PoweredMeanValue.lean` |
| Proposition 5.1, endpoint-compatible powered slices | `TypeII/OpenClosedDyadicSlices.lean` |
| Proposition 5.1, powered-slice threshold and natural scale | `TypeII/MediumThresholdBridge.lean` |
| Proposition 5.1, Halász--Montgomery specialization (IK04, Theorem 9.6) | `TypeII/HalaszMontgomery.lean` |
| Proposition 5.1, extreme-large ceiling power and exponent assembly | `TypeII/ExtremeLargeAssembly.lean` |
| Proposition 5.1, extreme-large uniform subpower absorption | `TypeII/ExtremeLargeAbsorption.lean` |
| Proposition 5.1, Luca--Tóth divisor moment and weighted extreme `R₁` contribution | `TypeII/WeightedExtremeRange.lean` |
| Proposition 5.1, tiny extreme `R₃` contribution | `TypeII/ExtremeSmallAssembly.lean` |
| Proposition 5.1, insertion of both extreme regimes into the actual partition | `TypeII/ExtremeRegimeAssembly.lean` |
| Proposition 5.1, medium-bin cardinality | `TypeII/MediumRangeCardinality.lean` |
| Proposition 5.1, finite uniformization of medium constants | `TypeII/MediumFiniteUniformization.lean` |
| Proposition 5.1, complete discrete weighted medium-bin assembly | `TypeII/MediumFullAssembly.lean` |
| Proposition 5.1, exact logarithmic-bin weights and occupied-bin bridge | `TypeII/MediumLogBinBridge.lean` |
| Proposition 5.1, shifted thresholds and outer saving reserves | `TypeII/OuterParameterReserve.lean` |
| Proposition 5.1, bounded powering order, natural powered supports, strong complementary-length interval, hybrid weakening, and eventual bin widths | `TypeII/OuterLengthGeometry.lean` |
| Proposition 5.1, insertion and summation of all occupied medium bins | `TypeII/MediumRegimeAssembly.lean` |
| Proposition 5.1, fully quantified target | `TypeII/TypeIIEstimate.lean` |
| Proposition 5.1, final regime combination, loss absorption, and integral estimate | `TypeII/FullTypeIIEstimate.lean` |
| Section 6.1, sparse polynomial, smooth support, deterministic support geometry, and the moving paper-scale deletion package | `Sparse/PrimePowerPolynomial.lean`, `Sparse/SmoothSupport.lean`, `Sparse/SupportGeometry.lean` |
| Section 6.1, lower bound for Q | `Sparse/QLowerBound.lean` |
| Section 6.1, first Heath--Brown branch, measure bridge, complex coefficients, and literal bins | `Sparse/MeasureBridge.lean`, `Sparse/FirstBranch.lean`, `Sparse/ComplexCoefficientSplit.lean`, `Sparse/MagnitudeBins.lean` |
| Section 6.1, residual range of the single-threshold argument *(alternative route)* | `Sparse/ResidualRange.lean` |
| Section 6.1, fifth-power second branch, five dyadic output blocks, and the key exponent `K(θ,σ₁,σ₂)` | `Sparse/SecondBranch.lean` |
| Endpoint `a > 35/32` of the single-threshold argument *(alternative route, for comparison)* | `Sparse/EndpointAlgebra.lean`, `Sparse/EndpointSaturation.lean` |
| Section 6.1, moving scale-ratio, structured Type-II convolution/product-scale bridges, and the two-branch dichotomy under the key inequality | `Sparse/Propagation.lean`, `Sparse/PropagationMoving.lean`, `Sparse/PropagationParameters.lean` |
| Section 6.1, sparse package on a literal medium log bin | `Completion/TypeIIAnalyticPartition.lean` |
| Proposition 7.1, Perron target | `Completion/PerronTarget.lean` |
| Proposition 7.1, cumulative-to-dyadic normalization, exact product support/coefficient budget, and general Parseval interface | `Completion/PerronCumulativeBounds.lean`, `Completion/GeneralPerronReduction.lean` |
| Proposition 7.1, complement of U | `Completion/RoughCoefficientTransfer.lean`, `Completion/ComplementOfU.lean` |
| Proposition 7.1, structured prime factors, exact coefficient/product fibre identity, and full-dyadic Harman specialization *(Harman modules: alternative route)* | `Completion/StructuredPrimeFactors.lean`, `Completion/HarmanScaleArithmetic.lean`, `Completion/HarmanNumericPaperScale.lean`, `Completion/HarmanDyadicEventual.lean` |
| Proposition 7.1, Type-I and Type-I/II convolution cases *(alternative route; the main theorem uses E4, E5)* | `Completion/TypeIClosure.lean`, `Completion/TypeIOverIIClosure.lean` |
| Proposition 7.1, Type-II short-segment projector and closure | `Completion/TypeIIClosure.lean` |
| Proposition 7.1, assembly *(alternative route)* | `Completion/ComponentAssembly.lean` |
| Proposition 7.1 | `Completion/ParameterizedReduction.lean` |
| Section 7.2, long minorant and blocks | `Completion/LongIntervalMinorant.lean`, `Completion/DyadicPrimeBlocks.lean` |
| Section 7.2, variance to almost all | `Completion/VarianceBlockSummation.lean`, `Completion/ChebyshevPassage.lean` |
| Section 7.2, exceptional integers | `Completion/RealToIntegerExceptions.lean` |
| Section 7.2, exact-semiprime bookkeeping | `Completion/PrimeWindowTransfer.lean`, `Completion/UniqueSmallPrimeFactor.lean`, `Completion/DyadicGlobalization.lean` |
| Proposition 7.1 and Section 7.1, labelled parameter extensions E1--E5 | `Extensions.lean` |
| Section 6.1, sparse support uniformly over a window of `a` | `Final/SparseUniform.lean` |
| Sections 6.2--6.3, density cases (a), (b), regions A, B1, B2, and the window margins for `a ≥ 1925/1763 + η` | `Final/TypeIIDensityBins.lean` |
| Proposition 7.1, Type II components on `𝒰` uniformly over the blocks | `Final/TypeIIComponent.lean` |
| Proposition 7.1, complement of `𝒰` for general `a, c` | `Final/ComplementU.lean` |
| Proposition 7.1, heights `T ≥ X` and the coefficient bound `5324` | `Final/PerronTail.lean` |
| Proposition 7.1, Dirichlet-polynomial target (`𝒰` part, middle range, tails) | `Final/DirichletTarget.lean` |
| Proposition 7.1, block variance | `Final/BlockVariance.lean` |
| Section 7.2, integrability, Chebyshev, union bound, disjoint blocks, prime-pair injection | `Final/Counting.lean` |
| Section 7.2, exceptional set on `[X,2X]` and the dyadic statement | `Final/Assembly.lean` |
| Theorem 1.3 | `Results/ParameterTheorem.lean` |
| Section 7.3 rational checks *(stand-alone; the same inequalities are proved inline)* | `Results/ExplicitExponentArithmetic.lean` |
| Theorem 1.2 | `Results/CleanTheorem.lean` |
| Previous state of the art | `Results/PreviousStateOfArt.lean` |
| Theorems 1.2 and 1.3, end to end from the hypothesis bundles | `MainTheorem.lean` |
| Trust audit (`#print axioms`, hypotheses actually used) | `Audit.lean` |
