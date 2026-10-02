import ExactSemiprimes.Results.PreviousStateOfArt
import ExactSemiprimes.Results.CleanTheorem
import ExactSemiprimes.Sparse.PropagationMoving
import ExactSemiprimes.Sparse.PropagationParameters
import ExactSemiprimes.TypeII.RealScaleNaturalization
import ExactSemiprimes.Completion.TypeIComponentClosure
import ExactSemiprimes.Completion.TypeIOverIIClosure
import ExactSemiprimes.Completion.ComponentIntegralAssembly
import ExactSemiprimes.Completion.PerronCumulativeBounds
import ExactSemiprimes.Completion.GeneralPerronReduction
import ExactSemiprimes.Extensions
import ExactSemiprimes.MainTheorem

/-!
# Exact semiprimes in almost all intervals of length `(log x)^2.092`

This is the root module of the formalization.  Every interval exponent
`c > 3688/1763 = 2.09188…` is admissible, improving the exponent `2.1` of
Matomäki--Teräväinen.  The end-to-end results are
`ExactSemiprimes.mainTheorem_exponent_2092` (paper Theorem 1.2) and
`ExactSemiprimes.mainTheorem_parameter` (paper Theorem 1.3) in
`ExactSemiprimes/MainTheorem.lean`.  Their only hypotheses are the cited
inputs `ExternalInputs` (`Assumptions.lean`) and the labelled parameter
extensions `ParameterExtensionInputs` (`Extensions.lean`).  No internal
lemma is asserted as an axiom, and there is no `sorry`.
-/
