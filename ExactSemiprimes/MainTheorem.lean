import ExactSemiprimes.Final.Assembly

/-!
# The main theorems

**Assumptions + Mathlib + symbol manipulation = new result.**

The two theorems below are the end-to-end formal versions of the paper's
Theorems 1.2 and 1.3.  Their only hypotheses are

* `inputs : ExternalInputs` — published theorems, each transcribed in its
  printed parameter range (`ExactSemiprimes/Assumptions.lean`), and
* `ext : ParameterExtensionInputs` — five *labelled* uniform-in-parameter
  versions of published Matomäki--Teräväinen/Matomäki--Radziwiłł lemmas
  whose printed proofs do not depend on the parameters being extended
  (`ExactSemiprimes/Extensions.lean`).

`ASSUMPTIONS.md` lists every field with its reference.  No `sorry`, no
project `axiom`, and no inhabitant of either bundle occurs anywhere;
`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`
(see `ExactSemiprimes/Audit.lean`).
-/

namespace ExactSemiprimes

/-- **Theorem 1.2 (exponent 2.092).**  There are `c₀ > 0` and `δ > 0` such
that for all `x ≤ X` outside an exceptional set of size `O(X/(log X)^δ)`
the interval `(x, x + (log x)^2.092]` contains at least `c₀ (log x)^1.092`
products `p q` of two primes with `(log x)^1.091 < p ≤ (log x)^1.092`; in
particular it contains an exact semiprime. -/
theorem mainTheorem_exponent_2092 (inputs : ExternalInputs)
    (ext : ParameterExtensionInputs) : Results.CleanTheoremStatement :=
  Final.cleanTheorem_of_inputs inputs ext

/-- **Theorem 1.3 (every exponent `c > 3688/1763`).**  For every
`c > 3688/1763 = 2.09188…`,
almost all intervals `(x, x + (log x)^c]` contain an exact semiprime, with a
power-of-log exceptional set; for `c ≤ 2.1` and every admissible window
`Δ`, they contain `≫ (log x)^(c-1)` prime products whose small factor lies
in `((log x)^(c-1-Δ), (log x)^(c-1-Δ/2)]`. -/
theorem mainTheorem_parameter (inputs : ExternalInputs)
    (ext : ParameterExtensionInputs) : Results.ParameterTheoremStatement :=
  Final.parameterTheorem_of_inputs inputs ext

end ExactSemiprimes
