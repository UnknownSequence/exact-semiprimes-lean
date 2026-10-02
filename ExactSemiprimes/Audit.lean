import ExactSemiprimes.MainTheorem

/-!
# Trust audit

Run with `lake env lean ExactSemiprimes/Audit.lean`.

1. `#print axioms` for the two main theorems: only Lean's standard
   `propext`, `Classical.choice`, `Quot.sound`.
2. `#used_inputs`: the fields of `ExternalInputs` and
   `ParameterExtensionInputs` that the proof term of a declaration actually
   uses (transitively).  Fields not listed are carried as hypotheses but
   never used.
-/

open Lean Elab Command

namespace ExactSemiprimes.Audit

/-- All `ExactSemiprimes` constants reachable from `root`. -/
partial def reachableConstants (env : Environment) (root : Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := [root]
  while !stack.isEmpty do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if visited.contains n then continue
      visited := visited.insert n
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet do
          if !visited.contains d then
            if d.getRoot == `ExactSemiprimes then
              stack := d :: stack
            else
              visited := visited.insert d
  return visited

elab "#used_inputs " id:ident : command => do
  let env ← getEnv
  let s := reachableConstants env id.getId
  let mut out : Array String := #[]
  for n in s do
    let p := n.getPrefix
    if (p == `ExactSemiprimes.ExternalInputs ||
        p == `ExactSemiprimes.ParameterExtensionInputs) && n.getString! != "mk" then
      out := out.push n.toString
  logInfo m!"{(out.qsort (· < ·)).toList}"

end ExactSemiprimes.Audit

#print axioms ExactSemiprimes.mainTheorem_exponent_2092
#print axioms ExactSemiprimes.mainTheorem_parameter

#used_inputs ExactSemiprimes.mainTheorem_exponent_2092
