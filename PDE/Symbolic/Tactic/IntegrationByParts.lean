/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import CAS.IntegrationTactic
public import PDE.Spaces.Sobolev.Weighted.IntegrationByParts -- shake: keep: `cas [ibp]` quotes `weightedSquareEnergy_eq_neg_two_cross` in tactic syntax; callers resolve it

/-!
# Checked integration by parts

`cas [ibp]` proves the weighted-square identity
`∫ x in (a, b), w x * u x ^ 2 = -2 * ∫ x in (a, b), W x * u x * u' x`
(`SobolevSpace.Weighted.weightedSquareEnergy_eq_neg_two_cross`, with `W' = w`). The two
derivative premises `HasDerivAt W (w x) x` and `HasDerivAt u (u' x) x` on `(a, b)` are
proved by `cas`; every other premise (`a < b`, both integrability conditions,
and the vanishing of `W * u ^ 2` at both endpoints) must be a hypothesis in the context.
-/

public meta section

namespace CAS.Tactic.IntegrationByParts

open Lean Elab Tactic

/-- Close a weighted-square integration-by-parts goal. -/
def close (requirementsSyntax? : Option (TSyntax `term)) : TacticM Unit := do
  let tactic ←
    match requirementsSyntax? with
    | none =>
        `(tactic|
          apply SobolevSpace.Weighted.weightedSquareEnergy_eq_neg_two_cross <;>
            first
            | assumption
            | (intro x hx; cas))
    | some requirements =>
        `(tactic|
          apply SobolevSpace.Weighted.weightedSquareEnergy_eq_neg_two_cross <;>
            first
            | assumption
            | (intro x hx
               first
               | cas using ($requirements x hx)
               | cas using ($requirements x)
               | cas using $requirements))
  try
    discard <| ProofCarrier.runClosingMainGoal "cas [ibp]" do
      focus <| evalTactic tactic
  catch error =>
    throwError
      "cas [ibp] could not prove this weighted-square integration-by-parts \
       identity. It checks the primitive and field derivative symbolically; \
       supply interval nonemptiness, integrability, and both vanishing \
       endpoint limits as hypotheses.\n\
       Detail:{indentD error.toMessageData}"

end CAS.Tactic.IntegrationByParts
