/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Symbolic.Tactic.IntegrationByParts

/-!
# Theorem-facing integration-by-parts tactic

The tactic `cas [ibp]` proves the weighted-square identity
`∫ x in (a, b), w x * u x ^ 2 = -2 * ∫ x in (a, b), W x * u x * u' x` by applying
`SobolevSpace.Weighted.weightedSquareEnergy_eq_neg_two_cross`. It proves the derivative
premises with `cas`; `a < b`, the integrability conditions, and the vanishing
of `W * u ^ 2` at both endpoints must be hypotheses. `cas [ibp using h]` passes the symbolic
domain evidence `h` to the derivative checks.
-/

public meta section

namespace CAS.ExactTactic

open Lean Elab Tactic

/-- Prove a weighted-square integration-by-parts identity. -/
@[tactic_alt tacticCas]
elab (priority := high) "cas " "[" &"ibp" "]" : tactic =>
  Tactic.ProofCarrier.tacticEntry "cas [ibp]"
    (Tactic.IntegrationByParts.close none)

/-- Prove a weighted-square identity using explicit symbolic domain evidence. -/
@[tactic_alt tacticCas]
elab (priority := high) "cas " "[" &"ibp" " using " requirements:term "]" : tactic =>
  Tactic.ProofCarrier.tacticEntry "cas [ibp]"
    (Tactic.IntegrationByParts.close (some requirements))

end CAS.ExactTactic
