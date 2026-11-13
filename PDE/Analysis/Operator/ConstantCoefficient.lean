/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.DerivNotation

/-!
# Finite constant-coefficient line-derivative operators

A constant-coefficient linear differential operator `P = ∑ᵢ aᵢ ∂_{m_{i,1}} ⋯ ∂_{m_{i,kᵢ}}`
is a finite linear combination of iterated directional derivatives, with
directions `m_{i,j} ∈ V` and scalar coefficients `aᵢ`. We define such a
combination as one continuous linear operator `X →L[𝕜] X` on any space `X`
carrying Mathlib's `LineDeriv` structure (test functions, distributions, or
smooth functions). Each iterated derivative is Mathlib's
`LineDeriv.iteratedLineDerivOpCLM`.

## Main results

* `constantCoeffLineDerivCLM`: the operator `∑ i, a i • ∂^{m i}`.
* `constantCoeffLineDerivCLM_apply`: its action on an element of `X`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace PDE.Analysis

variable {𝕜 V X : Type*}
variable [NontriviallyNormedField 𝕜]
variable [AddCommGroup V]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
variable [IsTopologicalAddGroup X] [ContinuousConstSMul 𝕜 X]
variable [LineDeriv V X X] [LineDerivAdd V X X]
variable [LineDerivSMul 𝕜 V X X] [ContinuousLineDeriv V X X]

/-- The finite constant-coefficient operator
`∑ i, a i • ∂^{m i}` assembled from iterated directional derivatives. -/
def constantCoeffLineDerivCLM
    {N : ℕ}
    (a : Fin N → 𝕜)
    (order : Fin N → ℕ)
    (m : ∀ i, Fin (order i) → V) :
    X →L[𝕜] X :=
  ∑ i, a i • LineDeriv.iteratedLineDerivOpCLM 𝕜 X (m i)

/-- Applying the bundled operator to `x` gives the finite sum of the iterated directional
derivatives of `x`, each weighted by its coefficient. -/
@[simp]
theorem constantCoeffLineDerivCLM_apply
    {N : ℕ}
    (a : Fin N → 𝕜)
    (order : Fin N → ℕ)
    (m : ∀ i, Fin (order i) → V)
    (x : X) :
    constantCoeffLineDerivCLM a order m x =
      ∑ i, a i • LineDeriv.iteratedLineDerivOp (m i) x := by
  simp [constantCoeffLineDerivCLM]

end PDE.Analysis
