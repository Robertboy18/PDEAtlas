/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction

/-!
# The weak Laplacian

On `W^{2,p}(Ω)` the Laplacian is the sum of the diagonal second weak derivatives.
The coordinate maps make it a continuous linear map to `Lᵖ`. Its representative
identity keeps the second derivatives visible when stating almost-everywhere PDEs.

Use `open scoped Sobolev Laplacian` and write `Δ u` with Mathlib's
Laplacian notation. For a Sobolev input the result is an `Lᵖ` class, with
the positive sign convention `∑ i, ∂ᵢ∂ᵢ u`. An explicit `Lp` result type
distinguishes this weak operator from the classical Laplacian of a function.
To use its representative, coerce that `Lp` result to a function.
Bundled maps and compositions retain the name `wkpLaplacianCLM`.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev Laplacian

variable {n : ℕ} {Ω : Set (ℝ^n)} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Sum of the diagonal second weak-derivative coordinates. -/
def wkpLaplacianCLM : W^{2,p}(Ω) →L[ℝ] DerivLp n p Ω :=
  ∑ i : Fin n, wkpCoordinateCLM (pairDerivIndex n i i)

/-- Mathlib's Laplacian notation applies the same weak operator to Sobolev functions. -/
instance instLaplacian : Laplacian (W^{2,p}(Ω)) (DerivLp n p Ω) where
  laplacian u := wkpLaplacianCLM u

/-- The notation projection applies the bounded weak Laplacian. -/
@[simp] theorem laplacian_eq_wkpLaplacianCLM (u : W^{2,p}(Ω)) :
    Δ u = wkpLaplacianCLM u :=
  rfl

/-- The Laplacian is the `Lᵖ` sum of the diagonal second coordinates. -/
theorem wkpLaplacianCLM_apply (u : W^{2,p}(Ω)) :
    wkpLaplacianCLM u = ∑ i : Fin n, (u : WkpAmbientOn n 2 p Ω) (pairDerivIndex n i i) := by
  simp [wkpLaplacianCLM]

/-- Almost everywhere, the Laplacian representative is the sum of the diagonal representatives. -/
theorem wkpLaplacianCLM_coeFn (u : W^{2,p}(Ω)) :
    (wkpLaplacianCLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      fun x ↦ ∑ i : Fin n, (u : WkpAmbientOn n 2 p Ω) (pairDerivIndex n i i) x := by
  rw [wkpLaplacianCLM_apply]
  exact Lp.coeFn_fun_finsetSum _ _

end SobolevSpace.GraphSpace
