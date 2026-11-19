/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Derivatives of sphere-valued maps

Differentiating the locally constant squared norm places every derivative vector in the
orthogonal complement of the value of the map. Only the germ of the map at the point
matters.
-/

@[expose] public section

open Filter
open scoped Topology InnerProductSpace

namespace PDE.Analysis

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Every derivative vector of a locally sphere-valued map is orthogonal to its value. -/
theorem inner_fderiv_eq_zero_of_eventually_norm_eq {f : E → H} {x : E} {r : ℝ}
    (hf : DifferentiableAt ℝ f x) (hr : ∀ᶠ y in 𝓝 x, ‖f y‖ = r) (v : E) :
    ⟪f x, fderiv ℝ f x v⟫_ℝ = 0 := by
  have hconst : (fun y ↦ ‖f y‖ ^ 2) =ᶠ[𝓝 x] fun _ ↦ r ^ 2 :=
    hr.mono fun _ hy ↦ congrArg (fun t : ℝ ↦ t ^ 2) hy
  have hzero := hf.hasFDerivAt.norm_sq.unique
    ((hasFDerivAt_const (r ^ 2) x).congr_of_eventuallyEq hconst)
  have hv := congrArg (fun A : E →L[ℝ] ℝ ↦ A v) hzero
  simpa using hv

end PDE.Analysis
