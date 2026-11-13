/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Retarded.Derivative

/-!
# Initial traces of a retarded integral

The integral vanishes when the time interval collapses. If the kernel also
vanishes at the initial point, the entire first derivative vanishes there.
Joint continuity of the kernel and its space-age derivative suffices;
no derivative in the forcing index is required.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The collapsed integration interval gives zero initial displacement. -/
@[simp]
theorem retardedIntegral_initial (F : ℝ → E × ℝ → V) (x : E) :
    retardedIntegral F (x, 0) = 0 := by
  simp [retardedIntegral]

variable [FiniteDimensional ℝ E] [CompleteSpace V]

/-- A zero initial kernel value gives zero full first derivative at time zero. -/
theorem hasFDerivAt_retardedIntegral_initial
    {F : ℝ → E × ℝ → V} (hF : ∀ s, Differentiable ℝ (F s))
    (hc : Continuous (fun p : ℝ × (E × ℝ) ↦ F p.1 p.2))
    (hD : Continuous (fun p : ℝ × (E × ℝ) ↦ fderiv ℝ (F p.1) p.2))
    {x : E} (hx : F 0 (x, 0) = 0) :
    HasFDerivAt (retardedIntegral F) (0 : (E × ℝ) →L[ℝ] V) (x, 0) := by
  simpa [hx] using hasFDerivAt_retardedIntegral hF hc hD (x, 0)

end PDE.Analysis
