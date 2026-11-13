/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Quasilinear.Boundary.Chart.Extension
public import PDE.Analysis.MeasureTheory.Lp.Superposition

/-!
# Integrability of the extended nonlinear chart flux

Centering the physical flux is useful on the half-space, which has infinite
measure. The extended flux then has no constant growth term, so its state
Lipschitz bound preserves `Lᵖ` without a finite-measure assumption.
-/

@[expose] public noncomputable section

open TopologicalSpace
open scoped Distributions

namespace PDE.Elliptic.Regularity.Quasilinear

open MeasureTheory
open scoped ENNReal

variable {n : ℕ} {p : ℝ≥0∞}

/-- The extended chart flux sends an `Lᵖ` vector field to an `Lᵖ` vector
field. The measure and exponent are arbitrary. -/
theorem memLp_extendedChartFlux
    {μ : Measure (ℝ^n)}
    (E : OpenPartialHomeomorph (ℝ^n) (ℝ^n))
    (hE : ContDiff ℝ 2 (fun x ↦ E x))
    (hSymm : ContDiff ℝ 2 (fun y ↦ E.symm y))
    (A : ℝ^n → ℝ^n) (hA : Continuous A) (hzero : A 0 = 0)
    (κ σ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (β : ℝ) {D : ℝ}
    (hstate : ∀ y z w, ‖extendedChartFlux E A κ σ β y w -
      extendedChartFlux E A κ σ β y z‖ ≤ D * ‖w - z‖)
    {v : ℝ^n → ℝ^n} (hv : MemLp v p μ) :
    MemLp (fun y ↦ extendedChartFlux E A κ σ β y (v y)) p μ := by
  apply hv.comp_of_norm_le (C := D) (a := fun _ ↦ 0)
    (continuous_extendedChartFlux E hE hSymm A hA κ σ β).measurable
    (MemLp.zero : MemLp (fun _ : ℝ^n ↦ (0 : ℝ)) p μ)
  filter_upwards with y
  intro z
  simpa only [extendedChartFlux_zero E A hzero κ σ β y, sub_zero, zero_add] using
    hstate y 0 z

end PDE.Elliptic.Regularity.Quasilinear
