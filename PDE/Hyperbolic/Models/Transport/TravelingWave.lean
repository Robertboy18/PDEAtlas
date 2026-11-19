/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Transport
public import PDE.Representations.Similarity.Pointwise
import CAS.ExactTactic

/-!
# Traveling waves for the transport equation

Every differentiable profile transported at speed `c` has zero residual for
`u_t + c u_x = 0`. The field is a traveling wave (1) of Evans, §4.2.1, and the statement is
the one-dimensional case of the transport solution (3) of Evans, §2.1.1, through which we
prove it.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.1.1, equation (3); §4.2.1, equation (1).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (spatialGradient)

namespace TransportEquation

open PDE.Common
open PDE.Representations.Similarity

/-- A differentiable traveling-wave profile solves the one-dimensional transport equation. -/
theorem traveling_wave_1d_satisfies_transport (profile : ℝ → ℝ)
    (hprofile : ∀ s, DifferentiableAt ℝ profile s) (speed : ℝ) (xt : ℝ^2) :
    (∂[(0 : Fin 2)] (travelingWave1D profile speed)) xt + speed *
      (∂[(1 : Fin 2)] (travelingWave1D profile speed)) xt = 0 := by
  classical
  let spatialProfile : ℝ^1 → ℝ := fun x ↦ profile (x 0)
  have hspatialProfile : ∀ x, DifferentiableAt ℝ spatialProfile x := by
    intro x
    have hproj : DifferentiableAt ℝ (fun y : ℝ^1 ↦ y 0) x := by
      cas
    simpa [spatialProfile, Function.comp_def] using (hprofile (x 0)).comp x hproj
  have htransport := TransportEquation.transportOperator_transportFunction_eq_zero (n := 1)
    (EuclideanSpace.single (0 : Fin 1) speed) spatialProfile hspatialProfile xt
  have hfield : TransportEquation.transportFunction (n := 1)
          (EuclideanSpace.single (0 : Fin 1) speed) spatialProfile =
        travelingWave1D profile speed := by
    funext p
    simp [TransportEquation.transportFunction, TransportEquation.transportInner_apply,
      spatialProfile, travelingWave1D, sub_eq_add_neg, mul_comm]
  rw [hfield, TransportEquation.transportOperator_eq_timeDeriv_add_dot_spatialGradient]
    at htransport
  simpa [spatialGradient, spatialPartCLM_apply, PDE.gradient_apply_eq_partialDeriv] using htransport

end TransportEquation
