/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonuniqueness.Symmetry.Action
public import PDE.Fluid.NavierStokes.Stationary.Linearization
public import PDE.Fluid.Incompressible.LerayProjection.Isometry

/-!
# Equivariance of the stationary self-similar operators

For `g = groupElement θ s` the derivative of `act θ s u` at `x` is `g ∘ Du(g⁻¹ x) ∘ g⁻¹` and its
Laplacian is `g Δu(g⁻¹ x)`, while `x = g (g⁻¹ x)`. Hence the stationary self-similar velocity
operator `-½(U + ξ·∇U) + (U·∇)U - ΔU` and its linearization commute with the action on `C²`
fields. On whole-space `L²` the action is the linear isometry equivalence `actL2 θ s`, which
agrees with `act θ s` almost everywhere and commutes with the Leray projection
(`lerayProjection_act`).
-/

@[expose] public noncomputable section

namespace NavierStokes.Symmetry

set_option linter.missingDocs true

variable {U v : ℝ^3 → ℝ^3}

/-- The derivative of a transformed `C²` field applied to a vector. -/
private theorem fderiv_act_apply {φ : ℝ^3 → ℝ^3} (hφ : ContDiff ℝ 2 φ) (θ : ℝ) (s : Bool)
    (x w : ℝ^3) :
    fderiv ℝ (act θ s φ) x w =
      groupElement θ s (fderiv ℝ φ ((groupElement θ s).symm x) ((groupElement θ s).symm w)) := by
  rw [fderiv_act ((hφ.differentiable (by simp)) _)]
  rfl

/-- The stationary self-similar velocity operator commutes with the axisymmetry group on `C²`
fields. -/
theorem stationaryVelocityOperator_act (hU : ContDiff ℝ 2 U) (θ : ℝ) (s : Bool) :
    stationaryVelocityOperator (act θ s U) = act θ s (stationaryVelocityOperator U) := by
  funext x
  simp only [stationaryVelocityOperator, PDE.advectiveDerivative, fderiv_act_apply hU,
    laplacian_act hU, act_apply, LinearIsometryEquiv.symm_apply_apply, map_add, map_sub,
    map_smul]

/-- The linearized stationary operator commutes with the axisymmetry group on `C²` fields. -/
theorem stationaryVelocityLinearization_act (hU : ContDiff ℝ 2 U) (hv : ContDiff ℝ 2 v)
    (θ : ℝ) (s : Bool) :
    stationaryVelocityLinearization (act θ s U) (act θ s v) =
      act θ s (stationaryVelocityLinearization U v) := by
  funext x
  simp only [stationaryVelocityLinearization, PDE.advectiveDerivative, fderiv_act_apply hU,
    fderiv_act_apply hv, laplacian_act hv, act_apply, LinearIsometryEquiv.symm_apply_apply,
    map_add, map_sub, map_smul]

/-- The action of a group element on whole-space `L²` vector fields. -/
def actL2 (θ : ℝ) (s : Bool) : IncompressibleFlow.WholeSpaceL2 3 ≃ₗᵢ[ℝ]
    IncompressibleFlow.WholeSpaceL2 3 :=
  IncompressibleFlow.l2Isometry (groupElement θ s)

/-- The `L²` action agrees with the pointwise action almost everywhere. -/
theorem actL2_ae (θ : ℝ) (s : Bool) (f : IncompressibleFlow.WholeSpaceL2 3) :
    actL2 θ s f =ᵐ[MeasureTheory.volume] act θ s f :=
  IncompressibleFlow.l2Isometry_ae (groupElement θ s) f

/-- The `L²` action preserves the divergence-free subspace. -/
theorem actL2_mem_l2Solenoidal (θ : ℝ) (s : Bool) {v : IncompressibleFlow.WholeSpaceL2 3}
    (hv : v ∈ IncompressibleFlow.l2Solenoidal 3) :
    actL2 θ s v ∈ IncompressibleFlow.l2Solenoidal 3 :=
  IncompressibleFlow.l2Isometry_mem_solenoidal (groupElement θ s) hv

/-- The Leray projection commutes with the axisymmetry group. -/
theorem lerayProjection_act (θ : ℝ) (s : Bool) (v : IncompressibleFlow.WholeSpaceL2 3) :
    IncompressibleFlow.lerayProjection 3 (actL2 θ s v) =
      actL2 θ s (IncompressibleFlow.lerayProjection 3 v) :=
  IncompressibleFlow.lerayProjection_l2Isometry (groupElement θ s) v

end NavierStokes.Symmetry
