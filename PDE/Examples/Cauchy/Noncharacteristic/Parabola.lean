/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Geometry.Hypersurface.Conormal
public import PDE.Common.Euclidean.SpaceTime
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# A curved noncharacteristic initial curve

The parabola `x₀ = x₁²` is the graph of `x₁ ↦ x₁²` and has local parametrizations
with conormal `(1, -2x₁)` (`parabola_hasConormalParametrizations`). The first
conormal coordinate never vanishes, so a pure `x₀` principal derivative of any order
is noncharacteristic.
-/

@[expose] public noncomputable section

open Set PDE.Analysis PDE.Common

namespace PDE.Examples.Cauchy.Quasilinear

/-- The parabola `x₀ = x₁²`. -/
def parabola : Set (ℝ^2) := {x | x 0 = (x 1) ^ 2}

/-- A nonzero conormal field on the parabola. -/
def parabolaNormal (x : ℝ^2) : ℝ^2 := WithLp.toLp 2 ![1, -2 * x 1]

/-- The chosen conormal has first component one everywhere. -/
@[simp]
theorem parabolaNormal_zero (x : ℝ^2) : parabolaNormal x 0 = 1 := rfl

/-- The conormal field never vanishes. -/
theorem parabolaNormal_ne_zero (x : ℝ^2) : parabolaNormal x ≠ 0 := by
  intro h
  have := congrArg (fun v : ℝ^2 ↦ v 0) h
  simp at this

/-- The parabola has local parametrizations with conormal `parabolaNormal`. -/
theorem parabola_hasConormalParametrizations :
    HasConormalParametrizations (ℝ^1) parabola
      (fun x ↦ (innerSL ℝ (parabolaNormal x)).toLinearMap) := by
  let g : ℝ^1 → ℝ := fun z ↦ (z 0) ^ 2
  have hg : Differentiable ℝ g := by
    dsimp [g]
    cas
  have hD (z : ℝ^1) :
      fderiv ℝ g z = (2 * z 0) • EuclideanSpace.proj (0 : Fin 1) := by
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.ext
    intro i
    fin_cases i
    simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    change fderiv ℝ g z (EuclideanSpace.single 0 1) = 2 * z 0 * 1
    rw [mul_one]
    dsimp only [g]
    cas
  have h := (hasConormalParametrizations_graph hg).map
    (spaceTimeContinuousLinearEquiv 1).symm
  have hset :
      (spaceTimeContinuousLinearEquiv 1).symm '' (range fun z : ℝ^1 ↦ (z, g z)) =
        parabola := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      simp [parabola, g, joinSpaceTime, timeSpaceCons]
    · intro hx
      refine ⟨(spatialPart x, g (spatialPart x)), ⟨spatialPart x, rfl⟩, ?_⟩
      change timeSpaceCons (g (spatialPart x)) (spatialPart x) = x
      rw [show g (spatialPart x) = x 0 from by
        simpa [g, parabola] using hx.symm]
      exact timeSpaceCons_spatialPart x
  rw [hset] at h
  convert h using 1
  funext x
  ext w
  simp only [ContinuousLinearEquiv.symm_symm, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe, sub_apply, ContinuousLinearMap.comp_apply,
    spaceTimeContinuousLinearEquiv_apply, splitSpaceTime, hD, smul_apply,
    smul_eq_mul, innerSL_apply_apply]
  simp [parabolaNormal, PiLp.inner_apply, Fin.sum_univ_two, sub_eq_add_neg, mul_comm]

end PDE.Examples.Cauchy.Quasilinear
