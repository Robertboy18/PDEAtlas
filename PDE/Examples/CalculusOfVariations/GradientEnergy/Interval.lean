/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.CalculusOfVariations.GradientEnergy.Density
public import PDE.CalculusOfVariations.GradientEnergy.L2.Resolvent
public import PDE.CalculusOfVariations.GradientEnergy.L2.Affine
public import PDE.Spaces.Sobolev.Boundary.Atlas.UnitBall.SmoothGraph
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# A nonquadratic gradient energy on the interval

The one-dimensional Euclidean unit ball is the interval `(-1,1)`, and its smooth
graph boundary comes from the general ball construction. The energy of the
nonquadratic signed density is proper, convex and lower semicontinuous on `L²`, and
equals `-6` at zero. Its subdifferential has domain `H² ∩ H¹₀` and is the operator
`-(1 + cos(Du)/4) D²u`, and every `L²` load has a unique resolvent with an estimate
`‖W‖ ≤ M ‖f‖`.
-/

open scoped Sobolev

@[expose] public noncomputable section

namespace PDE.Examples.GradientEnergy

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open PDE.CalculusOfVariations PDE.Analysis.Convex
open scoped ENNReal NNReal

local notation "Ω₀" => Boundary.Atlas.UnitBall.domain 1
local notation "I" => l2DirichletGradientEnergy (Ω := Ω₀) signedDensity

/-- The signed interval energy is proper, convex and lower semicontinuous on `L²`. -/
theorem signedInterval_energy_properties :
    IsProper I ∧ Convex ℝ (realEpigraph I) ∧ LowerSemicontinuous I := by
  have hΩ₀ := Boundary.Atlas.UnitBall.isOpen_domain 1
  have hb := Boundary.Atlas.UnitBall.bounded_domain 1
  refine ⟨isProper_l2DirichletGradientEnergy _, ?_, ?_⟩
  · exact convex_realEpigraph_l2DirichletGradientEnergy hΩ₀
      ((PDE.Analysis.strongConvexOn_of_hessian_bound signedDensity_contDiff
        signedDensity_hessian_lower).strictConvexOn (by norm_num)).convexOn
      (integrable_gradientDensity_of_hessian_bounds hb signedDensity_contDiff
        (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (0 : ℝ) ≤ 5 / 4)
        signedDensity_hessian_lower signedDensity_hessian_upper)
  · exact lowerSemicontinuous_l2DirichletGradientEnergy_of_hessian_bounds (by norm_num)
      hΩ₀ hb signedDensity_contDiff (by norm_num : (0 : ℝ) < 3 / 4)
      (by norm_num : (0 : ℝ) ≤ 5 / 4)
      signedDensity_hessian_lower signedDensity_hessian_upper

/-- The energy of zero is `-6`: the density value `-3` times the length `2`. -/
theorem signedInterval_energy_zero : I 0 = (-6 : ℝ) := by
  have hvol : volume Ω₀ = 2 := by
    change volume (Metric.ball (0 : ℝ^1) 1) = 2
    norm_num [InnerProductSpace.volume_ball_of_dim_odd (k := 0) (by simp) (0 : ℝ^1) 1]
  rw [l2DirichletGradientEnergy_zero (Boundary.Atlas.UnitBall.isOpen_domain 1),
    signedDensity_zero]
  norm_num [Measure.real, domainMeasure, hvol]

/-- The domain of the subdifferential is exactly `H² ∩ H¹₀`. -/
theorem signedInterval_subdifferentialDomain :
    subdifferentialDomain I = l2H2DirichletDomain 1 Ω₀ :=
  subdifferentialDomain_l2DirichletGradientEnergy
    (Boundary.Atlas.UnitBall.isOpen_domain 1) (Boundary.Atlas.UnitBall.bounded_domain 1)
    (Boundary.Atlas.UnitBall.hasContDiffGraphBoundary 1 2)
    signedDensity_contDiff (by norm_num : (0 : ℝ) < 3 / 4)
    (C := (5 / 4 : ℝ≥0)) signedDensity_hessian_lower signedDensity_hessian_upper

/-- The one-dimensional nonlinear operator is `-(1 + cos(Du)/4) D²u`, evaluated on
the `H²` representative. -/
theorem signedInterval_operator (W : W^{2,2}(Ω₀)) (u : H¹₀(Ω₀))
    (hu : lowerOrderCLM (by omega : 1 ≤ 2) W = u.val) (f : DerivLp 1 2 Ω₀) :
    f ∈ subdifferential I (baseCoordCLM u) ↔
      ∀ᵐ x ∂domainMeasure 1 Ω₀,
        f x = -(1 + Real.cos (derivCoordCLM 0 u x) / 4) *
          wkpCoordinateCLM (singleDerivIndex 1 0) (h2FirstDerivativeFamily W 0) x := by
  rw [mem_subdifferential_l2DirichletGradientEnergy_iff_hessian
    (Boundary.Atlas.UnitBall.isOpen_domain 1) (Boundary.Atlas.UnitBall.bounded_domain 1)
    (Boundary.Atlas.UnitBall.hasContDiffGraphBoundary 1 2)
    signedDensity_contDiff (by norm_num : (0 : ℝ) < 3 / 4)
    (C := (5 / 4 : ℝ≥0)) signedDensity_hessian_lower signedDensity_hessian_upper W u hu f]
  have hb : wkpBaseCoordinateCLM (h2FirstDerivativeFamily W 0) = derivCoordCLM 0 u := by
    rw [h2FirstDerivativeFamily_base, hu]
    rfl
  simp only [signedDensity_hessian, Fin.sum_univ_one,
    FiniteProductComposition.values, FiniteProductComposition.derivatives,
    PiLp.single_apply, ite_true, mul_one, hb, neg_mul]
  rfl

/-- Every `L²` load has a unique resolvent in `H² ∩ H¹₀`, with one estimate constant
for all loads. -/
theorem signedInterval_resolvent :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ f : DerivLp 1 2 Ω₀, ∃ W : W^{2,2}(Ω₀),
      lowerOrderCLM (by omega : 1 ≤ 2) W ∈ (h10SubmoduleOn (n := 1) (Ω := Ω₀)) ∧
      (f - wkpBaseCoordinateCLM W) ∈ subdifferential I (wkpBaseCoordinateCLM W) ∧
      ‖W‖ ≤ M * ‖f‖ ∧
      ∀ z : DerivLp 1 2 Ω₀, f - z ∈ subdifferential I z → z = wkpBaseCoordinateCLM W :=
  exists_H2_resolvent_l2DirichletGradientEnergy
    (Boundary.Atlas.UnitBall.isOpen_domain 1) (Boundary.Atlas.UnitBall.bounded_domain 1)
    (Boundary.Atlas.UnitBall.hasContDiffGraphBoundary 1 2)
    signedDensity_contDiff (by norm_num : (0 : ℝ) < 3 / 4)
    (C := (5 / 4 : ℝ≥0)) signedDensity_hessian_lower signedDensity_hessian_upper

end PDE.Examples.GradientEnergy
