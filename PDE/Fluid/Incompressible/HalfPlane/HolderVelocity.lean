/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.WeightedHessian

/-!
# The velocity of a decaying Hölder vorticity

For a vorticity `f` of the decaying Hölder class (`IncompressibleFlow.IsHolderVorticity α f`:
continuous on the closed upper half-plane, odd in `x₀`, decaying, locally Hölder), the gradient of
the grouped quadrant potential `Ψ = GreenFunction.quadrantPotential f` is the grouped Biot-Savart
integral

`∂ⱼΨ(x) = ∫_{ℝ²₊₊} gⱼₛ(x, y) f(y) dy`

at every point of the plane, and the integral converges absolutely
(`IsHolderVorticity.partialDeriv_quadrantPotential`,
`IsHolderVorticity.integrableOn_symmetrizedKernel_gradientKernel`). This is the first-order
formula `partialDeriv_quadrantPotential` of the class `IsDecayingVorticity` with the `C²`
hypothesis replaced by local Hölder continuity. The proof uses the decomposition of
`IsHolderVorticity.quadrantPotential_eq` at the radius `R = 2(|x| + 1)`: near `x`, `Ψ` is the Green
potential of the compact continuous near source, whose velocity is the grouped integral of that
source, plus the potential of the far source, whose velocity on `B(0, R/2)` is the grouped
integral of the far source.

With the weighted bound `|f(y)| ≤ M min(|y|^a, |y|^(-b))`, `a, b > 0`, the strain integrand `K₁ f`
is integrable as well, and the velocity with its strain part removed is one absolutely convergent
grouped integral (`IsHolderVorticity.partialDeriv_quadrantPotential_sub_mixedCoefficient`):
`∂ⱼΨ(x) - c x_{j'} = ∫_{ℝ²₊₊} (gⱼₛ(x, y) - (4/π) x_{j'} K₁(y)) f(y) dy` with `j' = 1 - j` and
`c = mixedCoefficient f`. For `(u, v) = (-∂₁Ψ, ∂₀Ψ)` and the strain `u_x(0) = -c` of the
half-plane velocity, these are the strain-free velocities `-ũ = -(u - u_x(0) x₀)` and
`ṽ = v + u_x(0) x₁`.

## Main results

* `IsHolderVorticity.integrableOn_symmetrizedKernel_gradientKernel`: the grouped velocity
  integrand of a decaying Hölder vorticity is integrable at every point.
* `IsHolderVorticity.partialDeriv_quadrantPotential`: `∂ⱼΨ(x) = ∫_{ℝ²₊₊} gⱼₛ(x, y) f(y) dy` at
  every point of the plane.
* `IsHolderVorticity.partialDeriv_quadrantPotential_sub_mixedCoefficient`: under the weighted
  bound, `∂ⱼΨ(x) - c x_{j'} = ∫_{ℝ²₊₊} (gⱼₛ(x, y) - (4/π) x_{j'} K₁(y)) f(y) dy`, an absolutely
  convergent integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set GreenFunction PotentialTheory PotentialTheory.Planar

namespace IncompressibleFlow

variable {α : ℝ} {f : ℝ^2 → ℝ}

/-- The radius of the near-far split at `x`: `2(|x| + 1)`, with `|x| < R/2`. -/
private theorem norm_lt_splitRadius (x : ℝ^2) : ‖x‖ < 2 * (‖x‖ + 1) / 2 := by linarith

/-- **Integrability of the grouped velocity integrand** of a decaying Hölder vorticity at every
point. -/
theorem IsHolderVorticity.integrableOn_symmetrizedKernel_gradientKernel
    (hf : IsHolderVorticity α f) (j : Fin 2) (x : ℝ^2) :
    IntegrableOn (fun y ↦ symmetrizedKernel (gradientKernel j) x y * f y)
      GreenFunction.quadrant := by
  have hR : 0 < 2 * (‖x‖ + 1) := by positivity
  have hN := continuous_nearSource (R := 2 * (‖x‖ + 1)) hf.continuousOn
  have hNc := hasCompactSupport_nearSource (f := f) hR
  have hNodd : ∀ y, 0 ≤ y 1 →
      nearSource (2 * (‖x‖ + 1)) f (PDE.Common.coordinateReflection 0 y) =
        -nearSource (2 * (‖x‖ + 1)) f y := fun y hy ↦ nearSource_odd hf.odd hy
  refine ((integrableOn_symmetrizedKernel_gradientKernel_of_compact hN hNc hNodd j x).add
    (integrableOn_symmetrizedKernel_gradientKernel_of_far (hf.isQuadrantFarDensity_farSource hR)
      j (norm_lt_splitRadius x))).congr_fun (fun y hy ↦ ?_) measurableSet_quadrant
  simp only [Pi.add_apply, nearSource_of_nonneg (le_of_lt hy.2), farSource]
  ring

/-- **The velocity of a decaying Hölder vorticity**: `∂ⱼΨ(x) = ∫_{ℝ²₊₊} gⱼₛ(x, y) f(y) dy` at every
point, for the grouped quadrant potential `Ψ`. -/
theorem IsHolderVorticity.partialDeriv_quadrantPotential (hf : IsHolderVorticity α f) (j : Fin 2)
    (x : ℝ^2) :
    (∂[j] (quadrantPotential f)) x =
      ∫ y in GreenFunction.quadrant, symmetrizedKernel (gradientKernel j) x y * f y := by
  have hR : 0 < 2 * (‖x‖ + 1) := by positivity
  have hxR := norm_lt_splitRadius x
  have hN := continuous_nearSource (R := 2 * (‖x‖ + 1)) hf.continuousOn
  have hNc := hasCompactSupport_nearSource (f := f) hR
  have hNodd : ∀ y, 0 ≤ y 1 →
      nearSource (2 * (‖x‖ + 1)) f (PDE.Common.coordinateReflection 0 y) =
        -nearSource (2 * (‖x‖ + 1)) f y := fun y hy ↦ nearSource_odd hf.odd hy
  have hfar := hf.isQuadrantFarDensity_farSource hR
  rw [PDE.partialDeriv_congr_nhds j (hf.quadrantPotential_eventuallyEq hR hxR),
    PDE.partialDeriv_add ((contDiff_one_halfSpaceGreenPotential hN hNc).differentiable
      one_ne_zero x) ((hf.contDiffAt_farSource hR hxR (n := 1)).differentiableAt one_ne_zero),
    partialDeriv_halfSpaceGreenPotential_eq_setIntegral hN hNc hNodd,
    partialDeriv_quadrantPotential_ball hfar j hxR,
    ← integral_add (integrableOn_symmetrizedKernel_gradientKernel_of_compact hN hNc hNodd j x)
      (integrableOn_symmetrizedKernel_gradientKernel_of_far hfar j hxR)]
  refine setIntegral_congr_fun measurableSet_quadrant fun y hy ↦ ?_
  rw [nearSource_of_nonneg (le_of_lt hy.2), farSource]
  ring

/-- **The strain-free velocity of a weighted Hölder vorticity.** If
`|f(y)| ≤ M min(|y|^a, |y|^(-b))` with `a, b > 0`, the velocity of `Ψ` with the strain part
removed is the absolutely convergent grouped integral
`∂ⱼΨ(x) - c x_{j'} = ∫_{ℝ²₊₊} (gⱼₛ(x, y) - (4/π) x_{j'} K₁(y)) f(y) dy`, where `j' = 1 - j` is the
other coordinate and `c = mixedCoefficient f = (4/π) ∫_{ℝ²₊₊} K₁ f` is the coefficient of `x₀ x₁`
at the origin. For the velocity `(u, v) = (-∂₁Ψ, ∂₀Ψ)` with strain `u_x(0) = -c` these are `-ũ`
(`j = 1`) and `ṽ` (`j = 0`). -/
theorem IsHolderVorticity.partialDeriv_quadrantPotential_sub_mixedCoefficient
    (hf : IsHolderVorticity α f) {M a b : ℝ}
    (hS : ∀ y : ℝ^2, 0 ≤ y 1 → |f y| ≤ M * min (‖y‖ ^ a) (‖y‖ ^ (-b))) (ha : 0 < a) (hb : 0 < b)
    (j : Fin 2) (x : ℝ^2) :
    IntegrableOn (fun y ↦ (symmetrizedKernel (gradientKernel j) x y -
        4 / Real.pi * x (1 - j) * hessianKernel 0 1 y) * f y) GreenFunction.quadrant ∧
      (∂[j] (quadrantPotential f)) x - mixedCoefficient f * x (1 - j) =
        ∫ y in GreenFunction.quadrant, (symmetrizedKernel (gradientKernel j) x y -
          4 / Real.pi * x (1 - j) * hessianKernel 0 1 y) * f y := by
  have hg := hf.integrableOn_symmetrizedKernel_gradientKernel j x
  have hK := (integrableOn_hessianKernel_mul_of_le_min hS hf ha hb).const_mul
    (4 / Real.pi * x (1 - j))
  have he : (fun y ↦ (symmetrizedKernel (gradientKernel j) x y -
      4 / Real.pi * x (1 - j) * hessianKernel 0 1 y) * f y) =
      fun y ↦ symmetrizedKernel (gradientKernel j) x y * f y -
        4 / Real.pi * x (1 - j) * (hessianKernel 0 1 y * f y) := funext fun y ↦ by ring
  refine ⟨he ▸ hg.sub hK, ?_⟩
  rw [he, integral_sub hg hK, integral_const_mul, hf.partialDeriv_quadrantPotential j,
    mixedCoefficient]
  ring

end IncompressibleFlow
