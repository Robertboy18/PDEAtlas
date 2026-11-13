/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.Pole
public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GreenPotential
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.BoundaryRegularity
import PDE.FDeriv.Calculus
import PDE.FDeriv.Reflection.Coordinate

/-!
# Exact half-plane inversion of a compact Laplacian

For a compactly supported, normally odd `C²` function `u`, the actual
method-of-images integral satisfies `G(Δu) = -u` on the whole plane.
The proof uses the translated pole identity, retaining the sign convention
that the Green kernel inverts `-Δ`.

## Main results

* `halfSpaceGreenPotential_laplacian_eq_neg`: `G(Δu) = -u` at every point of the plane for
  compactly supported normally odd `C²` functions `u`.
* `halfSpaceGreenPotential_const_mul_laplacian`: the same with a constant amplitude,
  `G(a Δu) = -a u`.
-/

@[expose] public noncomputable section

namespace GreenFunction

open MeasureTheory SobolevSpace
open PDE (laplacian)

/-- The Laplacian of a normally odd `C²` function on the plane is normally odd. -/
private theorem laplacian_normally_odd {u : ℝ^2 → ℝ}
    (hu : ContDiff ℝ 2 u) (hodd : ∀ y, u (HalfSpace.reflect 2 y) = -u y) :
    ∀ y, laplacian u (HalfSpace.reflect 2 y) = -laplacian u y := by
  have hreflect := reflect_two_eq_coordinateReflection
  have hfun : (fun y ↦ u (PDE.Common.coordinateReflection (1 : Fin 2) y)) = -u := by
    funext y
    rw [← hreflect]
    exact hodd y
  intro y
  rw [hreflect, ← PDE.Common.laplacian_comp_coordinateReflection (1 : Fin 2) u y hu,
    hfun, PDE.laplacian_neg]

/-- The half-plane Green integral inverts the negative Laplacian on compact normally odd
`C²` functions, including points on and below the boundary. -/
theorem halfSpaceGreenPotential_laplacian_eq_neg {u : ℝ^2 → ℝ}
    (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u)
    (hodd : ∀ y, u (HalfSpace.reflect 2 y) = -u y) (x : ℝ^2) :
    halfSpaceGreenPotential (laplacian u) x = -u x := by
  have hkernel (y : ℝ^2) :
      PotentialTheory.fundamentalSolution 2 (x - y) =
        PotentialTheory.fundamentalSolution 2 (y - x) :=
    PotentialTheory.fundamentalSolution_eq_of_norm_eq (norm_sub_rev x y)
  have hi : Integrable
      (fun y ↦ PotentialTheory.fundamentalSolution 2 (x - y) * laplacian u y) := by
    simpa only [hkernel] using
      PotentialTheory.integrable_fundamentalSolution_sub_mul_laplacian hu hc x
  rw [halfSpaceGreenPotential_eq_convolution_of_odd_of_integrable
    (laplacian u) (laplacian_normally_odd hu hodd) x hi,
    MeasureTheory.convolution_mul_swap]
  simpa only [hkernel] using
    PotentialTheory.integral_fundamentalSolution_sub_mul_laplacian (by norm_num) hu hc x

/-- A constant amplitude passes through the exact compact half-plane inverse. -/
theorem halfSpaceGreenPotential_const_mul_laplacian {u : ℝ^2 → ℝ}
    (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u)
    (hodd : ∀ y, u (HalfSpace.reflect 2 y) = -u y) (a : ℝ) (x : ℝ^2) :
    halfSpaceGreenPotential (fun y ↦ a * laplacian u y) x = -a * u x := by
  have h := halfSpaceGreenPotential_laplacian_eq_neg (hu.const_smul a)
    (show HasCompactSupport (fun y ↦ a * u y) from hc.mul_left)
    (fun y ↦ by simp only [smul_eq_mul, hodd, mul_neg]) x
  have hlap : laplacian (fun y ↦ a * u y) = fun y ↦ a * laplacian u y :=
    funext (PDE.laplacian_const_smul a u)
  simpa only [smul_eq_mul, hlap, neg_mul] using h

end GreenFunction
