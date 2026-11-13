/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import PDE.CoordinateSystems.Axisymmetric

/-!
# Axisymmetric meridian measure

The meridian weight `r` is the measure `Measure.volumeIoiPow 1 × volume` on the meridian
half-plane.

The measure below is `r dr dz`, without the angular factor `2π`. The corresponding
three-dimensional change of variables is `integral_cylindricalLift`.

For the cylindrical-coordinate convention and its use in incompressible flow, see Ukhovskii and
Yudovich, and Majda and Bertozzi.

## References

* M. R. Ukhovskii and V. I. Yudovich, "Axially symmetric flows of ideal and viscous fluids
  filling the whole space", *J. Appl. Math. Mech.* 32 (1968), no. 1, 52-62.
  <https://doi.org/10.1016/0021-8928(68)90147-0>
* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge University
  Press, 2001. <https://doi.org/10.1017/CBO9780511613203>
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace PDE.Analysis

/-- The open meridian half-plane with positive cylindrical radius. -/
abbrev MeridianHalfPlane :=
  Set.Ioi (0 : ℝ) × ℝ

/-- Forget the positivity proof and regard a meridian-half-plane point as `(r,z) ∈ ℝ^2`. -/
def meridianHalfPlaneCoordinates (x : MeridianHalfPlane) : ℝ^2 :=
  WithLp.toLp 2 ![x.1.1, x.2]

/-- Embedding a half-plane point `(r, z)` with `r > 0` into `ℝ^3` as `(r, 0, z)` and reading off
its meridian coordinates returns `(r, z)`; the sign condition on `r` (only `r ≥ 0` is used) is
what makes the cylindrical radius recoverable. -/
@[simp]
theorem meridianCoordinates_meridianPoint_of_halfPlane (x : MeridianHalfPlane) :
    PDE.CoordinateSystems.meridianCoordinates
        (PDE.CoordinateSystems.meridianPoint x.1.1 x.2) =
      meridianHalfPlaneCoordinates x := by
  exact PDE.CoordinateSystems.meridianCoordinates_meridianPoint
    x.1.1 x.2 (le_of_lt x.1.2)

/-- The meridian measure `r dr dz` for three-dimensional axisymmetric integration. -/
def axisymmetricMeridianMeasure : Measure MeridianHalfPlane :=
  (Measure.volumeIoiPow 1).prod volume

/-- The meridian measure of a radial interval times an axial set. -/
theorem axisymmetricMeridianMeasure_Iio_prod (R : Set.Ioi (0 : ℝ)) (s : Set ℝ) :
    axisymmetricMeridianMeasure (Set.Iio R ×ˢ s) =
      ENNReal.ofReal (R.1 ^ 2 / 2) * volume s := by
  simp only [axisymmetricMeridianMeasure, Measure.prod_prod,
    Measure.volumeIoiPow_apply_Iio]
  norm_num

end PDE.Analysis

end
