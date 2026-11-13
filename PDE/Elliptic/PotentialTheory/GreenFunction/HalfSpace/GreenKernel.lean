/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.Definitions
public import PDE.Elliptic.PotentialTheory.FundamentalSolution
public import PDE.Spaces.Sobolev.Boundary.Geometry.HalfSpace
import PDE.FDeriv.Calculus

/-!
# Green kernel for the half-space

We define Green's function of `-Δ` for the upper half-space `ℝ^n₊ = {x : xₙ > 0}` by the method of
images. Reflecting the pole `x` in the boundary hyperplane to `x̃ = (x₁, …, xₙ₋₁, -xₙ)` gives a
corrector `y ↦ Φ(y - x̃)` that is harmonic on `ℝ^n₊`, since its singularity lies in the lower
half-space, and agrees with `Φ(y - x)` when `yₙ = 0`, since then `‖y - x̃‖ = ‖y - x‖`. Hence

`G(x, y) = Φ(y - x) - Φ(y - x̃)`

vanishes on the boundary and is harmonic in `y` on `ℝ^n₊ \ {x}`. This is Evans's construction in
§2.2.4(b). The geometry (`upper`, `boundary`, `reflect`) is taken from `SobolevSpace.HalfSpace`; the
Green potential and its Poisson inversion for odd planar sources are in `GreenPotential`.

## Main definitions

* `halfSpaceGreenFunction`: the method-of-images kernel, with the pole as first argument.

## Main results

* `halfSpaceGreenFunction_comm`: symmetry `G(x, y) = G(y, x)`.
* `halfSpaceGreenFunction_coordinateReflection`: invariance under simultaneous reflection of both
  arguments in any tangential coordinate.
* `halfSpaceGreenFunction_harmonic`, `halfSpaceGreenFunction_isHarmonicPDE`: for `x ∈ ℝ^n₊`,
  `y ↦ G(x, y)` has zero Laplacian at each `y ∈ ℝ^n₊`, `y ≠ x`, and is classically harmonic (`C²`
  with vanishing Laplacian) on `ℝ^n₊ \ {x}`.
* `halfSpaceGreenFunction_boundary`: `G(x, y) = 0` for every `y` on the boundary hyperplane and
  every pole `x`.

## How it works

Evans notes that the half-space is unbounded, so the calculations for bounded regions do not apply
directly, and in step 1 of the proof of Theorem 14 he uses the symmetry `G(x, y) = G(y, x)` without
a separate check. We check it directly: reflection is an isometric involution, so
`‖y - x̃‖ = ‖x - ỹ‖`, and `Φ` depends only on the norm
(`PotentialTheory.fundamentalSolution_eq_of_norm_eq`). The same norm identity at `yₙ = 0` gives the
boundary values. Harmonicity off the pole is the harmonicity of `Φ` away from the origin, applied to
both terms; the image pole `x̃` has negative last coordinate, so it never lies in `ℝ^n₊`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(b), the reflection in the plane `∂ℝ^n₊` and the
  corrector `Φ(y - x̃)`, p. 36, the definition of Green's function for the half-space, p. 37, and
  step 1 of the proof of Theorem 14 (Poisson's formula for half-space), p. 38.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

namespace GreenFunction

open Set
open SobolevSpace


/-! ## Green's function for the half-space

The geometry is `SobolevSpace.HalfSpace`, the upper half-space `{x | xₙ > 0}` of `ℝ^n` used in
Evans's §2.2.4(b).
-/

/-- Green's function for the half-space, `G(x, y) = Φ(y - x) - Φ(y - x̃)`, where `x̃` is the
reflection of `x` in the boundary hyperplane. The first argument is the pole (or source point)
and the second the field point; `halfSpaceGreenFunction_comm` shows that the kernel is
symmetric. -/
noncomputable def halfSpaceGreenFunction {n : ℕ} [Fact (0 < n)] (x y : ℝ^n) :
  ℝ :=
  PotentialTheory.fundamentalSolution n (y - x) -
    PotentialTheory.fundamentalSolution n (y - HalfSpace.reflect n x)

section HalfSpaceProofs

variable {n : ℕ}

variable [Fact (0 < n)]

/-- The method-of-images Green kernel is symmetric in its source and field
points. -/
theorem halfSpaceGreenFunction_comm (x y : ℝ^n) :
    halfSpaceGreenFunction (n := n) x y =
      halfSpaceGreenFunction (n := n) y x := by
  have himageNorm : ‖y - HalfSpace.reflect n x‖ = ‖x - HalfSpace.reflect n y‖ := by
    rw [← HalfSpace.norm_reflect (n := n), HalfSpace.reflect_sub, HalfSpace.reflect_involutive,
      norm_sub_rev]
  rw [halfSpaceGreenFunction, halfSpaceGreenFunction,
    PotentialTheory.fundamentalSolution_eq_of_norm_eq (norm_sub_rev y x),
    PotentialTheory.fundamentalSolution_eq_of_norm_eq himageNorm]

/-- Reflecting both arguments in a tangential coordinate leaves the
half-space Green kernel unchanged. -/
theorem halfSpaceGreenFunction_coordinateReflection
    {i : Fin n} (hi : i ≠ PDE.Common.lastIndex (n := n)) (x y : ℝ^n) :
    halfSpaceGreenFunction (n := n) (PDE.Common.coordinateReflection i x)
        (PDE.Common.coordinateReflection i y) =
      halfSpaceGreenFunction (n := n) x y := by
  rw [halfSpaceGreenFunction, halfSpaceGreenFunction, ← PDE.Common.coordinateReflection_sub,
    ← HalfSpace.coordinateReflection_reflect_comm n hi, ← PDE.Common.coordinateReflection_sub,
    PotentialTheory.fundamentalSolution_coordinateReflection,
    PotentialTheory.fundamentalSolution_coordinateReflection]

omit [Fact (0 < n)] in
/-- A translated fundamental solution is `C²` away from its pole. -/
private theorem contDiffAt_fundamentalSolution_sub_const {a y : ℝ^n} (h : y ≠ a) :
    ContDiffAt ℝ 2 (fun z ↦ PotentialTheory.fundamentalSolution n (z - a)) y :=
  ((PotentialTheory.contDiffAt_fundamentalSolution n (y - a) (sub_ne_zero.mpr h)).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp y (contDiffAt_id.sub contDiffAt_const)

/-- For a pole `x` in the half-space, `y ↦ G(x, y)` has zero Laplacian at every point `y ≠ x` of
the half-space. -/
theorem halfSpaceGreenFunction_harmonic
    {x y : ℝ^n}
    (hx : x ∈ HalfSpace.upper n) (hy : y ∈ HalfSpace.upper n) (hxy : y ≠ x) :
    laplacian (n := n) (fun z ↦ halfSpaceGreenFunction (n := n) x z) y = 0 := by
  have hne := HalfSpace.ne_reflect_of_mem_upper n hx hy
  have hlap (a : ℝ^n) (ha : y ≠ a) :
      laplacian (fun z ↦ PotentialTheory.fundamentalSolution n (z - a)) y = 0 := by
    rw [PDE.laplacian_comp_sub_right _ a y ((PotentialTheory.contDiffAt_fundamentalSolution n
      (y - a) (sub_ne_zero.mpr ha)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
    exact PotentialTheory.laplacian_fundamentalSolution_eq_zero n (y - a) (sub_ne_zero.mpr ha)
  exact (PDE.laplacian_sub _ _ y (contDiffAt_fundamentalSolution_sub_const hxy)
    (contDiffAt_fundamentalSolution_sub_const hne)).trans (by rw [hlap x hxy, hlap _ hne, sub_self])

/-- For a pole `x` in the half-space, `y ↦ G(x, y)` is classically harmonic (`C²` with zero
Laplacian, as `IsHarmonicPDE` records) on the half-space punctured at `x`; the pointwise
Laplacian is `halfSpaceGreenFunction_harmonic`.

The image pole `HalfSpace.reflect n x` needs no puncture: `x` has positive last coordinate, so
its reflection lies outside the upper half-space. -/
theorem halfSpaceGreenFunction_isHarmonicPDE
    {x : ℝ^n} (hx : x ∈ HalfSpace.upper n) :
    LaplacianEquation.IsHarmonicPDE n (fun y ↦ halfSpaceGreenFunction (n := n) x y)
      (HalfSpace.upper n \ {x}) := by
  apply LaplacianEquation.IsHarmonicPDE.mk
  · intro y hy
    exact ((contDiffAt_fundamentalSolution_sub_const (by simpa using hy.2)).sub
      (contDiffAt_fundamentalSolution_sub_const
        (HalfSpace.ne_reflect_of_mem_upper n hx hy.1))).contDiffWithinAt
  · intro y hy
    exact halfSpaceGreenFunction_harmonic (n := n) hx hy.1 (by simpa using hy.2)

/-- On the boundary hyperplane, the half-space Green function vanishes.

The cancellation holds for every pole `x`; membership of `x` in the upper half-space is needed
for interior harmonicity, but not for this boundary identity. -/
theorem halfSpaceGreenFunction_boundary
    {x y : ℝ^n} (hy : y ∈ HalfSpace.boundary n) :
    halfSpaceGreenFunction (n := n) x y = 0 := by
  rw [halfSpaceGreenFunction, PotentialTheory.fundamentalSolution_eq_of_norm_eq
    (HalfSpace.norm_sub_reflect_eq_of_mem_boundary n x hy).symm, sub_self]

end HalfSpaceProofs

end GreenFunction
