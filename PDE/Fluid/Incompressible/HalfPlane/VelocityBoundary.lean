/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.VelocityHolder
import PDE.Analysis.Calculus.HalfPlaneHolderDerivative

/-!
# The half-plane velocity is `C^{1,α}` up to the boundary

For a continuous compactly supported vorticity `ω` that is `α`-Hölder (`0 < α < 1`) on the
closed upper half-plane `H̄ = {x₁ ≥ 0}`, each velocity component `uₖ` of
`halfPlaneVelocity ω` is differentiable within `H̄` at every point of `H̄`
(`hasFDerivWithinAt_halfPlaneVelocity`): the interior derivatives are Hölder, so they converge
at boundary points, and a function continuous on the closure of a convex open set whose
derivative converges at a boundary point is differentiable within the closure there
(`PDE.Analysis.hasFDerivWithinAt_closedUpper_of_holder`). The
derivatives within `H̄` are `α`-Hölder on all of `H̄` (`norm_fderivWithin_halfPlaneVelocity_sub_le`,
constant `422/(α(1-α)) · M`), and at interior points they are the ordinary derivatives. The
velocity is Lipschitz on the closed half-plane (`abs_halfPlaneVelocity_sub_le_mul`).

At a boundary point where `ω` does not vanish the velocity is not differentiable in the
ambient sense (`∂₁u₀ = ω` from above, `-ω` across the line for the reflected representative),
so derivatives within `H̄` are the right notion there.

## Main results

* `continuous_halfPlaneVelocity`: the velocity of a continuous compactly supported vorticity is
  continuous on the plane.
* `hasFDerivWithinAt_halfPlaneVelocity`: at every point of `H̄` each velocity component is
  differentiable within `H̄`, with derivative the limit of the interior derivatives.
* `fderivWithin_halfPlaneVelocity_of_mem_upper`: at interior points the derivative within `H̄` is
  the derivative.
* `norm_fderivWithin_halfPlaneVelocity_sub_le`:
  `‖D^H uₖ(x) - D^H uₖ(x')‖ ≤ 422/(α(1-α)) · M |x - x'|^α` on `H̄`.
* `norm_fderivWithin_halfPlaneVelocity_le_log`: with `|ω| ≤ B` on `H̄` and `L = ∫_{ℝ²₊} |ω|`,
  `‖D^H uₖ(x)‖ ≤ 2((50/α)(1 + B log(2 + M)) + 8B + 10L)` on `H̄`.
* `abs_halfPlaneVelocity_sub_le_mul`: `uₖ` is Lipschitz on `H̄` with the same constant.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology
open GreenFunction PotentialTheory.Planar SobolevSpace

namespace IncompressibleFlow

variable {ω : ℝ^2 → ℝ} {M α : ℝ}

/-- The velocity of a continuous compactly supported vorticity is continuous on the plane. -/
theorem continuous_halfPlaneVelocity (hω : Continuous ω) (hc : HasCompactSupport ω) (k : Fin 2) :
    Continuous fun y ↦ halfPlaneVelocity ω y k := by
  have hφ := contDiff_one_halfSpaceGreenPotential hω hc
  have hpart : ∀ i : Fin 2, Continuous (∂[i] (halfSpaceGreenPotential ω)) := fun i ↦
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  match k with
  | 0 =>
    rw [halfPlaneVelocity_zero]
    exact (hpart 1).neg
  | 1 =>
    rw [halfPlaneVelocity_one]
    exact hpart 0

/-- Derivatives within the closed upper half-plane are unique: the coordinate half-space
`{y | 0 ≤ y 1}` of `uniqueDiffOn_coordinateHalfSpace`. -/
theorem uniqueDiffOn_closedUpper : UniqueDiffOn ℝ {y : ℝ^2 | 0 ≤ y 1} :=
  PDE.Analysis.uniqueDiffOn_coordinateHalfSpace 1

section Boundary

variable (hω : Continuous ω) (hc : HasCompactSupport ω) (hα : 0 < α) (hα1 : α < 1)
  (hM : ∀ y z, 0 ≤ y 1 → 0 ≤ z 1 → |ω y - ω z| ≤ M * ‖y - z‖ ^ α)
include hω hc hα hα1 hM

/-- The interior derivatives of a velocity component are Hölder. -/
private theorem norm_fderiv_sub_le (k : Fin 2) {x x' : ℝ^2} (hx : x ∈ HalfSpace.upper 2)
    (hx' : x' ∈ HalfSpace.upper 2) :
    ‖fderiv ℝ (fun y ↦ halfPlaneVelocity ω y k) x - fderiv ℝ (fun y ↦ halfPlaneVelocity ω y k) x'‖ ≤
      422 / (α * (1 - α)) * M * ‖x - x'‖ ^ α := by
  refine (ContinuousLinearMap.norm_le_sum_norm_apply_single _).trans ?_
  have h := fun i ↦ abs_partialDeriv_halfPlaneVelocity_sub_le hω hc hα hα1 hM i k hx hx'
  have e : ∀ i : Fin 2, (fderiv ℝ (fun y ↦ halfPlaneVelocity ω y k) x -
      fderiv ℝ (fun y ↦ halfPlaneVelocity ω y k) x') (EuclideanSpace.single i 1) =
      (∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x - (∂[i] (fun y ↦ halfPlaneVelocity ω y k)) x' :=
    fun i ↦ rfl
  rw [Fin.sum_univ_two, e 0, e 1, Real.norm_eq_abs, Real.norm_eq_abs]
  have e' : 422 / (α * (1 - α)) * M * ‖x - x'‖ ^ α =
      2 * (211 / (α * (1 - α)) * M * ‖x - x'‖ ^ α) := by ring
  linarith [h 0, h 1]

/-- **Differentiability within the closed half-plane.** At every point `x` of the closed upper
half-plane each velocity component is differentiable within it, and its derivative within is
the limit of the interior derivatives. -/
theorem hasFDerivWithinAt_halfPlaneVelocity (k : Fin 2) {x : ℝ^2} (hx : 0 ≤ x 1) :
    HasFDerivWithinAt (fun y ↦ halfPlaneVelocity ω y k)
      (fderivWithin ℝ (fun y ↦ halfPlaneVelocity ω y k) {y : ℝ^2 | 0 ≤ y 1} x)
      {y : ℝ^2 | 0 ≤ y 1} x ∧
    Tendsto (fun y ↦ fderiv ℝ (fun z ↦ halfPlaneVelocity ω z k) y) (𝓝[HalfSpace.upper 2] x)
      (𝓝 (fderivWithin ℝ (fun y ↦ halfPlaneVelocity ω y k) {y : ℝ^2 | 0 ≤ y 1} x)) := by
  exact PDE.Analysis.hasFDerivWithinAt_closedUpper_of_holder hα
    (continuous_halfPlaneVelocity hω hc k).continuousOn
    (fun y hy ↦ (hasFDerivAt_halfPlaneVelocity hω hc hα hα1.le hM k hy).differentiableAt
      |>.differentiableWithinAt)
    (fun y hy y' hy' ↦ norm_fderiv_sub_le hω hc hα hα1 hM k hy hy') hx

omit hω hc hα hα1 hM in
/-- At interior points the derivative within the closed half-plane is the derivative. -/
theorem fderivWithin_halfPlaneVelocity_of_mem_upper (k : Fin 2) {x : ℝ^2}
    (hx : x ∈ HalfSpace.upper 2) :
    fderivWithin ℝ (fun y ↦ halfPlaneVelocity ω y k) {y : ℝ^2 | 0 ≤ y 1} x =
      fderiv ℝ (fun y ↦ halfPlaneVelocity ω y k) x :=
  fderivWithin_of_mem_nhds (Filter.mem_of_superset ((HalfSpace.isOpen_upper 2).mem_nhds hx)
    fun y hy ↦ (le_of_lt (show (0 : ℝ) < y 1 from hy) : (0 : ℝ) ≤ y 1))

/-- **Hölder continuity of the derivative up to the boundary.** For `x, x'` in the closed upper
half-plane, `‖D^H uₖ(x) - D^H uₖ(x')‖ ≤ 422/(α(1-α)) · M |x - x'|^α` for the derivatives within
the closed half-plane. -/
theorem norm_fderivWithin_halfPlaneVelocity_sub_le (k : Fin 2) {x x' : ℝ^2} (hx : 0 ≤ x 1)
    (hx' : 0 ≤ x' 1) :
    ‖fderivWithin ℝ (fun y ↦ halfPlaneVelocity ω y k) {y : ℝ^2 | 0 ≤ y 1} x -
        fderivWithin ℝ (fun y ↦ halfPlaneVelocity ω y k) {y : ℝ^2 | 0 ≤ y 1} x'‖ ≤
      422 / (α * (1 - α)) * M * ‖x - x'‖ ^ α := by
  exact PDE.Analysis.norm_fderivWithin_closedUpper_sub_le_of_holder hα
    (continuous_halfPlaneVelocity hω hc k).continuousOn
    (fun y hy ↦ (hasFDerivAt_halfPlaneVelocity hω hc hα hα1.le hM k hy).differentiableAt
      |>.differentiableWithinAt)
    (fun y hy y' hy' ↦ norm_fderiv_sub_le hω hc hα hα1 hM k hy hy') hx hx'

/-- **Size of the derivative up to the boundary.** With `|ω| ≤ B` on the closed half-plane and
`L = ∫_{ℝ²₊} |ω|`, `‖D^H uₖ(x)‖ ≤ 2((50/α)(1 + B log(2 + M)) + 8B + 10L)` at every point of the
closed half-plane. -/
theorem norm_fderivWithin_halfPlaneVelocity_le_log {B : ℝ} (hB : ∀ y, 0 ≤ y 1 → |ω y| ≤ B)
    (k : Fin 2) {x : ℝ^2} (hx : 0 ≤ x 1) :
    ‖fderivWithin ℝ (fun y ↦ halfPlaneVelocity ω y k) {y : ℝ^2 | 0 ≤ y 1} x‖ ≤
      2 * (50 / α * (1 + B * Real.log (2 + M)) + 8 * B +
        10 * ∫ y in HalfSpace.upper 2, |ω y|) := by
  have hcl : x ∈ closure (HalfSpace.upper 2) := by rw [HalfSpace.closure_upper_two]; exact hx
  have : (𝓝[HalfSpace.upper 2] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hcl
  refine le_of_tendsto (hasFDerivWithinAt_halfPlaneVelocity hω hc hα hα1 hM k hx).2.norm ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  refine (ContinuousLinearMap.norm_le_sum_norm_apply_single _).trans ?_
  have h := fun i ↦ abs_partialDeriv_halfPlaneVelocity_le_log hω hc hα hα1.le hM hB i k hy
  rw [Fin.sum_univ_two]
  change |(∂[(0 : Fin 2)] (fun z ↦ halfPlaneVelocity ω z k)) y| +
    |(∂[(1 : Fin 2)] (fun z ↦ halfPlaneVelocity ω z k)) y| ≤ _
  linarith [h 0, h 1]

/-- **The velocity is Lipschitz on the closed half-plane.** With `|ω| ≤ B` on the closed
half-plane and `L = ∫_{ℝ²₊} |ω|`, for `x, x'` in the closed upper half-plane
`|uₖ(x) - uₖ(x')| ≤ 2((50/α)(1 + B log(2 + M)) + 8B + 10L) |x - x'|`. -/
theorem abs_halfPlaneVelocity_sub_le_mul {B : ℝ} (hB : ∀ y, 0 ≤ y 1 → |ω y| ≤ B) (k : Fin 2)
    {x x' : ℝ^2} (hx : 0 ≤ x 1) (hx' : 0 ≤ x' 1) :
    |halfPlaneVelocity ω x k - halfPlaneVelocity ω x' k| ≤
      2 * (50 / α * (1 + B * Real.log (2 + M)) + 8 * B +
        10 * ∫ y in HalfSpace.upper 2, |ω y|) * ‖x - x'‖ := by
  have hconv : Convex ℝ {y : ℝ^2 | 0 ≤ y 1} :=
    convex_halfSpace_ge (f := fun y : ℝ^2 ↦ y 1) ⟨fun _ _ ↦ by simp, fun _ _ ↦ by simp⟩ 0
  have h := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun y ↦ halfPlaneVelocity ω y k)
    (fun y hy ↦ (hasFDerivWithinAt_halfPlaneVelocity hω hc hα hα1 hM k hy).1)
    (fun y hy ↦ norm_fderivWithin_halfPlaneVelocity_le_log hω hc hα hα1 hM hB k hy) hx' hx
  rwa [Real.norm_eq_abs] at h

end Boundary

end IncompressibleFlow
