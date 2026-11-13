/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import
  PDE.Hyperbolic.FirstOrder.NonlinearFirstOrder.LocalExistence.AutomaticCharacteristicFlow

/-!
# Automatic inverse coordinates for nonlinear characteristics

We identify the initial derivative of the spatial characteristic
parametrization from its boundary trace and characteristic ODE. Evans's
noncharacteristic condition then makes this derivative invertible, so the
inverse function theorem supplies local characteristic coordinates, as in Lemma 2 of Evans,
§3.2.4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §3.2.3, equation (36); §3.2.4, Lemma 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (SpaceTime)

namespace NonlinearFirstOrder

noncomputable section

open scoped NNReal RealInnerProductSpace Topology
open Set

variable {k : ℕ}

/-- The derivative of the spatial characteristic parametrization at time
zero is forced by the initial trace and Evans's characteristic ODE.

In particular, the first derivative and its invertibility are not
hypotheses. The only regularity hypothesis is `C¹` dependence of the ODE family on `(y,s)`, the
smooth-dependence theorem for ordinary differential equations. -/
theorem hasFDerivAt_characteristicPosition_initial (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ) (initialGradient : ℝ^k → SpaceTime k)
    (curve : (ℝ^k × ℝ) → (SpaceTime k × (ℝ × SpaceTime k))) (y0 : ℝ^k)
    (hF : Differentiable ℝ (phaseFunction (n := k + 1) F)) (hcurve : ContDiffAt ℝ 1 curve (y0, 0))
    (hinitial :
      (fun y ↦ curve (y, 0)) =ᶠ[nhds y0] characteristicInitialState boundary data initialGradient)
    (htime : HasDerivAt (fun s ↦ curve (y0, s)) (characteristicVectorField F (curve (y0, 0))) 0) :
    HasFDerivAt (fun ys ↦ (curve ys).2.2)
      (characteristicInitialDerivative F boundary y0 (initialGradient y0) (data y0)) (y0, 0) := by
  let xmap : (ℝ^k × ℝ) → SpaceTime k := fun ys ↦ (curve ys).2.2
  have hxDiff : DifferentiableAt ℝ xmap (y0, 0) :=
    hcurve.differentiableAt (by norm_num) |>.snd.snd
  have hxEventually :
      (fun y : ℝ^k ↦ xmap (y, 0)) =ᶠ[nhds y0] boundary := by
    filter_upwards [hinitial] with y hy
    simpa [xmap, characteristicInitialState] using congrArg (fun q ↦ q.2.2) hy
  have htangent (dy : ℝ^k) : fderiv ℝ xmap (y0, 0) (dy, 0) =
        fderiv ℝ boundary y0 dy := by
    rw [← fderiv_boundary_slice xmap y0 0 hxDiff dy]
    exact congrArg (fun L : ℝ^k →L[ℝ] SpaceTime k ↦ L dy) (hxEventually.fderiv_eq (𝕜 := ℝ))
  have hinitial0 : curve (y0, 0) = characteristicInitialState boundary data initialGradient y0 :=
    hinitial.self_of_nhds
  have htimeEquation := (characteristic_equations_of_hasDerivAt F hF
      (fun s ↦ curve (y0, s)) 0 htime).2.2
  have htime : fderiv ℝ xmap (y0, 0) (0, 1) = momentumGradient (n := k + 1) F
          (initialGradient y0) (data y0) (boundary y0) := by
    rw [← deriv_time_slice xmap y0 0 hxDiff]
    rw [htimeEquation.deriv]
    simp [hinitial0, characteristicInitialState]
  have hmap : fderiv ℝ xmap (y0, 0) = characteristicInitialDerivative F boundary y0
          (initialGradient y0) (data y0) := by
    apply ContinuousLinearMap.ext
    rintro ⟨dy, ds⟩
    have hdecomp :
        (dy, ds) = (dy, (0 : ℝ)) + ds • ((0 : ℝ^k), (1 : ℝ)) := by
      ext <;> simp
    rw [hdecomp]
    simp only [map_add, map_smul, htangent, htime, characteristicInitialDerivative_apply]
    simp
  exact hxDiff.hasFDerivAt.congr_fderiv hmap

/-- A `C¹` characteristic family with the automatic ODE and initial trace
has local spatial coordinates at every noncharacteristic basepoint.

This theorem removes a separately supplied first variation and a separately
supplied invertible Jacobian from the inverse-function step. -/
theorem exists_local_inverse_coords_of_characteristic_family (F : SpaceTime k → ℝ → SpaceTime k → ℝ)
    (boundary : ℝ^k → SpaceTime k) (data : ℝ^k → ℝ) (initialGradient : ℝ^k → SpaceTime k)
    (curve : (ℝ^k × ℝ) → (SpaceTime k × (ℝ × SpaceTime k))) (y0 : ℝ^k)
    (hF : Differentiable ℝ (phaseFunction (n := k + 1) F)) (hcurve : ContDiffAt ℝ 1 curve (y0, 0))
    (hinitial :
      (fun y ↦ curve (y, 0)) =ᶠ[nhds y0] characteristicInitialState boundary data initialGradient)
    (htime : HasDerivAt (fun s ↦ curve (y0, s)) (characteristicVectorField F (curve (y0, 0))) 0)
    (hnonchar : IsNoncharacteristicAt F boundary y0 (initialGradient y0) (data y0)) :
    ∃ V : Set (SpaceTime k), IsOpen V ∧ boundary y0 ∈ V ∧
      ∃ y : SpaceTime k → ℝ^k, ∃ s : SpaceTime k → ℝ,
        ContDiffAt ℝ 1 y (boundary y0) ∧
        ContDiffAt ℝ 1 s (boundary y0) ∧
        (∀ x ∈ V, (curve (y x, s x)).2.2 = x) ∧
        y (boundary y0) = y0 ∧
        s (boundary y0) = 0 := by
  let xmap : (ℝ^k × ℝ) → SpaceTime k := fun ys ↦ (curve ys).2.2
  have hx : ContDiffAt ℝ 1 xmap (y0, 0) :=
    contDiffAt_snd.comp (y0, 0) (contDiffAt_snd.comp (y0, 0) hcurve)
  have hx' : HasFDerivAt xmap (characteristicInitialDerivative F boundary y0
          (initialGradient y0) (data y0)) (y0, 0) :=
    hasFDerivAt_characteristicPosition_initial F boundary data
      initialGradient curve y0 hF hcurve hinitial htime
  have hinitial0 := hinitial.self_of_nhds
  have hx0 : xmap (y0, 0) = boundary y0 := by
    simpa [xmap, characteristicInitialState] using congrArg (fun q ↦ q.2.2) hinitial0
  simpa [xmap, hx0] using exists_local_inverse_coords_of_noncharacteristic
      F boundary y0 (initialGradient y0) (data y0) 0 xmap hx hx' hnonchar

end

end NonlinearFirstOrder
