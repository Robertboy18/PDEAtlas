/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Dynamic rescaling pullbacks

Dynamic rescaling studies a possibly singular solution `F(x, t)` of an evolution equation
through the rescaled field

```text
F̃(x, τ) = A(τ) F(L(τ) x, t(τ)),
```

in which the amplitude `A`, the spatial dilation `L`, and the physical time `t` are all
functions of a new time `τ`. A self-similar blowup of `F` corresponds to a stationary or
slowly varying `F̃`, and the singularity is absorbed into `A`, `L`, and `t`.

The calculus here does not depend on the equation. Differentiating `F̃` in `τ` by the
chain rule produces three terms: the amplitude term `A'(τ) F`, the dilation term
`A(τ) L'(τ) (x · ∇F)`, and the physical-time term `A(τ) t'(τ) ∂ₜF`. The theorems keep the
three contributions separate so that a model can substitute its own ODEs for `A`, `L`, `t`.

## Main results

* `dynamicPullback`: the rescaled field `F̃`.
* `fderiv_uncurry_apply_prod`: the joint Fréchet derivative of `(x, t) ↦ F(x, t)` splits into
  the spatial slice derivative and the time slice derivative.
* `hasDerivAt_dynamicPullback`, `hasDerivAt_dynamicPullback_expanded`: the `τ`-derivative of
  `F̃`, first in terms of the joint derivative of `F` and then with the three contributions
  written out.
* `advectiveDerivative_smul_id_dynamicPullback`: the dilation term as the advective derivative
  of `F̃(·, τ)` along the field `x ↦ rate · x`, with the factor `A(τ) L(τ)` made explicit.

## Implementation notes

The field is only assumed differentiable at the one point `(L(τ) x, t(τ))` where the chain
rule is applied, and the scaling functions are only assumed differentiable at `τ`.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Section 2.1,
  (2.4)-(2.6), for the dynamic rescaling formulation.
  <https://arxiv.org/abs/2210.07191v4>
* V. Duruisseaux, A. Ganeshram, R. J. George, and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v1, Section 3.1.1,
  (31)-(34), p. 12, for the amplitude, dilation, and time change: `A = 1 / sᵤ`, `L = sᵣ`, and
  `t(τ)` is physical time as a function of rescaled time.
  <https://arxiv.org/abs/2609.10860v1>
-/

@[expose] public section

namespace PDE.Representations.Similarity


noncomputable section

variable {V E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pull a time-dependent field back by an amplitude, a spatial dilation,
and a physical-time change. -/
def dynamicPullback
    (field : V → ℝ → E)
    (amplitudeScale spatialScale physicalTime : ℝ → ℝ)
    (x : V) (τ : ℝ) : E :=
  amplitudeScale τ • field (spatialScale τ • x) (physicalTime τ)

/-- Split the derivative of a jointly differentiable field into its spatial
and temporal slice derivatives. -/
theorem fderiv_uncurry_apply_prod
    (field : V → ℝ → E) (x v : V) (t s : ℝ)
    (hfield : DifferentiableAt ℝ (Function.uncurry field) (x, t)) :
    fderiv ℝ (Function.uncurry field) (x, t) (v, s) =
      fderiv ℝ (fun y ↦ field y t) x v +
        s • deriv (field x) t := by
  have hspaceComp :
      fderiv ℝ (fun y ↦ field y t) x =
        (fderiv ℝ (Function.uncurry field) (x, t)).comp
          (ContinuousLinearMap.inl ℝ V ℝ) := by
    have hcomp := (hfield.hasFDerivAt.comp x
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)).fderiv
    have hfun :
        Function.uncurry field ∘ (fun y : V ↦ (y, t)) =
          fun y ↦ field y t := by
      rfl
    rw [hfun] at hcomp
    exact hcomp
  have hspace :
      fderiv ℝ (Function.uncurry field) (x, t) (v, 0) =
        fderiv ℝ (fun y ↦ field y t) x v := by
    have happly := congrArg (fun L : V →L[ℝ] E ↦ L v) hspaceComp
    simpa [ContinuousLinearMap.comp_apply] using happly.symm
  have htimeComp :
      fderiv ℝ (field x) t =
        (fderiv ℝ (Function.uncurry field) (x, t)).comp
          (ContinuousLinearMap.inr ℝ V ℝ) := by
    have hcomp := (hfield.hasFDerivAt.comp t
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t)).fderiv
    have hfun :
        Function.uncurry field ∘ (fun s : ℝ ↦ (x, s)) =
          field x := by
      rfl
    rw [hfun] at hcomp
    exact hcomp
  have htime :
      fderiv ℝ (Function.uncurry field) (x, t) (0, s) =
        s • deriv (field x) t := by
    have happly := congrArg (fun L : ℝ →L[ℝ] E ↦ L s) htimeComp
    simpa [ContinuousLinearMap.comp_apply, fderiv_eq_smul_deriv] using
      happly.symm
  calc
    fderiv ℝ (Function.uncurry field) (x, t) (v, s) =
        fderiv ℝ (Function.uncurry field) (x, t)
          ((v, 0) + (0, s)) := by
      rw [show (v, s) = (v, 0) + (0, s) by simp]
    _ =
        fderiv ℝ (Function.uncurry field) (x, t) (v, 0) +
          fderiv ℝ (Function.uncurry field) (x, t) (0, s) := by
      rw [map_add]
    _ = _ := by rw [hspace, htime]

/-- Chain rule for a dynamic pullback, stated directly in terms of the joint
Fréchet derivative of the original field. -/
theorem hasDerivAt_dynamicPullback
    (field : V → ℝ → E)
    (amplitudeScale spatialScale physicalTime : ℝ → ℝ)
    (x : V) (τ amplitudeDerivative spatialDerivative timeDerivative : ℝ)
    (hfield : DifferentiableAt ℝ (Function.uncurry field)
      (spatialScale τ • x, physicalTime τ))
    (hamplitude :
      HasDerivAt amplitudeScale amplitudeDerivative τ)
    (hspatial :
      HasDerivAt spatialScale spatialDerivative τ)
    (htime :
      HasDerivAt physicalTime timeDerivative τ) :
    HasDerivAt
      (fun s ↦ dynamicPullback field amplitudeScale spatialScale
        physicalTime x s)
      (amplitudeScale τ •
          fderiv ℝ (Function.uncurry field)
            (spatialScale τ • x, physicalTime τ)
            (spatialDerivative • x, timeDerivative) +
        amplitudeDerivative •
          field (spatialScale τ • x) (physicalTime τ))
      τ := by
  have hpath :
      HasDerivAt
        (fun s ↦ (spatialScale s • x, physicalTime s))
        (spatialDerivative • x, timeDerivative) τ :=
    (hspatial.smul_const x).prodMk htime
  have hcomp :=
    hfield.hasFDerivAt.comp_hasDerivAt τ hpath
  change
    HasDerivAt
      (fun s ↦ amplitudeScale s •
        (Function.uncurry field)
          (spatialScale s • x, physicalTime s))
      _ τ
  exact hamplitude.smul hcomp

/-- Expanded dynamic-pullback derivative, with separate amplitude, spatial,
and physical-time contributions. -/
theorem hasDerivAt_dynamicPullback_expanded
    (field : V → ℝ → E)
    (amplitudeScale spatialScale physicalTime : ℝ → ℝ)
    (x : V) (τ amplitudeDerivative spatialDerivative timeDerivative : ℝ)
    (hfield : DifferentiableAt ℝ (Function.uncurry field)
      (spatialScale τ • x, physicalTime τ))
    (hamplitude :
      HasDerivAt amplitudeScale amplitudeDerivative τ)
    (hspatial :
      HasDerivAt spatialScale spatialDerivative τ)
    (htime :
      HasDerivAt physicalTime timeDerivative τ) :
    HasDerivAt
      (fun s ↦ dynamicPullback field amplitudeScale spatialScale
        physicalTime x s)
      (amplitudeScale τ •
          (spatialDerivative •
              fderiv ℝ
                (fun y ↦ field y (physicalTime τ))
                (spatialScale τ • x) x +
            timeDerivative •
              deriv (field (spatialScale τ • x)) (physicalTime τ)) +
        amplitudeDerivative •
          field (spatialScale τ • x) (physicalTime τ))
      τ := by
  apply
    (hasDerivAt_dynamicPullback field amplitudeScale spatialScale
      physicalTime x τ amplitudeDerivative spatialDerivative
      timeDerivative hfield hamplitude hspatial htime).congr_deriv
  rw [fderiv_uncurry_apply_prod field
    (spatialScale τ • x) (spatialDerivative • x)
    (physicalTime τ) timeDerivative hfield]
  rw [map_smul]

/-- Advection by the dilation field `rate · x` of a fixed-time dynamic
pullback. -/
theorem advectiveDerivative_smul_id_dynamicPullback
    {n : ℕ}
    (field : ℝ^n → ℝ → E)
    (amplitudeScale spatialScale physicalTime : ℝ → ℝ)
    (rate : ℝ) (x : ℝ^n) (τ : ℝ)
    (hfield : DifferentiableAt ℝ
      (fun y ↦ field y (physicalTime τ)) (spatialScale τ • x)) :
    advectiveDerivative
        (fun y ↦ rate • y)
        (fun y ↦ dynamicPullback field amplitudeScale spatialScale
          physicalTime y τ) x =
      (rate * amplitudeScale τ * spatialScale τ) •
        fderiv ℝ (fun y ↦ field y (physicalTime τ))
          (spatialScale τ • x) x := by
  have hmap :
      HasFDerivAt (fun y : ℝ^n ↦ spatialScale τ • y)
        (spatialScale τ • ContinuousLinearMap.id ℝ (ℝ^n)) x := by
    fun_prop
  have hcomp :=
    hfield.hasFDerivAt.comp x hmap
  have hscaled := hcomp.const_smul (amplitudeScale τ)
  unfold advectiveDerivative dynamicPullback
  change
    fderiv ℝ
        (fun y ↦ amplitudeScale τ •
          field (spatialScale τ • y) (physicalTime τ)) x
        (rate • x) =
      _
  rw [show
      (fun y ↦ amplitudeScale τ •
        field (spatialScale τ • y) (physicalTime τ)) =
        amplitudeScale τ •
          ((fun y ↦ field y (physicalTime τ)) ∘
            fun y ↦ spatialScale τ • y) by
    rfl]
  rw [hscaled.fderiv]
  simp only [ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.id_apply,
    map_smul]
  rw [smul_smul, smul_smul]

end

end PDE.Representations.Similarity
