/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Operators
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import PDE.FDeriv.Calculus
import PDE.Representations.Similarity.Dynamic

/-!
# Dynamic affine similarity pullbacks

The dynamic-rescaling calculus of `Similarity.Dynamic`, extended from a pure
dilation to a dilation followed by a translation:

```text
X(x,τ) = L(τ)x + b(τ),
F̃(x,τ) = A(τ) F(X(x,τ), t(τ)).
```

The translation lets the center of a modulated profile move, as the axial center `z̊_c(t)`
does in the dynamic rescaling of Duruisseaux, Ganeshram, George and Anandkumar, Section 3.1.1,
(31)-(37). The theorems keep the four chain-rule contributions separate: amplitude, dilation,
translation, and physical time.

## References

* V. Duruisseaux, A. Ganeshram, R. J. George, and A. Anandkumar, "Stability Framework for the
  Singularity of the Euler Equations on ℝ³", arXiv:2609.10860v1, Section 3.1.1,
  (31)-(37), p. 12.
  <https://arxiv.org/abs/2609.10860v1>
-/

@[expose] public section

namespace PDE.Representations.Similarity


noncomputable section

variable {V E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A spatial dilation followed by a translation. -/
def affineDilation (scale : ℝ) (shift x : V) : V :=
  scale • x + shift

/-- The time-dependent affine similarity point `L(τ)x + b(τ)`. -/
def dynamicAffinePoint
    (spatialScale : ℝ → ℝ) (shift : ℝ → V)
    (x : V) (τ : ℝ) : V :=
  affineDilation (spatialScale τ) (shift τ) x

/-- Pull a time-dependent field back by an amplitude, an affine spatial map,
and a physical-time change. -/
def dynamicAffinePullback
    (field : V → ℝ → E)
    (amplitudeScale spatialScale : ℝ → ℝ)
    (shift : ℝ → V) (physicalTime : ℝ → ℝ)
    (x : V) (τ : ℝ) : E :=
  amplitudeScale τ •
    field (dynamicAffinePoint spatialScale shift x τ) (physicalTime τ)

/-- Derivative of a dynamic affine similarity point. -/
theorem hasDerivAt_dynamicAffinePoint
    (spatialScale : ℝ → ℝ) (shift : ℝ → V)
    (x : V) (τ spatialDerivative : ℝ) (shiftDerivative : V)
    (hspatial : HasDerivAt spatialScale spatialDerivative τ)
    (hshift : HasDerivAt shift shiftDerivative τ) :
    HasDerivAt
      (fun s ↦ dynamicAffinePoint spatialScale shift x s)
      (spatialDerivative • x + shiftDerivative) τ := by
  change
    HasDerivAt ((fun s ↦ spatialScale s • x) + shift)
      (spatialDerivative • x + shiftDerivative) τ
  exact (hspatial.smul_const x).add hshift

/-- Chain rule for a dynamic affine pullback, stated through the joint
Fréchet derivative of the physical field. -/
theorem hasDerivAt_dynamicAffinePullback
    (field : V → ℝ → E)
    (amplitudeScale spatialScale : ℝ → ℝ)
    (shift : ℝ → V) (physicalTime : ℝ → ℝ)
    (x : V) (τ amplitudeDerivative spatialDerivative timeDerivative : ℝ)
    (shiftDerivative : V)
    (hfield : DifferentiableAt ℝ (Function.uncurry field)
      (dynamicAffinePoint spatialScale shift x τ, physicalTime τ))
    (hamplitude :
      HasDerivAt amplitudeScale amplitudeDerivative τ)
    (hspatial :
      HasDerivAt spatialScale spatialDerivative τ)
    (hshift :
      HasDerivAt shift shiftDerivative τ)
    (htime :
      HasDerivAt physicalTime timeDerivative τ) :
    HasDerivAt
      (fun s ↦ dynamicAffinePullback field amplitudeScale spatialScale
        shift physicalTime x s)
      (amplitudeScale τ •
          fderiv ℝ (Function.uncurry field)
            (dynamicAffinePoint spatialScale shift x τ, physicalTime τ)
            (spatialDerivative • x + shiftDerivative, timeDerivative) +
        amplitudeDerivative •
          field (dynamicAffinePoint spatialScale shift x τ)
            (physicalTime τ))
      τ := by
  have hpath :
      HasDerivAt
        (fun s ↦
          (dynamicAffinePoint spatialScale shift x s, physicalTime s))
        (spatialDerivative • x + shiftDerivative, timeDerivative) τ :=
    (hasDerivAt_dynamicAffinePoint spatialScale shift x τ
      spatialDerivative shiftDerivative hspatial hshift).prodMk htime
  have hcomp :=
    hfield.hasFDerivAt.comp_hasDerivAt τ hpath
  change
    HasDerivAt
      (fun s ↦ amplitudeScale s •
        (Function.uncurry field)
          (dynamicAffinePoint spatialScale shift x s, physicalTime s))
      _ τ
  exact hamplitude.smul hcomp

/-- Expanded dynamic-affine chain rule with separate spatial and temporal
slice derivatives. -/
theorem hasDerivAt_dynamicAffinePullback_expanded
    (field : V → ℝ → E)
    (amplitudeScale spatialScale : ℝ → ℝ)
    (shift : ℝ → V) (physicalTime : ℝ → ℝ)
    (x : V) (τ amplitudeDerivative spatialDerivative timeDerivative : ℝ)
    (shiftDerivative : V)
    (hfield : DifferentiableAt ℝ (Function.uncurry field)
      (dynamicAffinePoint spatialScale shift x τ, physicalTime τ))
    (hamplitude :
      HasDerivAt amplitudeScale amplitudeDerivative τ)
    (hspatial :
      HasDerivAt spatialScale spatialDerivative τ)
    (hshift :
      HasDerivAt shift shiftDerivative τ)
    (htime :
      HasDerivAt physicalTime timeDerivative τ) :
    HasDerivAt
      (fun s ↦ dynamicAffinePullback field amplitudeScale spatialScale
        shift physicalTime x s)
      (amplitudeScale τ •
          (fderiv ℝ
              (fun y ↦ field y (physicalTime τ))
              (dynamicAffinePoint spatialScale shift x τ)
              (spatialDerivative • x + shiftDerivative) +
            timeDerivative •
              deriv
                (field (dynamicAffinePoint spatialScale shift x τ))
                (physicalTime τ)) +
        amplitudeDerivative •
          field (dynamicAffinePoint spatialScale shift x τ)
            (physicalTime τ))
      τ := by
  apply
    (hasDerivAt_dynamicAffinePullback field amplitudeScale spatialScale
      shift physicalTime x τ amplitudeDerivative spatialDerivative
      timeDerivative shiftDerivative hfield hamplitude hspatial hshift
      htime).congr_deriv
  rw [fderiv_uncurry_apply_prod field
    (dynamicAffinePoint spatialScale shift x τ)
    (spatialDerivative • x + shiftDerivative)
    (physicalTime τ) timeDerivative hfield]

/-- The derivative of a fixed affine dilation is `scale` times the identity. -/
theorem hasFDerivAt_affineDilation
    {n : ℕ} (scale : ℝ) (shift x : ℝ^n) :
    HasFDerivAt (affineDilation scale shift)
      (scale • ContinuousLinearMap.id ℝ (ℝ^n)) x := by
  convert
    ((ContinuousLinearMap.id ℝ (ℝ^n)).hasFDerivAt.const_smul scale).add_const
      shift using 1
  rfl

/-- A fixed affine dilation is smooth to every order. -/
@[fun_prop]
theorem contDiff_affineDilation
    {n : ℕ} {k : WithTop ℕ∞} (scale : ℝ) (shift : ℝ^n) :
    ContDiff ℝ k (affineDilation scale shift) := by
  unfold affineDilation
  fun_prop

/-- Coordinate `j` of an affine dilation has derivative
`scale δᵢⱼ` in direction `i`. -/
theorem partialDeriv_affineDilation_apply
    {n : ℕ} (scale : ℝ) (shift x : ℝ^n) (i j : Fin n) :
    (∂[i] (fun y ↦ affineDilation scale shift y j)) x =
      scale * if i = j then 1 else 0 := by
  rw [← partialDeriv_apply i j
    (hasFDerivAt_affineDilation scale shift x).differentiableAt]
  rw [partialDeriv, (hasFDerivAt_affineDilation scale shift x).fderiv]
  simp [eq_comm]

/-- Pullback by a fixed affine dilation multiplies every first coordinate
derivative by the spatial scale. -/
theorem partialDeriv_comp_affineDilation
    {n : ℕ} (i : Fin n) (profile : ℝ^n → ℝ)
    (scale : ℝ) (shift x : ℝ^n)
    (hprofile :
      DifferentiableAt ℝ profile (affineDilation scale shift x)) :
    (∂[i]
        (fun y ↦ profile (affineDilation scale shift y))) x =
      scale * (∂[i] profile) (affineDilation scale shift x) := by
  rw [partialDeriv_comp i profile (affineDilation scale shift) x hprofile
    (hasFDerivAt_affineDilation scale shift x).differentiableAt]
  simp [partialDeriv_affineDilation_apply, mul_comm]

/-- A constant amplitude and an affine spatial pullback contribute one
amplitude factor and one spatial-scale factor to a first derivative. -/
theorem partialDeriv_const_mul_comp_affineDilation
    {n : ℕ} (i : Fin n) (profile : ℝ^n → ℝ)
    (amplitude scale : ℝ) (shift x : ℝ^n)
    (hprofile :
      DifferentiableAt ℝ profile (affineDilation scale shift x)) :
    (∂[i]
        (fun y ↦ amplitude *
          profile (affineDilation scale shift y))) x =
      amplitude * scale *
        (∂[i] profile) (affineDilation scale shift x) := by
  rw [show
      (fun y ↦ amplitude * profile (affineDilation scale shift y)) =
        fun y ↦ amplitude • profile (affineDilation scale shift y) by
    funext y
    simp [smul_eq_mul]]
  rw [partialDeriv_const_smul]
  simp only [smul_eq_mul]
  rw [partialDeriv_comp_affineDilation i profile scale shift x hprofile]
  ring

/-- The second coordinate derivatives of an affine dilation vanish. -/
theorem partialDeriv_partialDeriv_affineDilation_apply
    {n : ℕ} (scale : ℝ) (shift x : ℝ^n) (i k j : Fin n) :
    (∂[i]
        (fun y ↦ (∂[k]
          (fun z ↦ affineDilation scale shift z j)) y)) x = 0 := by
  rw [show
      (fun y ↦ (∂[k]
        (fun z ↦ affineDilation scale shift z j)) y) =
        fun _ ↦ scale * if k = j then 1 else 0 by
    funext y
    exact partialDeriv_affineDilation_apply scale shift y k j]
  simp

/-- Pullback by a fixed affine dilation multiplies every second coordinate
derivative by the square of the spatial scale. -/
theorem partialDeriv_partialDeriv_comp_affineDilation
    {n : ℕ} (i k : Fin n) (profile : ℝ^n → ℝ)
    (scale : ℝ) (shift x : ℝ^n)
    (hprofile : ContDiff ℝ 2 profile) :
    (∂[i]
        (fun y ↦ (∂[k]
          (fun z ↦ profile (affineDilation scale shift z))) y)) x =
      scale ^ 2 *
        (∂[i] (fun y ↦ (∂[k] profile) y))
          (affineDilation scale shift x) := by
  rw [partialDeriv_partialDeriv_comp i k profile
    (affineDilation scale shift) x hprofile
    (contDiff_affineDilation scale shift)]
  simp [partialDeriv_affineDilation_apply, pow_two]
  ring

/-- A constant amplitude and an affine spatial pullback contribute one
amplitude factor and two spatial-scale factors to a second derivative. -/
theorem partialDeriv_partialDeriv_const_mul_comp_affineDilation
    {n : ℕ} (i k : Fin n) (profile : ℝ^n → ℝ)
    (amplitude scale : ℝ) (shift x : ℝ^n)
    (hprofile : ContDiff ℝ 2 profile) :
    (∂[i]
        (fun y ↦ (∂[k]
          (fun z ↦ amplitude *
            profile (affineDilation scale shift z))) y)) x =
      amplitude * scale ^ 2 *
        (∂[i] (fun y ↦ (∂[k] profile) y))
          (affineDilation scale shift x) := by
  rw [show
      (fun y ↦ (∂[k]
        (fun z ↦ amplitude * profile (affineDilation scale shift z))) y) =
        fun y ↦ amplitude •
          (∂[k]
            (fun z ↦ profile (affineDilation scale shift z))) y by
    funext y
    rw [← partialDeriv_const_smul]
    rfl]
  rw [partialDeriv_const_smul]
  simp only [smul_eq_mul]
  rw [partialDeriv_partialDeriv_comp_affineDilation
    i k profile scale shift x hprofile]
  ring

/-- Advection of two fields pulled back by the same affine dilation gains the
product of their amplitudes and one spatial-scale factor. -/
theorem advectiveDerivative_smul_comp_affineDilation
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (advecting : ℝ^n → ℝ^n) (transported : ℝ^n → E)
    (advectingAmplitude transportedAmplitude scale : ℝ)
    (shift x : ℝ^n)
    (htransported :
      DifferentiableAt ℝ transported (affineDilation scale shift x)) :
    advectiveDerivative
        (fun y ↦ advectingAmplitude •
          advecting (affineDilation scale shift y))
        (fun y ↦ transportedAmplitude •
          transported (affineDilation scale shift y)) x =
      (advectingAmplitude * transportedAmplitude * scale) •
        advectiveDerivative advecting transported
          (affineDilation scale shift x) := by
  have hcomp :=
    htransported.hasFDerivAt.comp x
      (hasFDerivAt_affineDilation scale shift x)
  have hscaled := hcomp.const_smul transportedAmplitude
  unfold advectiveDerivative
  change
    (fderiv ℝ
      (transportedAmplitude • transported ∘ affineDilation scale shift) x)
        (advectingAmplitude • advecting (affineDilation scale shift x)) =
      _
  rw [hscaled.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, map_smul, smul_smul]
  simp [mul_assoc]

end

end PDE.Representations.Similarity
