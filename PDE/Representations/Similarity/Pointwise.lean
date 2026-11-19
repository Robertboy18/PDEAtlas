/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean

/-!
# Pointwise similarity transformations

Pointwise transformations used in traveling-wave, self-similar, and concentration arguments.
They are plain functions. The files for each equation state the relevant identity on its
domain and prove the reduced equation.

`forwardSelfSimilarAnsatz` scales away from an initial time and `backwardSelfSimilarAnsatz`
concentrates toward a candidate singular time. Both are special cases of `scaledProfileAnsatz`.

These are the ansatzes of Evans, §4.2, in particular the scaling ansatz (28) of §4.2.2,
pp. 185-186.

The spatial and value types are parameters, and the definitions need only subtraction and real
scalar actions, so scalar-, vector-, and complex-valued profiles use the same definitions.
Sobolev and `Lᵖ` elements are equivalence classes rather than pointwise functions, so a
similarity action on those spaces needs a separately constructed pullback.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.2, in particular §4.2.2,
  (28), p. 185.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace PDE.Representations.Similarity

/-- The one-dimensional traveling wave `u(t, x) = f(x - c t)`, represented with time in
coordinate `0` and space in coordinate `1`. -/
def travelingWave1D {E : Type*} (profile : ℝ → E) (speed : ℝ) (xt : ℝ^2) : E :=
  profile (xt 1 - speed * xt 0)

/-- At time zero, a traveling wave agrees with its profile. -/
@[simp]
theorem traveling_wave_1d_zero_time {E : Type*}
    (profile : ℝ → E) (speed x : ℝ) :
    travelingWave1D profile speed !₂[0, x] = profile x := by
  simp [travelingWave1D]

/-- Translate `center` to the origin and scale the resulting displacement by `scale`. -/
def centeredDilation
    {V : Type*} [Sub V] [SMul ℝ V]
    (scale : ℝ) (center x : V) : V :=
  scale • (x - center)

/-- Dilating the inverse-scaled point `center + scale⁻¹ • y` recovers `y`.

This identity supplies the moving spatial point used to transfer growth of a
similarity amplitude into growth of a spatial supremum norm. -/
@[simp]
theorem centered_dilation_center_add_inv_smul
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {scale : ℝ} (hscale : scale ≠ 0) (center y : V) :
    centeredDilation scale center (center + scale⁻¹ • y) = y := by
  simp [centeredDilation, hscale]

/-- The centered coordinate map is surjective when its scale is nonzero. -/
theorem centered_dilation_surjective
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {scale : ℝ} (hscale : scale ≠ 0) (center : V) :
    Function.Surjective (centeredDilation scale center) := by
  intro y
  exact ⟨center + scale⁻¹ • y, centered_dilation_center_add_inv_smul hscale center y⟩

/-- Apply amplitude and spatial scales to a pointwise profile.

This is the transformation behind fixed-exponent self-similarity, modulated profiles, and Type II
concentration. It is a total function; positivity and nonvanishing of the scales are hypotheses
of the theorems about the transformed field. -/
def scaledProfileAnsatz
    {V E : Type*} [Sub V] [SMul ℝ V] [SMul ℝ E]
    (profile : V → E) (amplitudeScale spatialScale : ℝ → ℝ) (center : V)
    (x : V) (t : ℝ) : E :=
  amplitudeScale t • profile (centeredDilation (spatialScale t) center x)

/-- Evaluating a scaled profile at the inverse-dilated point recovers the original profile
coordinate, multiplied only by the amplitude scale. -/
theorem scaled_profile_ansatz_at_inverse_dilation
    {V E : Type*} [AddCommGroup V] [Module ℝ V] [SMul ℝ E]
    (profile : V → E) (amplitudeScale spatialScale : ℝ → ℝ)
    (center y : V) (t : ℝ) (hspatial : spatialScale t ≠ 0) :
    scaledProfileAnsatz profile amplitudeScale spatialScale center
        (center + (spatialScale t)⁻¹ • y) t =
      amplitudeScale t • profile y := by
  simp [scaledProfileAnsatz, hspatial]

/-- The backward power scale `(T - t)^(-α)` associated with singular time `T`.

`Real.rpow` is total on ℝ; the analytic API uses this expression only under `t < T`, where its
base is positive. -/
noncomputable def backwardPowerScale
    (alpha singularTime t : ℝ) : ℝ :=
  (singularTime - t) ^ (-alpha)

/-- The forward self-similar field `t^α • f (t^(-β) • (x - x₀))`.

For arbitrary real exponents, differential identities are stated only at positive times. -/
noncomputable def forwardSelfSimilarAnsatz
    {V E : Type*} [Sub V] [SMul ℝ V] [SMul ℝ E]
    (profile : V → E) (alpha beta : ℝ) (center : V)
    (x : V) (t : ℝ) : E :=
  scaledProfileAnsatz profile
    (fun s ↦ s ^ alpha)
    (fun s ↦ (s ^ beta)⁻¹)
    center x t

/-- The backward self-similar field concentrating at time `T`,
`(T - t)^(-α) • f ((T - t)^(-β) • (x - x₀))`.

It is meant for `t < T`; at later times it is just the value of the total `Real.rpow`. -/
noncomputable def backwardSelfSimilarAnsatz
    {V E : Type*} [Sub V] [SMul ℝ V] [SMul ℝ E]
    (profile : V → E) (alpha beta singularTime : ℝ) (center : V)
    (x : V) (t : ℝ) : E :=
  scaledProfileAnsatz profile
    (backwardPowerScale alpha singularTime)
    (backwardPowerScale beta singularTime)
    center x t

/-- A concentration field with a given scale `λ`,
`λ(t)^(-α) • f (λ(t)⁻¹ • (x - x₀))`. -/
noncomputable def concentrationAnsatz
    {V E : Type*} [Sub V] [SMul ℝ V] [SMul ℝ E]
    (profile : V → E) (scale : ℝ → ℝ) (alpha : ℝ) (center : V)
    (x : V) (t : ℝ) : E :=
  scaledProfileAnsatz profile
    (fun s ↦ (scale s) ^ (-alpha))
    (fun s ↦ (scale s)⁻¹)
    center x t

/-- Scaling the zero profile gives the zero field, independently of both scale functions. -/
@[simp]
theorem scaled_profile_ansatz_zero
    {V E : Type*} [Sub V] [SMul ℝ V] [Zero E] [SMulZeroClass ℝ E]
    (amplitudeScale spatialScale : ℝ → ℝ) (center : V) :
    scaledProfileAnsatz (fun _ : V ↦ (0 : E)) amplitudeScale spatialScale center =
      fun _ : V ↦ fun _ : ℝ ↦ (0 : E) := by
  funext x t
  simp [scaledProfileAnsatz]

end PDE.Representations.Similarity
