/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Representations.Similarity.Calculus
public import PDE.Solution.Singularity.FiniteTime.NonlinearHeat.Classical
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Similarity calculus for the nonlinear heat equation

We substitute a general amplitude-scaled profile into

`uₜ = Δu + uᵖ`.

The resulting identities are the substitution algebra behind the Type I and concentration
modules. The general identity has no sign condition or scaling law; those appear only in the
two specializations, where they simplify the real power and the scale coefficients.

The concentration identity is the algebraic input to a Type II modulation analysis.

## Main results

* `equation_residual_scaled_profile_ansatz`: the residual `Δu + uᵖ - uₜ` of the ansatz
  `u = A(t) Q(L(t) (x - x₀))`, for arbitrary differentiable scales `A`, `L` and a `C²` profile
  `Q`.
* `equation_residual_concentration_ansatz`: for `λ(t)^(-α) Q((x - x₀) / λ(t))` with the balance
  law `α p = α + 2`, the residual is `λ^(-(α+2))` times the stationary residual `ΔQ + Qᵖ` plus
  the modulation defect `λ λ' (α Q + y · ∇Q)`.
* `equation_residual_backward_self_similar_ansatz`: for the Giga–Kohn ansatz
  `(T - t)^(-α) Q((T - t)^(-β) (x - x₀))` with `2β = 1` and `α p = α + 1`, the residual is
  `(T - t)^(-(α+1))` times `ΔQ + Qᵖ - (α Q + β y · ∇Q)`, the self-similar profile equation.

## Implementation notes

The real power `uᵖ` is `Real.rpow`, and separating `(A Q)ᵖ = Aᵖ Qᵖ` needs `Q ≥ 0` at the
evaluation point. The two specializations therefore assume `Q ≥ 0` at the similarity
coordinate, and nowhere else.

## References

* Y. Giga and R. V. Kohn, "Asymptotically self-similar blow-up of semilinear heat equations",
  *Comm. Pure Appl. Math.* 38 (1985), 297-319.
  <https://doi.org/10.1002/cpa.3160380304>
* P. Quittner and P. Souplet, *Superlinear Parabolic Problems*, Birkhäuser Advanced Texts,
  Birkhäuser, 2007, chapter "Model Parabolic Problems", pp. 75-250.
  <https://doi.org/10.1007/978-3-7643-8442-5_3>
-/

@[expose] public section

namespace PDE.Solution.Singularity.FiniteTime.NonlinearHeat

open PDE.Representations.Similarity

variable {n : ℕ}

variable (p : ℝ)

/-- Exact nonlinear-heat residual of a profile with arbitrary amplitude and spatial scales. -/
theorem equation_residual_scaled_profile_ansatz
    (profile : ℝ^n → ℝ) (amplitudeScale spatialScale : ℝ → ℝ)
    (center x : ℝ^n) (t : ℝ)
    (hprofile : ContDiff ℝ 2 profile)
    (hamplitude : DifferentiableAt ℝ amplitudeScale t)
    (hspatial : DifferentiableAt ℝ spatialScale t) :
    equationResidual p
        (scaledProfileAnsatz profile amplitudeScale spatialScale center) x t =
      amplitudeScale t * spatialScale t ^ 2 *
          laplacian profile (centeredDilation (spatialScale t) center x) +
        (amplitudeScale t *
          profile (centeredDilation (spatialScale t) center x)) ^ p -
        deriv amplitudeScale t *
          profile (centeredDilation (spatialScale t) center x) -
        amplitudeScale t * deriv spatialScale t *
          ∑ i, (∂[i] profile)
            (centeredDilation (spatialScale t) center x) * (x - center) i := by
  rw [equationResidual]
  rw [laplacian_scaled_profile_ansatz profile amplitudeScale spatialScale center x t]
  rw [deriv_scaled_profile_ansatz profile amplitudeScale spatialScale center x t
    ((hprofile.differentiable (by norm_num)).differentiableAt)
    hamplitude hspatial]
  simp only [scaledProfileAnsatz, smul_eq_mul]
  ring

/-- Exact residual of a concentration ansatz whose amplitude exponent obeys the nonlinear-heat
balance law `alpha * p = alpha + 2`.

The diffusion and reaction terms share the factor `λ(t)^(-(alpha + 2))`. Differentiating the
time-dependent scale contributes the remaining
`λ(t) λ'(t) scalingGenerator alpha 1 profile` term. Thus the uncorrected pure-profile ansatz
solves the parabolic equation only where the stationary residual and modulation defect cancel. -/
theorem equation_residual_concentration_ansatz
    (profile : ℝ^n → ℝ) (scale : ℝ → ℝ) (alpha : ℝ)
    (center x : ℝ^n) (t : ℝ)
    (hprofile : ContDiff ℝ 2 profile)
    (hnonneg :
      0 ≤ profile (centeredDilation (scale t)⁻¹ center x))
    (hscale : DifferentiableAt ℝ scale t)
    (hscale_pos : 0 < scale t)
    (hreaction : alpha * p = alpha + 2) :
    equationResidual p
        (concentrationAnsatz profile scale alpha center) x t =
      scale t ^ (-(alpha + 2)) *
        (laplacian profile (centeredDilation (scale t)⁻¹ center x) +
          profile (centeredDilation (scale t)⁻¹ center x) ^ p +
          scale t * deriv scale t *
            scalingGenerator alpha 1 profile
              (centeredDilation (scale t)⁻¹ center x)) := by
  have hscale_ne : scale t ≠ 0 :=
    ne_of_gt hscale_pos
  have hamplitude :
      DifferentiableAt ℝ (fun s ↦ scale s ^ (-alpha)) t :=
    hscale.rpow_const (p := -alpha) (Or.inl hscale_ne)
  have hspatial :
      DifferentiableAt ℝ (fun s ↦ (scale s)⁻¹) t :=
    hscale.inv hscale_ne
  have hamplitude_deriv :
      deriv (fun s ↦ scale s ^ (-alpha)) t =
        -alpha * deriv scale t * scale t ^ (-alpha - 1) := by
    rw [deriv_rpow_const hscale (p := -alpha) (Or.inl hscale_ne)]
    ring
  have hspatial_deriv :
      deriv (fun s ↦ (scale s)⁻¹) t =
        -deriv scale t * (scale t)⁻¹ ^ 2 := by
    rw [deriv_fun_inv'' hscale hscale_ne]
    simp only [div_eq_mul_inv, inv_pow]
  have hdiffusion_scale :
      scale t ^ (-alpha) * (scale t)⁻¹ ^ 2 =
        scale t ^ (-(alpha + 2)) := by
    calc
      _ = scale t ^ (-alpha) *
          (scale t ^ (-1 : ℝ)) ^ (2 : ℝ) := by
        rw [Real.rpow_two, Real.rpow_neg_one]
      _ = scale t ^ (-alpha) *
          scale t ^ ((-1 : ℝ) * 2) := by
        rw [Real.rpow_mul hscale_pos.le]
      _ = scale t ^ (-alpha + (-1 : ℝ) * 2) :=
        (Real.rpow_add hscale_pos (-alpha) ((-1 : ℝ) * 2)).symm
      _ = _ := by
        congr 1
        ring
  have hreaction_exponent :
      -alpha * p = -(alpha + 2) := by
    calc
      -alpha * p = -(alpha * p) := by ring
      _ = -(alpha + 2) := by rw [hreaction]
  have hreaction_scale :
      (scale t ^ (-alpha) *
          profile (centeredDilation (scale t)⁻¹ center x)) ^ p =
        scale t ^ (-(alpha + 2)) *
          profile (centeredDilation (scale t)⁻¹ center x) ^ p := by
    rw [Real.mul_rpow (Real.rpow_nonneg hscale_pos.le _) hnonneg]
    rw [← Real.rpow_mul hscale_pos.le]
    rw [hreaction_exponent]
  have hamplitude_scale :
      scale t ^ (-alpha - 1) =
        scale t ^ (-(alpha + 2)) * scale t := by
    calc
      _ = scale t ^ (-(alpha + 2) + 1) := by
        congr 1
        ring
      _ = _ := by
        rw [Real.rpow_add hscale_pos, Real.rpow_one]
  have hspatial_scale :
      scale t ^ (-alpha) *
          (-deriv scale t * (scale t)⁻¹ ^ 2) =
        -deriv scale t * scale t ^ (-(alpha + 2)) := by
    calc
      _ = -deriv scale t *
          (scale t ^ (-alpha) * (scale t)⁻¹ ^ 2) := by
        ring
      _ = _ := by rw [hdiffusion_scale]
  have hcoordinate_sum :
      (∑ i, (centeredDilation (scale t)⁻¹ center x) i *
          (∂[i] profile)
            (centeredDilation (scale t)⁻¹ center x)) =
        (scale t)⁻¹ *
          ∑ i, (∂[i] profile)
            (centeredDilation (scale t)⁻¹ center x) *
              (x - center) i := by
    simp only [centeredDilation, PiLp.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold concentrationAnsatz
  rw [equation_residual_scaled_profile_ansatz p profile
    (fun s ↦ scale s ^ (-alpha)) (fun s ↦ (scale s)⁻¹)
    center x t hprofile hamplitude hspatial]
  rw [hamplitude_deriv, hspatial_deriv, hdiffusion_scale,
    hreaction_scale, hamplitude_scale, hspatial_scale]
  unfold scalingGenerator
  rw [hcoordinate_sum]
  simp only [one_mul]
  field_simp [hscale_ne]
  ring

/-- Exact reduction of a backward self-similar ansatz under the two parabolic balance laws.

The relation `2 * beta = 1` aligns the Laplacian with one inverse time scale, while
`alpha * p = alpha + 1` aligns the nonlinear term. The two time-derivative contributions form
`scalingGenerator alpha beta profile`. Nonnegativity is required only at the displayed
similarity coordinate, where `Real.mul_rpow` separates the amplitude and profile factors. -/
theorem equation_residual_backward_self_similar_ansatz
    (profile : ℝ^n → ℝ) (alpha beta : ℝ)
    (singularTime : ℝ) (center x : ℝ^n) (t : ℝ)
    (hprofile : ContDiff ℝ 2 profile)
    (hnonneg :
      0 ≤ profile
        (centeredDilation (backwardPowerScale beta singularTime t) center x))
    (ht : t < singularTime)
    (hdiffusion : 2 * beta = 1)
    (hreaction : alpha * p = alpha + 1) :
    equationResidual p
        (backwardSelfSimilarAnsatz profile alpha beta singularTime center) x t =
      backwardPowerScale (alpha + 1) singularTime t *
        (laplacian profile
            (centeredDilation (backwardPowerScale beta singularTime t) center x) +
          profile
              (centeredDilation (backwardPowerScale beta singularTime t) center x) ^ p -
          scalingGenerator alpha beta profile
            (centeredDilation (backwardPowerScale beta singularTime t) center x)) := by
  have hdiffusionScale :
      backwardPowerScale alpha singularTime t *
          backwardPowerScale beta singularTime t ^ 2 =
        backwardPowerScale (alpha + 1) singularTime t := by
    calc
      _ = backwardPowerScale alpha singularTime t *
          backwardPowerScale (2 * beta) singularTime t := by
        rw [backward_power_scale_sq ht]
      _ = backwardPowerScale (alpha + 2 * beta) singularTime t :=
        backward_power_scale_mul ht
      _ = _ := by rw [hdiffusion]
  have hreactionScale :
      (backwardPowerScale alpha singularTime t *
          profile
            (centeredDilation
              (backwardPowerScale beta singularTime t) center x)) ^ p =
        backwardPowerScale (alpha + 1) singularTime t *
          profile
            (centeredDilation
              (backwardPowerScale beta singularTime t) center x) ^ p := by
    rw [Real.mul_rpow (backward_power_scale_pos ht).le hnonneg]
    rw [backward_power_scale_rpow ht, hreaction]
  unfold equationResidual
  rw [deriv_backward_self_similar_ansatz profile alpha beta singularTime center x t
    (hprofile.differentiable (by norm_num) _) ht]
  unfold backwardSelfSimilarAnsatz
  rw [laplacian_scaled_profile_ansatz profile
    (backwardPowerScale alpha singularTime)
    (backwardPowerScale beta singularTime) center x t]
  simp only [scaledProfileAnsatz, smul_eq_mul]
  rw [hdiffusionScale, hreactionScale]
  ring

end PDE.Solution.Singularity.FiniteTime.NonlinearHeat
