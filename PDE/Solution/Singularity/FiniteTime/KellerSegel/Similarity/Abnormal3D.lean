/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Solution.Singularity.FiniteTime.KellerSegel.Classical
public import PDE.Representations.Similarity.Pointwise
public import PDE.Solution.Singularity.FiniteTime.Norm.SpatialSupremum
import PDE.Representations.Similarity.Calculus
import PDE.Solution.Singularity.FiniteTime.Norm.Similarity
import CAS.ExactTactic
import PDE.FDeriv.Calculus

/-!
# Abnormal three-dimensional Keller–Segel similarity

We formalize the scaling algebra of Liu, Wang and Zhou (arXiv:2504.12231v2), equations (1.8),
(1.12) and (1.13), with zero logistic damping `μ = 0`. The object of study is the uncorrected
leading ansatz.

For modes `j ≥ 4`, the spatial exponent `βⱼ = 1/3 + 1/(2j)` of their second comment on
Theorem 1.1 is below the parabolic exponent `1/2`. The leading profile equation is therefore
diffusion-free, while the full density residual contains diffusion with coefficient
`(T - t)^(1 - 2βⱼ)`.

The results are the exponent algebra and the exact pointwise substitution into both
Keller–Segel equations. A bounded density profile with one nonzero value makes the density
ansatz blow up (`abnormal_density_ansatz_3d_blows_up_at`), whether or not the profile solves
the profile equations. Under the diffusion-free profile equation, the exact density residual
vanishes everywhere at a pre-singular time exactly when the profile is harmonic
(`forall_density_residual_abnormal_ansatz_3d_eq_zero_iff_laplacian_eq_zero`); for `j ≥ 4`
its norm at the center tends to `∞` as `t → T⁻` when `ΔQ(0) ≠ 0`.

As in `KellerSegel.Similarity.Parabolic`, the profiles are pointwise functions because the
formulas use classical derivatives at given coordinates.

## References

* J. Liu, Y. Wang and T. Zhou, "Finite time blowup for Keller-Segel equation with logistic
  damping in three dimensions", arXiv:2504.12231v2, Theorem 1.1 and the comments after it,
  (1.8), (1.12) and (1.13).
  <https://arxiv.org/abs/2504.12231v2>
-/

open scoped Gradient

@[expose] public section

namespace PDE.Solution.Singularity.FiniteTime.KellerSegel

open Filter Topology
open PDE.Representations.Similarity

/-- Spatial scaling exponent of the abnormal three-dimensional Type I family. -/
noncomputable def abnormalBeta3D (j : ℕ) : ℝ :=
  1 / 3 + 1 / (2 * (j : ℝ))

/-- Power multiplying the diffusion perturbation after similarity rescaling. -/
noncomputable def abnormalDiffusionExponent3D (j : ℕ) : ℝ :=
  1 - 2 * abnormalBeta3D j

/-- The diffusion exponent in terms of the mode number. -/
@[simp]
theorem abnormal_diffusion_exponent_3d_eq (j : ℕ) :
    abnormalDiffusionExponent3D j = 1 / 3 - 1 / (j : ℝ) := by
  by_cases hj : (j : ℝ) = 0
  · have : j = 0 := by
      exact_mod_cast hj
    subst j
    norm_num [abnormalDiffusionExponent3D, abnormalBeta3D]
  · rw [abnormalDiffusionExponent3D, abnormalBeta3D]
    cas

/-- The diffusion perturbation exponent `1 - 2βⱼ` is positive for `j ≥ 4`. -/
theorem abnormal_diffusion_exponent_3d_pos {j : ℕ} (hj : 4 ≤ j) :
    0 < abnormalDiffusionExponent3D j := by
  have hj_three : (3 : ℝ) < (j : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 3 < 4) hj)
  have hrecip : (1 : ℝ) / (j : ℝ) < 1 / 3 :=
    one_div_lt_one_div_of_lt (by norm_num) hj_three
  rw [abnormal_diffusion_exponent_3d_eq, sub_pos]
  exact hrecip

/-- For every abnormal mode, the spatial exponent is strictly larger than `1/3`. -/
theorem one_third_lt_abnormal_beta_3d {j : ℕ} (hj : 4 ≤ j) :
    (1 : ℝ) / 3 < abnormalBeta3D j := by
  have hj_pos : 0 < (j : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 4) hj)
  rw [abnormalBeta3D]
  have hcorrection : 0 < (1 : ℝ) / (2 * (j : ℝ)) :=
    div_pos zero_lt_one (mul_pos (by norm_num) hj_pos)
  linarith

/-- The abnormal exponent lies strictly below the parabolic exponent `1/2`. -/
theorem abnormal_beta_3d_lt_half {j : ℕ} (hj : 4 ≤ j) :
    abnormalBeta3D j < 1 / 2 := by
  have h := abnormal_diffusion_exponent_3d_pos hj
  rw [abnormalDiffusionExponent3D] at h
  nlinarith

/-- For every abnormal mode `j ≥ 4`, the coefficient of the diffusion perturbation tends to
zero at the proposed singular time.

This is the analytic content of `βⱼ < 1/2`: diffusion is lower order than aggregation after
rescaling, although it does not vanish identically before the singular time. -/
theorem tendsto_abnormal_diffusion_coefficient_3d
    {j : ℕ} (hj : 4 ≤ j) (singularTime : ℝ) :
    Tendsto
      (fun t ↦ (singularTime - t) ^ abnormalDiffusionExponent3D j)
      (nhdsWithin singularTime (Set.Iio singularTime)) (nhds 0) := by
  have hexponent : 0 < abnormalDiffusionExponent3D j :=
    abnormal_diffusion_exponent_3d_pos hj
  have hbase :
      Tendsto (fun t : ℝ ↦ singularTime - t)
        (nhdsWithin singularTime (Set.Iio singularTime)) (nhds 0) := by
    have hcontinuous :
        ContinuousAt (fun t : ℝ ↦ singularTime - t) singularTime :=
      continuousAt_const.sub continuousAt_id
    simpa using hcontinuous.tendsto.mono_left nhdsWithin_le_nhds
  have hpower :
      Tendsto
        (fun τ : ℝ ↦ τ ^ abnormalDiffusionExponent3D j)
        (nhds 0) (nhds 0) := by
    simpa only [Real.zero_rpow hexponent.ne'] using
      (Real.continuousAt_rpow_const 0 _ (Or.inr hexponent.le)).tendsto
  exact
    (hpower.comp hbase).congr'
      (Eventually.of_forall fun _ ↦ rfl)

/-- The abnormal Type I density ansatz, intended for `t < T`.

The mode restriction `j ≥ 4` is needed for exponent estimates, not for the formula itself.
-/
noncomputable def abnormalDensityAnsatz3D
    (j : ℕ) (profile : ℝ^3 → ℝ) (singularTime : ℝ) (center : ℝ^3)
    (x : ℝ^3) (t : ℝ) : ℝ :=
  backwardSelfSimilarAnsatz profile 1 (abnormalBeta3D j) singularTime center x t

/-- A bounded abnormal density profile with one nonzero value makes its ansatz blow up in spatial
supremum norm at the proposed singular time.

Only the scaling of the density ansatz is used; the profile need not solve the profile
equations. -/
theorem abnormal_density_ansatz_3d_blows_up_at
    (j : ℕ) (profile : ℝ^3 → ℝ) (singularTime : ℝ) (center : ℝ^3)
    (y : ℝ^3) (hy : profile y ≠ 0)
    (hbounded : Bornology.IsBounded (Set.range profile)) :
    SpatialSupNormBlowsUpAt
      (abnormalDensityAnsatz3D j profile singularTime center)
      singularTime := by
  change
    SpatialSupNormBlowsUpAt
      (backwardSelfSimilarAnsatz profile 1 (abnormalBeta3D j)
        singularTime center)
      singularTime
  exact
    backward_self_similar_ansatz_blows_up_at
      profile 1 (abnormalBeta3D j) singularTime center zero_lt_one y hy hbounded

/-- Potential accompanying the abnormal density ansatz.

The amplitude `(T - t)^(2βⱼ - 1)` is forced by `-ΔΦ = Q`: two spatial
derivatives contribute `(T - t)^(-2βⱼ)`, leaving the density factor
`(T - t)⁻¹`.
-/
noncomputable def abnormalPotentialAnsatz3D
    (j : ℕ) (profile : ℝ^3 → ℝ) (singularTime : ℝ) (center : ℝ^3)
    (x : ℝ^3) (t : ℝ) : ℝ :=
  backwardSelfSimilarAnsatz profile (abnormalDiffusionExponent3D j)
    (abnormalBeta3D j) singularTime center x t

/-- Exact scaling of the elliptic potential residual.

Before `T`, substituting the abnormal density and potential ansätze into `-Δc - ρ`
produces `(T - t)⁻¹` times the profile residual at the similarity point.
-/
theorem potential_residual_abnormal_ansatz_3d
    (j : ℕ) (Q Φ : ℝ^3 → ℝ) (singularTime : ℝ) (center x : ℝ^3) (t : ℝ)
    (ht : t < singularTime) :
    potentialResidual
        (fun z ↦ abnormalDensityAnsatz3D j Q singularTime center z t)
        (fun z ↦ abnormalPotentialAnsatz3D j Φ singularTime center z t) x =
      backwardPowerScale 1 singularTime t *
        potentialResidual Q Φ
          (centeredDilation
            (backwardPowerScale (abnormalBeta3D j) singularTime t) center x) := by
  let y :=
    centeredDilation
      (backwardPowerScale (abnormalBeta3D j) singularTime t) center x
  have hscale :
      backwardPowerScale (abnormalDiffusionExponent3D j) singularTime t *
          backwardPowerScale (abnormalBeta3D j) singularTime t ^ 2 =
        backwardPowerScale 1 singularTime t := by
    rw [backward_power_scale_sq ht, backward_power_scale_mul ht]
    congr 1
    simp [abnormalDiffusionExponent3D]
  change
    -laplacian
        (fun z ↦ scaledProfileAnsatz Φ
          (backwardPowerScale (abnormalDiffusionExponent3D j) singularTime)
          (backwardPowerScale (abnormalBeta3D j) singularTime) center z t) x -
        scaledProfileAnsatz Q
          (backwardPowerScale 1 singularTime)
          (backwardPowerScale (abnormalBeta3D j) singularTime) center x t =
      backwardPowerScale 1 singularTime t * (-laplacian Φ y - Q y)
  rw [laplacian_scaled_profile_ansatz Φ
    (backwardPowerScale (abnormalDiffusionExponent3D j) singularTime)
    (backwardPowerScale (abnormalBeta3D j) singularTime) center x t]
  rw [hscale]
  simp only [scaledProfileAnsatz, smul_eq_mul]
  ring

/-- At a fixed pre-singular time, the potential residual of the abnormal ansatz vanishes
everywhere exactly when the elliptic profile residual vanishes everywhere.

Inverse dilation reaches every profile coordinate, so the substitution can be reversed. -/
theorem forall_potential_residual_abnormal_ansatz_3d_eq_zero_iff
    (j : ℕ) (Q Φ : ℝ^3 → ℝ) (singularTime : ℝ) (center : ℝ^3) (t : ℝ)
    (ht : t < singularTime) :
    (∀ x,
      potentialResidual
          (fun z ↦ abnormalDensityAnsatz3D j Q singularTime center z t)
          (fun z ↦ abnormalPotentialAnsatz3D j Φ singularTime center z t) x =
        0) ↔
      ∀ y, potentialResidual Q Φ y = 0 := by
  constructor
  · intro hansatz y
    have hscale :
        backwardPowerScale (abnormalBeta3D j) singularTime t ≠ 0 :=
      (backward_power_scale_pos ht).ne'
    let x :=
      center +
        (backwardPowerScale (abnormalBeta3D j) singularTime t)⁻¹ • y
    have hfactored :
        backwardPowerScale 1 singularTime t *
            potentialResidual Q Φ
              (centeredDilation
                (backwardPowerScale (abnormalBeta3D j) singularTime t) center x) =
          0 := by
      rw [← potential_residual_abnormal_ansatz_3d
        j Q Φ singularTime center x t ht]
      exact hansatz x
    have hprofile :
        potentialResidual Q Φ
            (centeredDilation
              (backwardPowerScale (abnormalBeta3D j) singularTime t) center x) =
          0 :=
      (mul_eq_zero.mp hfactored).resolve_left
        (backward_power_scale_pos ht).ne'
    simpa only [x, centered_dilation_center_add_inv_smul hscale] using hprofile
  · intro hprofile x
    rw [potential_residual_abnormal_ansatz_3d
      j Q Φ singularTime center x t ht]
    simp only [hprofile, mul_zero]

/-- Before the singular time, the elliptic equation for the abnormal ansatz is equivalent to the
profile elliptic equation at the corresponding similarity coordinate. -/
theorem potential_equation_abnormal_ansatz_3d_iff
    (j : ℕ) (Q Φ : ℝ^3 → ℝ) (singularTime : ℝ) (center x : ℝ^3) (t : ℝ)
    (ht : t < singularTime) :
    -laplacian
          (fun z ↦ abnormalPotentialAnsatz3D j Φ singularTime center z t) x =
        abnormalDensityAnsatz3D j Q singularTime center x t ↔
      -laplacian Φ
          (centeredDilation
            (backwardPowerScale (abnormalBeta3D j) singularTime t) center x) =
        Q
          (centeredDilation
            (backwardPowerScale (abnormalBeta3D j) singularTime t) center x) := by
  let y :=
    centeredDilation
      (backwardPowerScale (abnormalBeta3D j) singularTime t) center x
  change
    -laplacian
          (fun z ↦ abnormalPotentialAnsatz3D j Φ singularTime center z t) x =
        abnormalDensityAnsatz3D j Q singularTime center x t ↔
      -laplacian Φ y = Q y
  calc
    _ ↔
        potentialResidual
            (fun z ↦ abnormalDensityAnsatz3D j Q singularTime center z t)
            (fun z ↦ abnormalPotentialAnsatz3D j Φ singularTime center z t) x =
          0 :=
      (potential_residual_eq_zero_iff _ _ x).symm
    _ ↔ potentialResidual Q Φ y = 0 := by
      rw [potential_residual_abnormal_ansatz_3d
        j Q Φ singularTime center x t ht]
      exact mul_eq_zero_iff_left (backward_power_scale_pos ht).ne'
    _ ↔ -laplacian Φ y = Q y :=
      potential_residual_eq_zero_iff Q Φ y

/-- Full abnormal density residual at the scale `τ = T - t`.

The diffusion-free profile terms are followed by the lower-order diffusion contribution with its
exact similarity exponent.
-/
noncomputable def abnormalDensityProfileResidual3D
    (j : ℕ) (τ : ℝ) (Q Φ : ℝ^3 → ℝ) (y : ℝ^3) : ℝ :=
  Q y + abnormalBeta3D j * (∑ i, y i * (∇ Q y) i) +
    ∇· (fun z ↦ Q z • ∇ Φ z) y -
    τ ^ abnormalDiffusionExponent3D j * laplacian Q y

/-- Vanishing of the full residual is the time-dependent abnormal profile equation. -/
theorem abnormal_density_profile_residual_3d_eq_zero_iff
    (j : ℕ) (τ : ℝ) (Q Φ : ℝ^3 → ℝ) (y : ℝ^3) :
    abnormalDensityProfileResidual3D j τ Q Φ y = 0 ↔
      Q y + abnormalBeta3D j * (∑ i, y i * (∇ Q y) i) =
        τ ^ abnormalDiffusionExponent3D j * laplacian Q y -
          ∇· (fun z ↦ Q z • ∇ Φ z) y := by
  unfold abnormalDensityProfileResidual3D
  constructor <;> intro h <;> linarith

/-- A pointwise aggregation profile equation leaves exactly the scaled diffusion error. -/
theorem abnormal_density_profile_residual_3d_eq_diffusion_error
    {j : ℕ} {Q Φ : ℝ^3 → ℝ}
    (τ : ℝ) (y : ℝ^3)
    (haggregation :
      Q y + abnormalBeta3D j * (∑ i, y i * (∇ Q y) i) =
        -∇· (fun z ↦ Q z • ∇ Φ z) y) :
    abnormalDensityProfileResidual3D j τ Q Φ y =
      -(τ ^ abnormalDiffusionExponent3D j * laplacian Q y) := by
  unfold abnormalDensityProfileResidual3D
  rw [haggregation]
  abel

/-- Under the diffusion-free aggregation equation, the full profile residual vanishes at a
positive time scale exactly when the density profile is harmonic at that point.

This isolates the obstruction to turning the leading abnormal profile into an exact
time-dependent profile: away from the singular time, the diffusion coefficient is nonzero. -/
theorem abnormal_density_profile_residual_3d_eq_zero_iff_laplacian_eq_zero
    {j : ℕ} {Q Φ : ℝ^3 → ℝ} {τ : ℝ} (hτ : 0 < τ) (y : ℝ^3)
    (haggregation :
      Q y + abnormalBeta3D j * (∑ i, y i * (∇ Q y) i) =
        -∇· (fun z ↦ Q z • ∇ Φ z) y) :
    abnormalDensityProfileResidual3D j τ Q Φ y = 0 ↔
      laplacian Q y = 0 := by
  rw [abnormal_density_profile_residual_3d_eq_diffusion_error τ y haggregation]
  simp only [neg_eq_zero]
  exact mul_eq_zero_iff_left (Real.rpow_pos_of_pos hτ _).ne'

/-- At a fixed similarity point, an abnormal aggregation profile has vanishing rescaled density
residual as `t` approaches the singular time from below.

This limit concerns the profile residual. The physical density residual also contains the
singular prefactor `(T - t)⁻²`, so no convergence claim for the original PDE residual follows
from this theorem. -/
theorem tendsto_abnormal_density_profile_residual_3d
    {j : ℕ} (hj : 4 ≤ j) {Q Φ : ℝ^3 → ℝ}
    (singularTime : ℝ) (y : ℝ^3)
    (haggregation :
      Q y + abnormalBeta3D j * (∑ i, y i * (∇ Q y) i) =
        -∇· (fun z ↦ Q z • ∇ Φ z) y) :
    Tendsto
      (fun t ↦ abnormalDensityProfileResidual3D j (singularTime - t) Q Φ y)
      (nhdsWithin singularTime (Set.Iio singularTime)) (nhds 0) := by
  have herror :
      Tendsto
        (fun t ↦
          -((singularTime - t) ^ abnormalDiffusionExponent3D j * laplacian Q y))
        (nhdsWithin singularTime (Set.Iio singularTime)) (nhds 0) := by
    simpa only [zero_mul, neg_zero] using
      ((tendsto_abnormal_diffusion_coefficient_3d hj singularTime).mul_const
        (laplacian Q y)).neg
  exact herror.congr' <| Eventually.of_forall fun t ↦
    (abnormal_density_profile_residual_3d_eq_diffusion_error
      (singularTime - t) y haggregation).symm

/-- Exact substitution of the abnormal ansatz into the density equation.

The residual is `(T - t)⁻²` times the negative profile residual. Thus diffusion appears relative
to aggregation with coefficient `(T - t)^(1 - 2βⱼ)`; no profile existence is asserted.
-/
theorem density_residual_abnormal_ansatz_3d
    (j : ℕ) (Q Φ : ℝ^3 → ℝ) (singularTime : ℝ) (center x : ℝ^3) (t : ℝ)
    (hQ : ContDiff ℝ 2 Q) (hΦ : ContDiff ℝ 2 Φ) (ht : t < singularTime) :
    densityResidual
        (abnormalDensityAnsatz3D j Q singularTime center)
        (abnormalPotentialAnsatz3D j Φ singularTime center) x t =
      -backwardPowerScale 2 singularTime t *
        abnormalDensityProfileResidual3D j (singularTime - t) Q Φ
          (centeredDilation
            (backwardPowerScale (abnormalBeta3D j) singularTime t) center x) := by
  let y :=
    centeredDilation
      (backwardPowerScale (abnormalBeta3D j) singularTime t) center x
  have hQdiff : DifferentiableAt ℝ Q y :=
    (hQ.differentiable (by norm_num)).differentiableAt
  have htime :
      deriv
          (fun s ↦ abnormalDensityAnsatz3D j Q singularTime center x s) t =
        backwardPowerScale 2 singularTime t *
          (Q y + abnormalBeta3D j *
            ∑ i, y i * (∇ Q y) i) := by
    simpa only [abnormalDensityAnsatz3D, one_add_one_eq_two,
      scalingGenerator, one_mul, gradient_apply_eq_partialDeriv] using
      deriv_backward_self_similar_ansatz
        Q 1 (abnormalBeta3D j) singularTime center x t hQdiff ht
  -- Two spatial derivatives leave the relative diffusion factor `(T - t)^(1 - 2βⱼ)`.
  have hdiffusionCoefficient :
      backwardPowerScale 1 singularTime t *
          backwardPowerScale (abnormalBeta3D j) singularTime t ^ 2 =
        backwardPowerScale 2 singularTime t *
          (singularTime - t) ^ abnormalDiffusionExponent3D j := by
    rw [backward_power_scale_sq ht, backward_power_scale_mul ht]
    unfold backwardPowerScale
    rw [← Real.rpow_add (sub_pos.mpr ht)]
    congr 1
    simp [abnormalDiffusionExponent3D]
    ring
  have hlaplacian :
      laplacian
          (fun z ↦ abnormalDensityAnsatz3D j Q singularTime center z t) x =
        backwardPowerScale 2 singularTime t *
          (singularTime - t) ^ abnormalDiffusionExponent3D j *
            laplacian Q y := by
    change
      laplacian
          (fun z ↦ scaledProfileAnsatz Q
            (backwardPowerScale 1 singularTime)
            (backwardPowerScale (abnormalBeta3D j) singularTime) center z t) x = _
    rw [laplacian_scaled_profile_ansatz Q
      (backwardPowerScale 1 singularTime)
      (backwardPowerScale (abnormalBeta3D j) singularTime) center x t]
    rw [hdiffusionCoefficient]
  -- The density, potential gradient, and divergence factors combine to the `τ⁻²` scale.
  have hfluxCoefficient :
      (backwardPowerScale 1 singularTime t *
          (backwardPowerScale (abnormalDiffusionExponent3D j) singularTime t *
            backwardPowerScale (abnormalBeta3D j) singularTime t)) *
          backwardPowerScale (abnormalBeta3D j) singularTime t =
        backwardPowerScale 2 singularTime t := by
    rw [backward_power_scale_mul ht, backward_power_scale_mul ht,
      backward_power_scale_mul ht]
    congr 1
    simp [abnormalDiffusionExponent3D]
    ring
  have hfluxProfileDifferentiable (i : Fin 3) :
      DifferentiableAt ℝ (fun z ↦ (Q z • ∇ Φ z) i) y := by
    have hpartialΦ :
        Differentiable ℝ (fun z ↦ (∂[i] Φ) z) :=
      (contDiff_partialDeriv_of_succ (m := 1) (i := i) hΦ).differentiable
        (by norm_num)
    have hproduct :
        DifferentiableAt ℝ (fun z : ℝ^3 ↦ Q z * (∂[i] Φ) z) y :=
      (hQ.differentiable (by norm_num)).differentiableAt.mul
        hpartialΦ.differentiableAt
    simpa only [PiLp.smul_apply, smul_eq_mul, gradient_apply_eq_partialDeriv] using
      hproduct
  have hflux :
      (fun z ↦
          abnormalDensityAnsatz3D j Q singularTime center z t •
            ∇
              (fun w ↦ abnormalPotentialAnsatz3D j Φ singularTime center w t) z) =
        fun z ↦
          (backwardPowerScale 1 singularTime t *
            (backwardPowerScale (abnormalDiffusionExponent3D j) singularTime t *
              backwardPowerScale (abnormalBeta3D j) singularTime t)) •
            ((fun w ↦ Q w • ∇ Φ w)
              (centeredDilation
                (backwardPowerScale (abnormalBeta3D j) singularTime t) center z)) := by
    funext z
    change
      scaledProfileAnsatz Q
            (backwardPowerScale 1 singularTime)
            (backwardPowerScale (abnormalBeta3D j) singularTime) center z t •
          ∇
            (fun w ↦ scaledProfileAnsatz Φ
              (backwardPowerScale (abnormalDiffusionExponent3D j) singularTime)
              (backwardPowerScale (abnormalBeta3D j) singularTime) center w t) z = _
    rw [gradient_scaled_profile_ansatz Φ
      (backwardPowerScale (abnormalDiffusionExponent3D j) singularTime)
      (backwardPowerScale (abnormalBeta3D j) singularTime) center z t
      (hΦ.differentiable (by norm_num)).differentiableAt]
    ext i
    simp only [scaledProfileAnsatz, PiLp.smul_apply, smul_eq_mul]
    ring
  have hfluxDivergence :
      ∇·
          (fun z ↦
            abnormalDensityAnsatz3D j Q singularTime center z t •
              ∇
                (fun w ↦ abnormalPotentialAnsatz3D j Φ singularTime center w t) z) x =
        backwardPowerScale 2 singularTime t *
          ∇· (fun z ↦ Q z • ∇ Φ z) y := by
    rw [hflux]
    rw [divergence_smul_comp_centered_dilation
      (fun z ↦ Q z • ∇ Φ z)
      (backwardPowerScale 1 singularTime t *
        (backwardPowerScale (abnormalDiffusionExponent3D j) singularTime t *
          backwardPowerScale (abnormalBeta3D j) singularTime t))
      (backwardPowerScale (abnormalBeta3D j) singularTime t) center x
      hfluxProfileDifferentiable]
    rw [hfluxCoefficient]
  have huC2 :
      ContDiff ℝ 2
        (fun z ↦ abnormalDensityAnsatz3D j Q singularTime center z t) := by
    simpa only [abnormalDensityAnsatz3D, backwardSelfSimilarAnsatz] using
      contDiff_scaled_profile_ansatz_slice
        Q (backwardPowerScale 1 singularTime)
        (backwardPowerScale (abnormalBeta3D j) singularTime) center t hQ
  have hΦC2 :
      ContDiff ℝ 2
        (fun z ↦ abnormalPotentialAnsatz3D j Φ singularTime center z t) := by
    simpa only [abnormalPotentialAnsatz3D, backwardSelfSimilarAnsatz] using
      contDiff_scaled_profile_ansatz_slice
        Φ
        (backwardPowerScale (abnormalDiffusionExponent3D j) singularTime)
        (backwardPowerScale (abnormalBeta3D j) singularTime) center t hΦ
  have hgradientDensity (i : Fin 3) :
      DifferentiableAt ℝ
        (fun z ↦
          ∇
            (fun w ↦ abnormalDensityAnsatz3D j Q singularTime center w t) z i) x := by
    have hpartial :
        ContDiff ℝ 1
          (fun z ↦ (∂[i]
            (fun w ↦ abnormalDensityAnsatz3D j Q singularTime center w t)) z) :=
      contDiff_partialDeriv_of_succ (m := 1) (i := i) huC2
    simpa only [gradient_apply_eq_partialDeriv] using
      (hpartial.differentiable (by norm_num)).differentiableAt
  have hfluxSlice (i : Fin 3) :
      DifferentiableAt ℝ
        (fun z ↦
          (abnormalDensityAnsatz3D j Q singularTime center z t •
            ∇
              (fun w ↦ abnormalPotentialAnsatz3D j Φ singularTime center w t) z) i) x := by
    have hpotentialGradient :
        ContDiff ℝ 1
          (fun z ↦ (∂[i]
            (fun w ↦ abnormalPotentialAnsatz3D j Φ singularTime center w t)) z) :=
      contDiff_partialDeriv_of_succ (m := 1) (i := i) hΦC2
    have hproduct :
        DifferentiableAt ℝ
          (fun z : ℝ^3 ↦
            abnormalDensityAnsatz3D j Q singularTime center z t *
              (∂[i]
                (fun w ↦ abnormalPotentialAnsatz3D j Φ singularTime center w t)) z) x :=
      (huC2.differentiable (by norm_num)).differentiableAt.mul
        (hpotentialGradient.differentiable (by norm_num)).differentiableAt
    simpa only [PiLp.smul_apply, smul_eq_mul, gradient_apply_eq_partialDeriv] using
      hproduct
  change
    ∇·
        (fun z ↦
          ∇
              (fun w ↦ abnormalDensityAnsatz3D j Q singularTime center w t) z -
            abnormalDensityAnsatz3D j Q singularTime center z t •
              ∇
                (fun w ↦ abnormalPotentialAnsatz3D j Φ singularTime center w t) z) x -
      deriv (fun s ↦ abnormalDensityAnsatz3D j Q singularTime center x s) t = _
  rw [divergence_sub (n := 3)
    (F := ∇ (fun w ↦ abnormalDensityAnsatz3D j Q singularTime center w t))
    (G := fun z ↦ abnormalDensityAnsatz3D j Q singularTime center z t •
      ∇
        (fun w ↦ abnormalPotentialAnsatz3D j Φ singularTime center w t) z)
    (x := x) hgradientDensity hfluxSlice]
  rw [← laplacian_eq_divergence_gradient]
  rw [hlaplacian, hfluxDivergence, htime]
  simp only [abnormalDensityProfileResidual3D]
  ring

/-- At a fixed pre-singular time, the physical abnormal density residual vanishes everywhere
exactly when the full time-dependent profile residual vanishes everywhere.

The nonzero factor `(T - t)⁻²` and the invertible spatial dilation preserve zero sets. The
leading aggregation equation is not assumed. -/
theorem forall_density_residual_abnormal_ansatz_3d_eq_zero_iff
    (j : ℕ) (Q Φ : ℝ^3 → ℝ) (singularTime : ℝ) (center : ℝ^3) (t : ℝ)
    (hQ : ContDiff ℝ 2 Q) (hΦ : ContDiff ℝ 2 Φ) (ht : t < singularTime) :
    (∀ x,
      densityResidual
          (abnormalDensityAnsatz3D j Q singularTime center)
          (abnormalPotentialAnsatz3D j Φ singularTime center) x t =
        0) ↔
      ∀ y, abnormalDensityProfileResidual3D j (singularTime - t) Q Φ y = 0 := by
  constructor
  · intro hansatz y
    have hscale :
        backwardPowerScale (abnormalBeta3D j) singularTime t ≠ 0 :=
      (backward_power_scale_pos ht).ne'
    let x :=
      center +
        (backwardPowerScale (abnormalBeta3D j) singularTime t)⁻¹ • y
    have hfactored :
        -backwardPowerScale 2 singularTime t *
            abnormalDensityProfileResidual3D j (singularTime - t) Q Φ
              (centeredDilation
                (backwardPowerScale (abnormalBeta3D j) singularTime t) center x) =
          0 := by
      rw [← density_residual_abnormal_ansatz_3d
        j Q Φ singularTime center x t hQ hΦ ht]
      exact hansatz x
    have hprofile :
        abnormalDensityProfileResidual3D j (singularTime - t) Q Φ
            (centeredDilation
              (backwardPowerScale (abnormalBeta3D j) singularTime t) center x) =
          0 :=
      (mul_eq_zero.mp hfactored).resolve_left
        (neg_ne_zero.mpr (backward_power_scale_pos ht).ne')
    simpa only [x, centered_dilation_center_add_inv_smul hscale] using hprofile
  · intro hprofile x
    rw [density_residual_abnormal_ansatz_3d
      j Q Φ singularTime center x t hQ hΦ ht]
    simp only [hprofile, mul_zero]

/-- Before the singular time, the abnormal density equation is equivalent to the full
time-dependent profile equation at the corresponding similarity coordinate. -/
theorem density_equation_abnormal_ansatz_3d_iff
    (j : ℕ) (Q Φ : ℝ^3 → ℝ) (singularTime : ℝ) (center x : ℝ^3) (t : ℝ)
    (hQ : ContDiff ℝ 2 Q) (hΦ : ContDiff ℝ 2 Φ) (ht : t < singularTime) :
    deriv
          (fun s ↦ abnormalDensityAnsatz3D j Q singularTime center x s) t =
        ∇·
          (fun z ↦
            ∇
                (fun w ↦ abnormalDensityAnsatz3D j Q singularTime center w t) z -
              abnormalDensityAnsatz3D j Q singularTime center z t •
                ∇
                  (fun w ↦ abnormalPotentialAnsatz3D j Φ singularTime center w t) z) x ↔
      Q
            (centeredDilation
              (backwardPowerScale (abnormalBeta3D j) singularTime t) center x) +
          abnormalBeta3D j *
            ∑ i,
              centeredDilation
                  (backwardPowerScale (abnormalBeta3D j) singularTime t) center x i *
                ∇ Q
                    (centeredDilation
                      (backwardPowerScale (abnormalBeta3D j) singularTime t) center x) i =
        (singularTime - t) ^ abnormalDiffusionExponent3D j *
              laplacian Q
                (centeredDilation
                  (backwardPowerScale (abnormalBeta3D j) singularTime t) center x) -
            ∇· (fun z ↦ Q z • ∇ Φ z)
              (centeredDilation
                (backwardPowerScale (abnormalBeta3D j) singularTime t) center x) := by
  let y :=
    centeredDilation
      (backwardPowerScale (abnormalBeta3D j) singularTime t) center x
  change
    deriv
          (fun s ↦ abnormalDensityAnsatz3D j Q singularTime center x s) t =
        ∇·
          (fun z ↦
            ∇
                (fun w ↦ abnormalDensityAnsatz3D j Q singularTime center w t) z -
              abnormalDensityAnsatz3D j Q singularTime center z t •
                ∇
                  (fun w ↦ abnormalPotentialAnsatz3D j Φ singularTime center w t) z) x ↔
      Q y + abnormalBeta3D j * ∑ i, y i * ∇ Q y i =
        (singularTime - t) ^ abnormalDiffusionExponent3D j * laplacian Q y -
          ∇· (fun z ↦ Q z • ∇ Φ z) y
  calc
    _ ↔
        densityResidual
            (abnormalDensityAnsatz3D j Q singularTime center)
            (abnormalPotentialAnsatz3D j Φ singularTime center) x t =
          0 :=
      (density_residual_eq_zero_iff _ _ x t).symm
    _ ↔
        abnormalDensityProfileResidual3D j (singularTime - t) Q Φ
            y =
          0 := by
      rw [density_residual_abnormal_ansatz_3d
        j Q Φ singularTime center x t hQ hΦ ht]
      exact
        mul_eq_zero_iff_left
          (neg_ne_zero.mpr (backward_power_scale_pos ht).ne')
    _ ↔
        Q y + abnormalBeta3D j * ∑ i, y i * ∇ Q y i =
          (singularTime - t) ^ abnormalDiffusionExponent3D j * laplacian Q y -
            ∇· (fun z ↦ Q z • ∇ Φ z) y :=
      abnormal_density_profile_residual_3d_eq_zero_iff
        j (singularTime - t) Q Φ y

/-- A diffusion-free abnormal profile leaves exactly the lower-order diffusion residual.

Only the aggregation equation at the displayed similarity coordinate is needed, besides the
regularity used by the substitution theorem. What remains is the one term the leading abnormal
equation does not cancel. -/
theorem density_residual_abnormal_ansatz_3d_eq_diffusion_error
    (j : ℕ) (Q Φ : ℝ^3 → ℝ) (singularTime : ℝ) (center x : ℝ^3) (t : ℝ)
    (hQ : ContDiff ℝ 2 Q) (hΦ : ContDiff ℝ 2 Φ)
    (haggregation :
      Q
            (centeredDilation
              (backwardPowerScale (abnormalBeta3D j) singularTime t) center x) +
          abnormalBeta3D j *
            ∑ i,
              centeredDilation
                  (backwardPowerScale (abnormalBeta3D j) singularTime t) center x i *
                ∇ Q
                    (centeredDilation
                      (backwardPowerScale (abnormalBeta3D j) singularTime t) center x) i =
        -∇· (fun z ↦ Q z • ∇ Φ z)
          (centeredDilation
            (backwardPowerScale (abnormalBeta3D j) singularTime t) center x))
    (ht : t < singularTime) :
    densityResidual
        (abnormalDensityAnsatz3D j Q singularTime center)
        (abnormalPotentialAnsatz3D j Φ singularTime center) x t =
      backwardPowerScale 2 singularTime t *
        (singularTime - t) ^ abnormalDiffusionExponent3D j *
          laplacian Q
            (centeredDilation
              (backwardPowerScale (abnormalBeta3D j) singularTime t) center x) := by
  rw [density_residual_abnormal_ansatz_3d
    j Q Φ singularTime center x t hQ hΦ ht]
  rw [abnormal_density_profile_residual_3d_eq_diffusion_error
    (singularTime - t) _ haggregation]
  ring

/-- The physical density residual of an uncorrected abnormal profile diverges at the similarity
center whenever the profile is nonharmonic there.

At `x = center`, the similarity coordinate is `0`, so the diffusion-free profile equation
cancels the aggregation terms. Exact substitution leaves
`(T - t)⁻² (T - t)^(1 - 2βⱼ) ΔQ(0) = (T - t)^(-(1 + 2βⱼ)) ΔQ(0)`.
For `j ≥ 4`, the exponent `1 + 2βⱼ` is positive; thus `ΔQ(0) ≠ 0` forces the norm of
the physical residual to tend to `+∞`, even though the rescaled diffusion coefficient tends
to zero. -/
theorem tendsto_norm_density_residual_abnormal_ansatz_3d_at_center
    {j : ℕ} (hj : 4 ≤ j) (Q Φ : ℝ^3 → ℝ) (singularTime : ℝ) (center : ℝ^3)
    (hQ : ContDiff ℝ 2 Q) (hΦ : ContDiff ℝ 2 Φ)
    (haggregation :
      ∀ y,
        Q y + abnormalBeta3D j * (∑ i, y i * (∇ Q y) i) =
          -∇· (fun z ↦ Q z • ∇ Φ z) y)
    (hlaplacian : laplacian Q 0 ≠ 0) :
    Tendsto
      (fun t ↦
        ‖densityResidual
          (abnormalDensityAnsatz3D j Q singularTime center)
          (abnormalPotentialAnsatz3D j Φ singularTime center) center t‖)
      (nhdsWithin singularTime (Set.Iio singularTime)) atTop := by
  have hexponent : 0 < 1 + 2 * abnormalBeta3D j := by
    linarith [one_third_lt_abnormal_beta_3d hj]
  have hscale :
      Tendsto
        (fun t ↦
          backwardPowerScale (1 + 2 * abnormalBeta3D j) singularTime t *
            ‖laplacian Q 0‖)
        (nhdsWithin singularTime (Set.Iio singularTime)) atTop :=
    Filter.Tendsto.atTop_mul_const (norm_pos_iff.mpr hlaplacian)
      (tendsto_backward_power_scale_at_top hexponent)
  refine hscale.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  -- Multiplying the physical `τ⁻²` factor by the diffusion error gives `τ^(-(1 + 2βⱼ))`.
  have hcoefficient :
      backwardPowerScale 2 singularTime t *
          (singularTime - t) ^ abnormalDiffusionExponent3D j =
        backwardPowerScale (1 + 2 * abnormalBeta3D j) singularTime t := by
    unfold backwardPowerScale
    rw [← Real.rpow_add (sub_pos.mpr ht)]
    congr 1
    simp [abnormalDiffusionExponent3D]
    ring
  rw [density_residual_abnormal_ansatz_3d_eq_diffusion_error
    j Q Φ singularTime center center t hQ hΦ (haggregation _) ht]
  simp only [centeredDilation, sub_self, smul_zero]
  rw [hcoefficient, norm_mul]
  simp only [Real.norm_eq_abs, abs_of_pos (backward_power_scale_pos ht)]

/-- Global obstruction for the uncorrected abnormal density ansatz at one pre-singular time.

The leading aggregation profile equation omits diffusion. Exact substitution restores the term
`(T - t)^(1 - 2βⱼ) ΔQ`, whose coefficient is nonzero for every `t < T`; inverse dilation shows
that the physical residual samples every profile coordinate. Hence the exact density residual
vanishes everywhere exactly when `Q` is harmonic everywhere. This concerns only the density
residual of the uncorrected ansatz. -/
theorem forall_density_residual_abnormal_ansatz_3d_eq_zero_iff_laplacian_eq_zero
    (j : ℕ) (Q Φ : ℝ^3 → ℝ) (singularTime : ℝ) (center : ℝ^3) (t : ℝ)
    (hQ : ContDiff ℝ 2 Q) (hΦ : ContDiff ℝ 2 Φ)
    (haggregation :
      ∀ y,
        Q y + abnormalBeta3D j * (∑ i, y i * (∇ Q y) i) =
          -∇· (fun z ↦ Q z • ∇ Φ z) y)
    (ht : t < singularTime) :
    (∀ x,
      densityResidual
        (abnormalDensityAnsatz3D j Q singularTime center)
        (abnormalPotentialAnsatz3D j Φ singularTime center) x t = 0) ↔
      ∀ y, laplacian Q y = 0 := by
  rw [forall_density_residual_abnormal_ansatz_3d_eq_zero_iff
    j Q Φ singularTime center t hQ hΦ ht]
  constructor
  · intro hresidual y
    exact
      (abnormal_density_profile_residual_3d_eq_zero_iff_laplacian_eq_zero
        (sub_pos.mpr ht) y (haggregation y)).1 (hresidual y)
  · intro hlaplacian y
    exact
      (abnormal_density_profile_residual_3d_eq_zero_iff_laplacian_eq_zero
        (sub_pos.mpr ht) y (haggregation y)).2 (hlaplacian y)

end PDE.Solution.Singularity.FiniteTime.KellerSegel
