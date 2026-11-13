/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Representations.Similarity.Calculus
public import PDE.Solution.Singularity.FiniteTime.KellerSegel.Classical
public import PDE.Solution.Singularity.FiniteTime.Norm.SpatialSupremum
import Mathlib.Analysis.Calculus.FDeriv.Mul
import PDE.Solution.Singularity.FiniteTime.Norm.Similarity

/-!
# Parabolic Keller–Segel similarity profiles

We study the backward parabolic ansatz

`u(x,t) = (T - t)⁻¹ Q((T - t)^(-1/2) • (x - x₀))`

and substitute it into the parabolic–elliptic Keller–Segel residuals. The calculus comes from
the general `backwardSelfSimilarAnsatz`, `backwardPowerScale`, and `scalingGenerator`, so the
inverse-square-root identities are not rederived for Keller–Segel.

The profile equations are separate scalar identities, and regularity, nonnegativity, and
dimension restrictions are hypotheses of the theorems that use them. The fixed-time
zero-residual equivalences go both ways: since the pre-singular dilation is invertible, an
ansatz residual vanishes at every spatial point exactly when the profile residual vanishes
everywhere.

The profiles are pointwise functions because the residuals evaluate derivatives at a given
similarity coordinate. Sobolev and `Lᵖ` profiles would need a weak or almost-everywhere
formulation. The final assembly theorem gives joint spacetime `C¹` regularity and `C²` spatial
slices, not joint `C^{2,1}` regularity.

## Main results

* `parabolicDensityAnsatz`, `parabolicPotentialAnsatz`: the density
  `(T - t)⁻¹ Q((T - t)^(-1/2) (x - x₀))` and the potential `Φ((T - t)^(-1/2) (x - x₀))`.
* `parabolicDensityProfileResidual`: the reduced density equation
  `div (∇Q - Q ∇Φ) = Q + ½ y · ∇Q` in the similarity variable `y`.
* `density_residual_parabolic_ansatz`, `potential_residual_parabolic_ansatz`: for `t < T` the
  density residual is `(T - t)^(-2)` times the reduced density residual and the potential
  residual is `(T - t)^(-1)` times the elliptic profile residual, both at the similarity point.
* `density_equation_parabolic_ansatz_iff`, `potential_equation_parabolic_ansatz_iff`: the
  ansatz solves an equation at a fixed pre-singular time exactly when the profile solves the
  reduced equation everywhere.
* `parabolic_ansatz_is_nonnegative_pointwise_classical_solution_on`: `C²` profiles solving the
  two reduced equations, with `Q ≥ 0`, give a nonnegative pointwise classical solution on
  `t < T`.
* `parabolic_density_ansatz_blows_up_at`: a bounded profile with a nonzero value gives a density
  with finite spatial slices whose supremum norm tends to `∞` as `t → T⁻`.

## References

* E. F. Keller and L. A. Segel, "Initiation of slime mold aggregation viewed as an
  instability", *J. Theoret. Biol.* 26 (1970), 399-415.
  <https://doi.org/10.1016/0022-5193(70)90092-5>
* M. A. Herrero and J. J. L. Velázquez, "Singularity patterns in a chemotaxis model",
  *Math. Ann.* 306 (1996), 583-623.
  <https://doi.org/10.1007/BF01445268>
* B. Perthame, *Transport Equations in Biology*, Frontiers in Mathematics, Birkhäuser, 2007,
  chapter "Cell motion and chemotaxis", pp. 111-149.
  <https://doi.org/10.1007/978-3-7643-7842-4_5>
-/

open scoped Gradient

@[expose] public section

namespace PDE.Solution.Singularity.FiniteTime.KellerSegel

open Filter Topology
open PDE.Representations.Similarity

variable {d : ℕ}

/-- The density field induced by a backward parabolic Keller–Segel profile. -/
noncomputable def parabolicDensityAnsatz
    (profile : ℝ^d → ℝ) (singularTime : ℝ) (center : ℝ^d)
    (x : ℝ^d) (t : ℝ) : ℝ :=
  backwardSelfSimilarAnsatz profile 1 (1 / 2) singularTime center x t

/-- A bounded parabolic density profile with one nonzero value makes its ansatz blow up in spatial
supremum norm at the proposed singular time.

Only the similarity scaling is used: the profile need not solve the reduced equations, and the
ansatz need not be a Keller–Segel solution. -/
theorem parabolic_density_ansatz_blows_up_at
    (profile : ℝ^d → ℝ) (singularTime : ℝ) (center : ℝ^d)
    (y : ℝ^d) (hy : profile y ≠ 0)
    (hbounded : Bornology.IsBounded (Set.range profile)) :
    SpatialSupNormBlowsUpAt
      (parabolicDensityAnsatz profile singularTime center)
      singularTime := by
  exact
    backward_self_similar_ansatz_blows_up_at
      profile 1 (1 / 2) singularTime center zero_lt_one y hy hbounded

/-- The potential field with the spatial scale of the parabolic density ansatz. -/
noncomputable def parabolicPotentialAnsatz
    (profile : ℝ^d → ℝ) (singularTime : ℝ) (center : ℝ^d)
    (x : ℝ^d) (t : ℝ) : ℝ :=
  scaledProfileAnsatz profile
    (fun _ ↦ (1 : ℝ))
    (backwardPowerScale (1 / 2) singularTime)
    center x t

/-- Pointwise residual of the reduced parabolic density equation.

Its vanishing states
`Q + (1/2) y · ∇Q = div (∇Q - Q∇Φ)`.
-/
noncomputable def parabolicDensityProfileResidual
    (densityProfile potentialProfile : ℝ^d → ℝ) (y : ℝ^d) : ℝ :=
  ∇·
      (fun z ↦ ∇ densityProfile z -
        densityProfile z • ∇ potentialProfile z) y -
    scalingGenerator 1 (1 / 2) densityProfile y

/-- Vanishing of the parabolic density residual is the pointwise profile equation. -/
theorem parabolic_density_profile_residual_eq_zero_iff
    (densityProfile potentialProfile : ℝ^d → ℝ) (y : ℝ^d) :
    parabolicDensityProfileResidual densityProfile potentialProfile y = 0 ↔
      densityProfile y +
          (1 / 2) * ∑ i, y i * (∇ densityProfile y) i =
        ∇·
          (fun z ↦ ∇ densityProfile z -
            densityProfile z • ∇ potentialProfile z) y := by
  simp only [parabolicDensityProfileResidual, scalingGenerator, one_mul,
    gradient_apply_eq_partialDeriv, sub_eq_zero]
  exact eq_comm

/-- The elliptic residual of a parabolic similarity pair is exactly the profile residual
multiplied by `(T - t)⁻¹`.

No regularity of either profile is needed: the density enters this equation without
derivatives, and the Laplacian scales under the centered dilation for every potential profile. -/
theorem potential_residual_parabolic_ansatz
    (densityProfile potentialProfile : ℝ^d → ℝ)
    (singularTime : ℝ) (center x : ℝ^d) (t : ℝ)
    (ht : t < singularTime) :
    potentialResidual
        (fun y ↦ parabolicDensityAnsatz densityProfile singularTime center y t)
        (fun y ↦ parabolicPotentialAnsatz potentialProfile singularTime center y t) x =
      backwardPowerScale 1 singularTime t *
        potentialResidual densityProfile potentialProfile
          (centeredDilation
            (backwardPowerScale (1 / 2) singularTime t) center x) := by
  have hscale :
      backwardPowerScale (1 / 2) singularTime t ^ 2 =
        backwardPowerScale 1 singularTime t := by
    rw [backward_power_scale_sq ht]
    congr 2
    norm_num
  unfold potentialResidual parabolicPotentialAnsatz parabolicDensityAnsatz
  rw [laplacian_scaled_profile_ansatz potentialProfile
    (fun _ ↦ (1 : ℝ)) (backwardPowerScale (1 / 2) singularTime)
    center x t]
  simp only [backwardSelfSimilarAnsatz, scaledProfileAnsatz, one_mul, smul_eq_mul]
  rw [hscale]
  ring

/-- At a fixed pre-singular time, the potential residual of the parabolic ansatz vanishes
everywhere exactly when the elliptic profile residual vanishes everywhere.

The reverse implication needs more than substitution: inverse dilation realizes each profile
coordinate as a physical spatial point. -/
theorem forall_potential_residual_parabolic_ansatz_eq_zero_iff
    (densityProfile potentialProfile : ℝ^d → ℝ)
    (singularTime : ℝ) (center : ℝ^d) (t : ℝ)
    (ht : t < singularTime) :
    (∀ x,
      potentialResidual
          (fun y ↦ parabolicDensityAnsatz densityProfile singularTime center y t)
          (fun y ↦ parabolicPotentialAnsatz potentialProfile singularTime center y t) x =
        0) ↔
      ∀ y, potentialResidual densityProfile potentialProfile y = 0 := by
  constructor
  · intro hansatz y
    have hscale :
        backwardPowerScale (1 / 2) singularTime t ≠ 0 :=
      (backward_power_scale_pos ht).ne'
    let x :=
      center +
        (backwardPowerScale (1 / 2) singularTime t)⁻¹ • y
    have hfactored :
        backwardPowerScale 1 singularTime t *
            potentialResidual densityProfile potentialProfile
              (centeredDilation
                (backwardPowerScale (1 / 2) singularTime t) center x) =
          0 := by
      rw [← potential_residual_parabolic_ansatz densityProfile potentialProfile
        singularTime center x t ht]
      exact hansatz x
    have hprofile :
        potentialResidual densityProfile potentialProfile
            (centeredDilation
              (backwardPowerScale (1 / 2) singularTime t) center x) =
          0 :=
      (mul_eq_zero.mp hfactored).resolve_left
        (backward_power_scale_pos ht).ne'
    simpa only [x, centered_dilation_center_add_inv_smul hscale] using hprofile
  · intro hprofile x
    rw [potential_residual_parabolic_ansatz densityProfile potentialProfile
      singularTime center x t ht]
    simp only [hprofile, mul_zero]

/-- A classical parabolic ansatz forces the elliptic residual of its profiles to vanish.

The proof reads the physical elliptic equation on one pre-singular time slice and then uses the
surjectivity of the similarity dilation. -/
theorem IsNonnegativePointwiseClassicalSolutionOn.parabolic_potential_profile_residual_eq_zero
    {densityProfile potentialProfile : ℝ^d → ℝ}
    {singularTime : ℝ} {center : ℝ^d}
    (hsolution :
      IsNonnegativePointwiseClassicalSolutionOn (Set.Iio singularTime)
        (parabolicDensityAnsatz densityProfile singularTime center)
        (parabolicPotentialAnsatz potentialProfile singularTime center))
    :
    ∀ y, potentialResidual densityProfile potentialProfile y = 0 := by
  have ht : singularTime - 1 < singularTime := by
    linarith
  apply
    (forall_potential_residual_parabolic_ansatz_eq_zero_iff
      densityProfile potentialProfile singularTime center (singularTime - 1)
       ht).1
  intro x
  exact hsolution.potential_residual_eq_zero x (singularTime - 1) ht

/-- The elliptic equation for a parabolic ansatz is equivalent to the profile equation at the
corresponding similarity coordinate. -/
theorem potential_equation_parabolic_ansatz_iff
    (densityProfile potentialProfile : ℝ^d → ℝ)
    (singularTime : ℝ) (center x : ℝ^d) (t : ℝ)
    (ht : t < singularTime) :
    -laplacian
          (fun y ↦ parabolicPotentialAnsatz potentialProfile singularTime center y t) x =
        parabolicDensityAnsatz densityProfile singularTime center x t ↔
      -laplacian potentialProfile
          (centeredDilation
            (backwardPowerScale (1 / 2) singularTime t) center x) =
        densityProfile
          (centeredDilation
            (backwardPowerScale (1 / 2) singularTime t) center x) := by
  let y :=
    centeredDilation
      (backwardPowerScale (1 / 2) singularTime t) center x
  change
    -laplacian
          (fun z ↦ parabolicPotentialAnsatz potentialProfile singularTime center z t) x =
        parabolicDensityAnsatz densityProfile singularTime center x t ↔
      -laplacian potentialProfile y = densityProfile y
  calc
    _ ↔
        potentialResidual
            (fun z ↦ parabolicDensityAnsatz densityProfile singularTime center z t)
            (fun z ↦ parabolicPotentialAnsatz potentialProfile singularTime center z t) x =
          0 :=
      (potential_residual_eq_zero_iff _ _ x).symm
    _ ↔ potentialResidual densityProfile potentialProfile y = 0 := by
      rw [potential_residual_parabolic_ansatz densityProfile potentialProfile
        singularTime center x t ht]
      exact mul_eq_zero_iff_left (backward_power_scale_pos ht).ne'
    _ ↔ -laplacian potentialProfile y = densityProfile y :=
      potential_residual_eq_zero_iff densityProfile potentialProfile y

/-- Time differentiation of the density ansatz gives the Euler scaling generator.

The profile needs only `C¹` regularity for this identity. -/
theorem deriv_parabolic_density_ansatz
    (profile : ℝ^d → ℝ) (singularTime : ℝ) (center x : ℝ^d) (t : ℝ)
    (hprofile : ContDiff ℝ 1 profile) (ht : t < singularTime) :
    deriv (fun s ↦ parabolicDensityAnsatz profile singularTime center x s) t =
      backwardPowerScale 2 singularTime t *
        scalingGenerator 1 (1 / 2) profile
          (centeredDilation
            (backwardPowerScale (1 / 2) singularTime t) center x) := by
  simpa only [parabolicDensityAnsatz, one_add_one_eq_two] using
    deriv_backward_self_similar_ansatz
      profile 1 (1 / 2) singularTime center x t
      (hprofile.differentiable (by norm_num) _) ht

/-- At fixed time, the gradient of the parabolic density ansatz gains one factor from its
amplitude and one from its spatial dilation. -/
theorem gradient_parabolic_density_ansatz
    (profile : ℝ^d → ℝ) (singularTime : ℝ) (center x : ℝ^d) (t : ℝ)
    (hprofile :
      DifferentiableAt ℝ profile
        (centeredDilation
          (backwardPowerScale (1 / 2) singularTime t) center x)) :
    ∇
        (fun y ↦ parabolicDensityAnsatz profile singularTime center y t) x =
      (backwardPowerScale 1 singularTime t *
          backwardPowerScale (1 / 2) singularTime t) •
        ∇ profile
          (centeredDilation
            (backwardPowerScale (1 / 2) singularTime t) center x) := by
  simpa only [parabolicDensityAnsatz, backwardSelfSimilarAnsatz] using
    gradient_scaled_profile_ansatz profile
      (backwardPowerScale 1 singularTime)
      (backwardPowerScale (1 / 2) singularTime)
      center x t hprofile

/-- At fixed time, the gradient of the parabolic potential ansatz gains exactly the spatial
dilation factor; its amplitude is constant. -/
theorem gradient_parabolic_potential_ansatz
    (profile : ℝ^d → ℝ) (singularTime : ℝ) (center x : ℝ^d) (t : ℝ)
    (hprofile :
      DifferentiableAt ℝ profile
        (centeredDilation
          (backwardPowerScale (1 / 2) singularTime t) center x)) :
    ∇
        (fun y ↦ parabolicPotentialAnsatz profile singularTime center y t) x =
      backwardPowerScale (1 / 2) singularTime t •
        ∇ profile
          (centeredDilation
            (backwardPowerScale (1 / 2) singularTime t) center x) := by
  simpa only [parabolicPotentialAnsatz, one_mul] using
    gradient_scaled_profile_ansatz profile
      (fun _ ↦ (1 : ℝ))
      (backwardPowerScale (1 / 2) singularTime)
      center x t hprofile

/-- The physical Keller–Segel flux of the parabolic ansatz is a scaled pullback of the profile
flux `∇Q - Q∇Φ`. -/
theorem parabolic_ansatz_flux_eq
    (densityProfile potentialProfile : ℝ^d → ℝ)
    (singularTime : ℝ) (center x : ℝ^d) (t : ℝ)
    (hdensity :
      DifferentiableAt ℝ densityProfile
        (centeredDilation
          (backwardPowerScale (1 / 2) singularTime t) center x))
    (hpotential :
      DifferentiableAt ℝ potentialProfile
        (centeredDilation
          (backwardPowerScale (1 / 2) singularTime t) center x)) :
    ∇
          (fun y ↦ parabolicDensityAnsatz densityProfile singularTime center y t) x -
        parabolicDensityAnsatz densityProfile singularTime center x t •
          ∇
            (fun y ↦ parabolicPotentialAnsatz potentialProfile singularTime center y t) x =
      (backwardPowerScale 1 singularTime t *
          backwardPowerScale (1 / 2) singularTime t) •
        (∇ densityProfile
            (centeredDilation
              (backwardPowerScale (1 / 2) singularTime t) center x) -
          densityProfile
              (centeredDilation
                (backwardPowerScale (1 / 2) singularTime t) center x) •
            ∇ potentialProfile
              (centeredDilation
                (backwardPowerScale (1 / 2) singularTime t) center x)) := by
  rw [gradient_parabolic_density_ansatz
    densityProfile singularTime center x t hdensity]
  rw [gradient_parabolic_potential_ansatz
    potentialProfile singularTime center x t hpotential]
  unfold parabolicDensityAnsatz backwardSelfSimilarAnsatz scaledProfileAnsatz
  ext i
  simp only [WithLp.ofLp_sub, Pi.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- The divergence of the parabolic Keller–Segel flux is the profile-flux divergence
multiplied by `(T - t)⁻²`.

Both profiles require `C²` regularity: one derivative forms the gradients and a second
derivative forms the divergence. -/
theorem divergence_parabolic_ansatz_flux
    (densityProfile potentialProfile : ℝ^d → ℝ)
    (singularTime : ℝ) (center x : ℝ^d) (t : ℝ)
    (hdensity : ContDiff ℝ 2 densityProfile)
    (hpotential : ContDiff ℝ 2 potentialProfile)
    (ht : t < singularTime) :
    ∇·
        (fun z ↦
          ∇
              (fun w ↦ parabolicDensityAnsatz densityProfile singularTime center w t) z -
            parabolicDensityAnsatz densityProfile singularTime center z t •
              ∇
                (fun w ↦
                  parabolicPotentialAnsatz potentialProfile singularTime center w t) z) x =
      backwardPowerScale 2 singularTime t *
        ∇·
          (fun z ↦ ∇ densityProfile z -
            densityProfile z • ∇ potentialProfile z)
          (centeredDilation
            (backwardPowerScale (1 / 2) singularTime t) center x) := by
  have hscale :
      backwardPowerScale (1 / 2) singularTime t ^ 2 =
        backwardPowerScale 1 singularTime t := by
    rw [backward_power_scale_sq ht]
    congr 2
    norm_num
  have hamplitude :
      backwardPowerScale 1 singularTime t *
          backwardPowerScale 1 singularTime t =
        backwardPowerScale 2 singularTime t := by
    rw [backward_power_scale_mul ht]
    congr 2
    norm_num
  -- Pull back the physical flux before differentiating it in the spatial variable.
  have hflux :
      (fun z ↦
          ∇
              (fun w ↦ parabolicDensityAnsatz densityProfile singularTime center w t) z -
            parabolicDensityAnsatz densityProfile singularTime center z t •
              ∇
                (fun w ↦
                  parabolicPotentialAnsatz potentialProfile singularTime center w t) z) =
        fun z ↦
          (backwardPowerScale 1 singularTime t *
              backwardPowerScale (1 / 2) singularTime t) •
            (∇ densityProfile
                (centeredDilation
                  (backwardPowerScale (1 / 2) singularTime t) center z) -
              densityProfile
                  (centeredDilation
                    (backwardPowerScale (1 / 2) singularTime t) center z) •
                ∇ potentialProfile
                  (centeredDilation
                    (backwardPowerScale (1 / 2) singularTime t) center z)) := by
    funext z
    exact
      parabolic_ansatz_flux_eq
        densityProfile potentialProfile singularTime center z t
        (hdensity.differentiable (by norm_num) _)
        (hpotential.differentiable (by norm_num) _)
  have hprofileFlux (i : Fin d) :
      DifferentiableAt ℝ
        (fun z ↦
          (∇ densityProfile z -
            densityProfile z • ∇ potentialProfile z) i)
        (centeredDilation
          (backwardPowerScale (1 / 2) singularTime t) center x) := by
    rw [show
      (fun z ↦
        (∇ densityProfile z -
          densityProfile z • ∇ potentialProfile z) i) =
        fun z ↦ (∂[i] densityProfile) z -
          densityProfile z * (∂[i] potentialProfile) z by
      funext z
      simp]
    have hDdensity : DifferentiableAt ℝ
        (fun z : ℝ^d ↦ (∂[i] densityProfile) z)
        (centeredDilation
          (backwardPowerScale (1 / 2) singularTime t) center x) :=
      ((contDiff_partialDeriv_of_succ (m := 1) (i := i) hdensity).differentiable
        (by norm_num)).differentiableAt
    have hDpotential : DifferentiableAt ℝ
        (fun z : ℝ^d ↦ (∂[i] potentialProfile) z)
        (centeredDilation
          (backwardPowerScale (1 / 2) singularTime t) center x) :=
      ((contDiff_partialDeriv_of_succ (m := 1) (i := i) hpotential).differentiable
        (by norm_num)).differentiableAt
    exact hDdensity.sub
      ((hdensity.differentiable (by norm_num)).differentiableAt.mul hDpotential)
  rw [hflux]
  rw [divergence_smul_comp_centered_dilation
    (fun z ↦ ∇ densityProfile z -
      densityProfile z • ∇ potentialProfile z)
    (backwardPowerScale 1 singularTime t *
      backwardPowerScale (1 / 2) singularTime t)
    (backwardPowerScale (1 / 2) singularTime t) center x hprofileFlux]
  calc
    (backwardPowerScale 1 singularTime t *
          backwardPowerScale (1 / 2) singularTime t) *
          backwardPowerScale (1 / 2) singularTime t *
        ∇·
          (fun z ↦ ∇ densityProfile z -
            densityProfile z • ∇ potentialProfile z)
          (centeredDilation
            (backwardPowerScale (1 / 2) singularTime t) center x) =
      backwardPowerScale 1 singularTime t *
          backwardPowerScale (1 / 2) singularTime t ^ 2 *
        ∇·
          (fun z ↦ ∇ densityProfile z -
            densityProfile z • ∇ potentialProfile z)
          (centeredDilation
            (backwardPowerScale (1 / 2) singularTime t) center x) := by
      ring
    _ = backwardPowerScale 1 singularTime t *
          backwardPowerScale 1 singularTime t *
        ∇·
          (fun z ↦ ∇ densityProfile z -
            densityProfile z • ∇ potentialProfile z)
          (centeredDilation
            (backwardPowerScale (1 / 2) singularTime t) center x) := by
      rw [hscale]
    _ = _ := by rw [hamplitude]

/-- Exact reduction of the parabolic density residual to the stationary profile residual.

So a `C²` profile pair satisfying the reduced density equation has zero density residual at
every point before the singular time. -/
theorem density_residual_parabolic_ansatz
    (densityProfile potentialProfile : ℝ^d → ℝ)
    (singularTime : ℝ) (center x : ℝ^d) (t : ℝ)
    (hdensity : ContDiff ℝ 2 densityProfile)
    (hpotential : ContDiff ℝ 2 potentialProfile)
    (ht : t < singularTime) :
    densityResidual
        (parabolicDensityAnsatz densityProfile singularTime center)
        (parabolicPotentialAnsatz potentialProfile singularTime center) x t =
      backwardPowerScale 2 singularTime t *
        parabolicDensityProfileResidual densityProfile potentialProfile
          (centeredDilation
            (backwardPowerScale (1 / 2) singularTime t) center x) := by
  unfold densityResidual
  rw [divergence_parabolic_ansatz_flux densityProfile potentialProfile
    singularTime center x t hdensity hpotential ht]
  rw [deriv_parabolic_density_ansatz densityProfile singularTime center x t
    (hdensity.of_le (by norm_num)) ht]
  unfold parabolicDensityProfileResidual
  ring

/-- At a fixed pre-singular time, the density residual of the parabolic ansatz vanishes
everywhere exactly when the stationary density-profile residual vanishes everywhere.

The converse evaluates the ansatz at inverse-dilated spatial points, which turns the usual
one-way profile construction into a characterization. -/
theorem forall_density_residual_parabolic_ansatz_eq_zero_iff
    (densityProfile potentialProfile : ℝ^d → ℝ)
    (singularTime : ℝ) (center : ℝ^d) (t : ℝ)
    (hdensity : ContDiff ℝ 2 densityProfile)
    (hpotential : ContDiff ℝ 2 potentialProfile)
    (ht : t < singularTime) :
    (∀ x,
      densityResidual
          (parabolicDensityAnsatz densityProfile singularTime center)
          (parabolicPotentialAnsatz potentialProfile singularTime center) x t =
        0) ↔
      ∀ y, parabolicDensityProfileResidual densityProfile potentialProfile y = 0 := by
  constructor
  · intro hansatz y
    have hscale :
        backwardPowerScale (1 / 2) singularTime t ≠ 0 :=
      (backward_power_scale_pos ht).ne'
    let x :=
      center +
        (backwardPowerScale (1 / 2) singularTime t)⁻¹ • y
    have hfactored :
        backwardPowerScale 2 singularTime t *
            parabolicDensityProfileResidual densityProfile potentialProfile
              (centeredDilation
                (backwardPowerScale (1 / 2) singularTime t) center x) =
          0 := by
      rw [← density_residual_parabolic_ansatz densityProfile potentialProfile
        singularTime center x t hdensity hpotential ht]
      exact hansatz x
    have hprofile :
        parabolicDensityProfileResidual densityProfile potentialProfile
            (centeredDilation
              (backwardPowerScale (1 / 2) singularTime t) center x) =
          0 :=
      (mul_eq_zero.mp hfactored).resolve_left
        (backward_power_scale_pos ht).ne'
    simpa only [x, centered_dilation_center_add_inv_smul hscale] using hprofile
  · intro hprofile x
    rw [density_residual_parabolic_ansatz densityProfile potentialProfile
      singularTime center x t hdensity hpotential ht]
    simp only [hprofile, mul_zero]

/-- A classical parabolic ansatz forces the stationary density-profile residual to vanish.

The reduced equation is recovered from the physical PDE, not assumed. -/
theorem IsNonnegativePointwiseClassicalSolutionOn.parabolic_density_profile_residual_eq_zero
    {densityProfile potentialProfile : ℝ^d → ℝ}
    {singularTime : ℝ} {center : ℝ^d}
    (hsolution :
      IsNonnegativePointwiseClassicalSolutionOn (Set.Iio singularTime)
        (parabolicDensityAnsatz densityProfile singularTime center)
        (parabolicPotentialAnsatz potentialProfile singularTime center))
    (hdensity : ContDiff ℝ 2 densityProfile)
    (hpotential : ContDiff ℝ 2 potentialProfile) :
    ∀ y, parabolicDensityProfileResidual densityProfile potentialProfile y = 0 := by
  have ht : singularTime - 1 < singularTime := by
    linarith
  apply
    (forall_density_residual_parabolic_ansatz_eq_zero_iff
      densityProfile potentialProfile singularTime center (singularTime - 1)
      hdensity hpotential ht).1
  intro x
  exact hsolution.density_residual_eq_zero x (singularTime - 1) ht

/-- The parabolic density equation is equivalent to the stationary profile equation at the
corresponding similarity coordinate. -/
theorem density_equation_parabolic_ansatz_iff
    (densityProfile potentialProfile : ℝ^d → ℝ)
    (singularTime : ℝ) (center x : ℝ^d) (t : ℝ)
    (hdensity : ContDiff ℝ 2 densityProfile)
    (hpotential : ContDiff ℝ 2 potentialProfile)
    (ht : t < singularTime) :
    deriv
          (fun s ↦ parabolicDensityAnsatz densityProfile singularTime center x s) t =
        ∇·
          (fun z ↦
            ∇
                (fun w ↦ parabolicDensityAnsatz densityProfile singularTime center w t) z -
              parabolicDensityAnsatz densityProfile singularTime center z t •
                ∇
                  (fun w ↦
                    parabolicPotentialAnsatz potentialProfile singularTime center w t) z) x ↔
      densityProfile
            (centeredDilation
              (backwardPowerScale (1 / 2) singularTime t) center x) +
          (1 / 2) *
            ∑ i,
              centeredDilation
                  (backwardPowerScale (1 / 2) singularTime t) center x i *
                ∇ densityProfile
                    (centeredDilation
                      (backwardPowerScale (1 / 2) singularTime t) center x) i =
        ∇·
          (fun z ↦ ∇ densityProfile z -
            densityProfile z • ∇ potentialProfile z)
          (centeredDilation
            (backwardPowerScale (1 / 2) singularTime t) center x) := by
  let y :=
    centeredDilation
      (backwardPowerScale (1 / 2) singularTime t) center x
  change
    deriv
          (fun s ↦ parabolicDensityAnsatz densityProfile singularTime center x s) t =
        ∇·
          (fun z ↦
            ∇
                (fun w ↦ parabolicDensityAnsatz densityProfile singularTime center w t) z -
              parabolicDensityAnsatz densityProfile singularTime center z t •
                ∇
                  (fun w ↦
                    parabolicPotentialAnsatz potentialProfile singularTime center w t) z) x ↔
      densityProfile y + (1 / 2) * ∑ i, y i * ∇ densityProfile y i =
        ∇·
          (fun z ↦ ∇ densityProfile z -
            densityProfile z • ∇ potentialProfile z) y
  calc
    _ ↔
        densityResidual
            (parabolicDensityAnsatz densityProfile singularTime center)
            (parabolicPotentialAnsatz potentialProfile singularTime center) x t =
          0 :=
      (density_residual_eq_zero_iff _ _ x t).symm
    _ ↔ parabolicDensityProfileResidual densityProfile potentialProfile y = 0 := by
      rw [density_residual_parabolic_ansatz densityProfile potentialProfile
        singularTime center x t hdensity hpotential ht]
      exact mul_eq_zero_iff_left (backward_power_scale_pos ht).ne'
    _ ↔
        densityProfile y + (1 / 2) * ∑ i, y i * ∇ densityProfile y i =
          ∇·
            (fun z ↦ ∇ densityProfile z -
              densityProfile z • ∇ potentialProfile z) y :=
      parabolic_density_profile_residual_eq_zero_iff densityProfile potentialProfile y

/-- A nonnegative `C²` profile pair whose two reduced residuals vanish gives a pointwise classical
Keller–Segel solution on `t < T`.

The density and potential residual laws are separate hypotheses. They are stated as vanishing
residuals; `parabolic_density_profile_residual_eq_zero_iff` and
`potential_residual_eq_zero_iff` give the expanded equations. -/
theorem parabolic_ansatz_is_nonnegative_pointwise_classical_solution_on
    (densityProfile potentialProfile : ℝ^d → ℝ)
    (singularTime : ℝ) (center : ℝ^d)
    (hdensity : ContDiff ℝ 2 densityProfile)
    (hpotential : ContDiff ℝ 2 potentialProfile)
    (hnonnegative : ∀ y, 0 ≤ densityProfile y)
    (hdensityResidual :
      ∀ y, parabolicDensityProfileResidual densityProfile potentialProfile y = 0)
    (hpotentialResidual :
      ∀ y, potentialResidual densityProfile potentialProfile y = 0) :
    IsNonnegativePointwiseClassicalSolutionOn (Set.Iio singularTime)
      (parabolicDensityAnsatz densityProfile singularTime center)
      (parabolicPotentialAnsatz potentialProfile singularTime center) := by
  refine
    { time_domain_open := isOpen_Iio
      density_spacetime_contDiffOn := ?_
      potential_spacetime_continuousOn := ?_
      density_spatial_slice_contDiff := ?_
      potential_spatial_slice_contDiff := ?_
      density_nonnegative := ?_
      density_equation := ?_
      potential_equation := ?_ }
  · -- The pre-singular power scales are smooth, so profile `C²` yields joint spacetime `C¹`.
    simpa only [parabolicDensityAnsatz, backwardSelfSimilarAnsatz] using
      contDiffOn_prod_scaled_profile_ansatz
        densityProfile
        (backwardPowerScale 1 singularTime)
        (backwardPowerScale (1 / 2) singularTime)
        center (Set.Iio singularTime)
        (hdensity.of_le (by norm_num))
        (contDiffOn_backward_power_scale 1 singularTime)
        (contDiffOn_backward_power_scale (1 / 2) singularTime)
  · have hpotentialSpacetime :
        ContDiffOn ℝ 1
          (fun xt : ℝ^d × ℝ ↦
            parabolicPotentialAnsatz
              potentialProfile singularTime center xt.1 xt.2)
          (Set.univ ×ˢ Set.Iio singularTime) := by
      simpa only [parabolicPotentialAnsatz] using
        contDiffOn_prod_scaled_profile_ansatz
          potentialProfile
          (fun _ ↦ (1 : ℝ))
          (backwardPowerScale (1 / 2) singularTime)
          center (Set.Iio singularTime)
          (hpotential.of_le (by norm_num)) contDiffOn_const
          (contDiffOn_backward_power_scale (1 / 2) singularTime)
    exact hpotentialSpacetime.continuousOn
  · -- At fixed time, the ansatz is a scalar multiple of a profile composed with an affine map.
    intro t _ht
    simpa only [parabolicDensityAnsatz, backwardSelfSimilarAnsatz] using
      contDiff_scaled_profile_ansatz_slice
        densityProfile
        (backwardPowerScale 1 singularTime)
        (backwardPowerScale (1 / 2) singularTime)
        center t hdensity
  · intro t _ht
    simpa only [parabolicPotentialAnsatz] using
      contDiff_scaled_profile_ansatz_slice
        potentialProfile
        (fun _ ↦ (1 : ℝ))
        (backwardPowerScale (1 / 2) singularTime)
        center t hpotential
  · intro x t ht
    change
      0 ≤ backwardPowerScale 1 singularTime t *
        densityProfile
          (centeredDilation
            (backwardPowerScale (1 / 2) singularTime t) center x)
    exact mul_nonneg (backward_power_scale_pos ht).le (hnonnegative _)
  · intro x t ht
    apply (density_residual_eq_zero_iff _ _ x t).1
    rw [density_residual_parabolic_ansatz densityProfile potentialProfile
      singularTime center x t hdensity hpotential ht]
    simp only [hdensityResidual, mul_zero]
  · intro x t ht
    apply (potential_residual_eq_zero_iff _ _ x).1
    rw [potential_residual_parabolic_ansatz densityProfile potentialProfile
      singularTime center x t ht]
    simp only [hpotentialResidual, mul_zero]

end PDE.Solution.Singularity.FiniteTime.KellerSegel
