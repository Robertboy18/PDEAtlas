/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Stokes.Ball.SphericalForm
public import PDE.CoordinateSystems.Spherical.AxisymmetricIntegration

/-!
# Orthogonality of the ball modes

Modes with different eigenvalues are orthogonal in `L²(B(0, R))` by the weak eigenvalue
equation tested with each other. Modes of different kind or different degree are orthogonal for
every pair of radial parameters: the ball integral of an axisymmetric function is
`2π ∫₀ᴿ ∫₀^π f(r, θ) r² sin θ dθ dr`, the frames are orthonormal and the zonal harmonics and their
derivatives are orthogonal for `sin θ dθ`. Together, distinct modes with nonnegative boundary
roots are orthogonal both in `L²` and for the gradient pairing, and modes of nonzero root are
orthogonal to the zero mode `e_z`. The same argument shows that a weak eigenfunction of
eigenvalue `μ` with integrable weak derivatives is orthogonal to every mode of eigenvalue
different from `μ`, and to `e_z` when `μ ≠ 0`.
-/

@[expose] public noncomputable section

open MeasureTheory MvPolynomial Set Real
open PDE (partialDeriv laplacian divergence)
open PDE.Analysis.SpecialFunctions PDE.CoordinateSystems PDE.CoordinateSystems.Spherical
open scoped RealInnerProductSpace ContDiff

namespace PDE.Fluid.Stokes.Ball

/-! ### Orthogonality -/

private theorem contDiff_one_mode (R : ℝ) (k : ModeKind) (l : ℕ) (α : ℝ) :
    ContDiff ℝ 1 (mode R k l α) :=
  (mode_contDiff R k l α).of_le (by exact_mod_cast le_top)

/-- Modes with different eigenvalues are orthogonal in `L²(B(0, R))`. -/
theorem integral_inner_mode_eq_zero_of_sq_ne {R : ℝ} (hR : 0 < R) {k k' : ModeKind}
    {l l' : ℕ} {α α' : ℝ} (hα : boundaryFunction k l α = 0)
    (hα' : boundaryFunction k' l' α' = 0) (hne : α ^ 2 ≠ α' ^ 2) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ⟪mode R k l α x, mode R k' l' α' x⟫ = 0 := by
  have h1 := mode_weak_eigen_of_contDiff hR hα (contDiff_one_mode R k' l' α')
    (fun x _ ↦ mode_divergence_eq_zero R k' l' α' x)
  have h2 := mode_weak_eigen_of_contDiff hR hα' (contDiff_one_mode R k l α)
    (fun x _ ↦ mode_divergence_eq_zero R k l α x)
  have hsym : ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
      ∂[j] (fun y ↦ mode R k' l' α' y i) x * ∂[j] (fun y ↦ mode R k l α y i) x =
      ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
        ∂[j] (fun y ↦ mode R k l α y i) x * ∂[j] (fun y ↦ mode R k' l' α' y i) x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun j _ ↦ mul_comm _ _)
  have hsym' : ∫ x in Metric.ball (0 : ℝ^3) R, ⟪mode R k' l' α' x, mode R k l α x⟫ =
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪mode R k l α x, mode R k' l' α' x⟫ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ real_inner_comm _ _)
  rw [hsym, hsym', h1] at h2
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR.ne'
  have hdiff : (α / R) ^ 2 - (α' / R) ^ 2 ≠ 0 := by
    rw [div_pow, div_pow, ← sub_div]
    exact div_ne_zero (sub_ne_zero.mpr hne) hR2
  have h3 : ((α / R) ^ 2 - (α' / R) ^ 2) *
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪mode R k l α x, mode R k' l' α' x⟫ = 0 := by
    rw [sub_mul, h2, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left hdiff

/-- A weak eigenfunction is orthogonal to the modes of other eigenvalues. Let `u` have
integrable components and integrable weak derivatives `Du i j = ∂ⱼ uᵢ` on the ball, be weakly
divergence free, and satisfy the weak eigenvalue equation
`∫ ∑ᵢⱼ ∂ⱼ uᵢ ∂ⱼ ψᵢ = μ ∫ ⟪u, ψ⟫` against the mode `ψ`. If `μ ≠ (α / R)²` then
`∫ ⟪ψ, u⟫ = 0`: the weak equation of the mode tested with `u` gives the same pairing with the
factor `(α / R)²`. -/
theorem integral_inner_mode_eq_zero_of_weak_eigen {R : ℝ} (hR : 0 < R) {k : ModeKind} {l : ℕ}
    {α μ : ℝ} (hα : boundaryFunction k l α = 0) (hμ : μ ≠ (α / R) ^ 2) {u : ℝ^3 → ℝ^3}
    {Du : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (hu : ∀ i, IntegrableOn (fun x ↦ u x i) (Metric.ball (0 : ℝ^3) R))
    (hDu : ∀ i j, IntegrableOn (Du i j) (Metric.ball (0 : ℝ^3) R))
    (hweak : ∀ i j, SobolevSpace.HasWeakDerivativeOn (Metric.ball (0 : ℝ^3) R) [j]
      (fun x ↦ u x i) (Du i j))
    (hdiv : ∀ᵐ x ∂(volume.restrict (Metric.ball (0 : ℝ^3) R)), ∑ i, Du i i x = 0)
    (heig : ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
        Du i j x * ∂[j] (fun y ↦ mode R k l α y i) x =
      μ * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, mode R k l α x⟫) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ⟪mode R k l α x, u x⟫ = 0 := by
  have h := mode_weak_eigen hR hα hu hDu hweak hdiv
  have hsym : ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
      ∂[j] (fun y ↦ mode R k l α y i) x * Du i j x =
      ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
        Du i j x * ∂[j] (fun y ↦ mode R k l α y i) x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ Finset.sum_congr rfl fun i _ ↦
      Finset.sum_congr rfl fun j _ ↦ mul_comm _ _)
  have hsym' : ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, mode R k l α x⟫ =
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪mode R k l α x, u x⟫ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ real_inner_comm _ _)
  rw [hsym, heig, hsym'] at h
  have h3 : (μ - (α / R) ^ 2) * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪mode R k l α x, u x⟫ = 0 := by
    rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hμ)

/-- A field satisfying the weak eigenvalue equation with eigenvalue `μ ≠ 0` against the zero
mode is orthogonal to `e_z`: the gradient pairing with a constant field vanishes. -/
theorem integral_inner_zeroMode_eq_zero_of_weak_eigen {R μ : ℝ} (hμ : μ ≠ 0) {u : ℝ^3 → ℝ^3}
    {Du : Fin 3 → Fin 3 → ℝ^3 → ℝ}
    (heig : ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
        Du i j x * ∂[j] (fun y ↦ zeroMode y i) x =
      μ * ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, zeroMode x⟫) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ⟪zeroMode x, u x⟫ = 0 := by
  have h0 : ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
      Du i j x * ∂[j] (fun y ↦ zeroMode y i) x = 0 := by
    simp [zeroMode, partialDeriv]
  rw [h0] at heig
  have hsym' : ∫ x in Metric.ball (0 : ℝ^3) R, ⟪u x, zeroMode x⟫ =
      ∫ x in Metric.ball (0 : ℝ^3) R, ⟪zeroMode x, u x⟫ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x ↦ real_inner_comm _ _)
  rw [hsym'] at heig
  exact (mul_eq_zero.mp heig.symm).resolve_left hμ

private theorem frame_inner (θ φ : ℝ) (i j : Fin 3) :
    ⟪frame θ φ i, frame θ φ j⟫ = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp (orthonormal_frame θ φ) i j

private theorem inner_frame_combination (a b a' b' : ℝ) (θ φ : ℝ) :
    ⟪a • radialFrame θ φ + b • polarFrame θ φ, a' • radialFrame θ φ + b' • polarFrame θ φ⟫ =
      a * a' + b * b' := by
  have h00 : ⟪radialFrame θ φ, radialFrame θ φ⟫ = 1 := frame_inner θ φ 0 0
  have h01 : ⟪radialFrame θ φ, polarFrame θ φ⟫ = 0 := frame_inner θ φ 0 1
  have h10 : ⟪polarFrame θ φ, radialFrame θ φ⟫ = 0 := frame_inner θ φ 1 0
  have h11 : ⟪polarFrame θ φ, polarFrame θ φ⟫ = 1 := frame_inner θ φ 1 1
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, h00,
    h01, h10, h11]
  ring

private theorem inner_frame_azimuthal (a b c : ℝ) (θ φ : ℝ) :
    ⟪a • radialFrame θ φ + b • polarFrame θ φ, c • azimuthalFrame φ⟫ = 0 := by
  have h02 : ⟪radialFrame θ φ, azimuthalFrame φ⟫ = 0 := frame_inner θ φ 0 2
  have h12 : ⟪polarFrame θ φ, azimuthalFrame φ⟫ = 0 := frame_inner θ φ 1 2
  simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right, h02, h12]
  ring

private theorem inner_azimuthal_frame (a b c : ℝ) (θ φ : ℝ) :
    ⟪c • azimuthalFrame φ, a • radialFrame θ φ + b • polarFrame θ φ⟫ = 0 := by
  rw [real_inner_comm, inner_frame_azimuthal]

private theorem inner_azimuthal_azimuthal (c c' φ : ℝ) :
    ⟪c • azimuthalFrame φ, c' • azimuthalFrame φ⟫ = c * c' := by
  have h : ⟪azimuthalFrame φ, azimuthalFrame φ⟫ = 1 := frame_inner 0 φ 2 2
  simp only [real_inner_smul_left, real_inner_smul_right, h]
  ring

/-- The zonal harmonics are orthogonal for `sin θ dθ` on `(0, π)`. -/
theorem integral_zonalHarmonic_mul_zonalHarmonic_mul_sin {l l' : ℕ} (hl : l ≠ l') :
    ∫ θ in (0 : ℝ)..π, zonalHarmonic l θ * zonalHarmonic l' θ * sin θ = 0 := by
  have h := integral_legendre_mul_legendre_polarAngleMeasure l l'
  rw [integral_polarAngleMeasure_eq] at h
  simpa [zonalHarmonic, hl] using h

/-- The polar derivatives of the zonal harmonics are orthogonal for `sin θ dθ` on `(0, π)`. -/
theorem integral_zonalHarmonicDeriv_mul_zonalHarmonicDeriv_mul_sin {l l' : ℕ} (hl : l ≠ l') :
    ∫ θ in (0 : ℝ)..π, zonalHarmonicDeriv l θ * zonalHarmonicDeriv l' θ * sin θ = 0 := by
  have h := integral_sin_mul_derivative_legendre_polarAngleMeasure l l'
  rw [integral_polarAngleMeasure_eq] at h
  simpa [zonalHarmonicDeriv, hl] using h

/-- Modes of different kind or different degree are orthogonal in `L²(B(0, R))`, for every
`α` and `α'`. -/
theorem integral_inner_mode_eq_zero_of_ne (R : ℝ) {k k' : ModeKind} {l l' : ℕ}
    (α α' : ℝ) (hne : (k, l) ≠ (k', l')) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ⟪mode R k l α x, mode R k' l' α' x⟫ = 0 := by
  have hrot : IsInvariantUnderAxisRotation fun x ↦ ⟪mode R k l α x, mode R k' l' α' x⟫ := by
    intro φ x
    simp only [mode_axisRotation, inner_axisRotation_axisRotation]
  have hcont : Continuous fun x ↦ ⟪mode R k l α x, mode R k' l' α' x⟫ :=
    (mode_contDiff R k l α).continuous.inner (mode_contDiff R k' l' α').continuous
  have hint : IntegrableOn (fun x ↦ ⟪mode R k l α x, mode R k' l' α' x⟫)
      (Metric.ball (0 : ℝ^3) R) :=
    (hcont.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set
      Metric.ball_subset_closedBall
  rw [setIntegral_ball_of_axisymmetric hrot hint]
  have hS (m : ℕ) : Continuous (zonalHarmonic m) := continuous_zonalHarmonic m
  have hD (m : ℕ) : Continuous (zonalHarmonicDeriv m) := continuous_zonalHarmonicDeriv m
  have hzero : ∀ r, ∫ θ in (0 : ℝ)..π, ⟪mode R k l α (point r θ 0),
      mode R k' l' α' (point r θ 0)⟫ * r ^ 2 * sin θ = 0 := by
    intro r
    cases k <;> cases k'
    · have hl : l ≠ l' := fun h ↦ hne (by rw [h])
      simp only [mode_meridional_point, inner_frame_combination]
      have hfun : (fun θ ↦ (meridionalRadialProfile R l α r * zonalHarmonic l θ *
          (meridionalRadialProfile R l' α' r * zonalHarmonic l' θ) +
          meridionalPolarProfile R l α r * zonalHarmonicDeriv l θ *
            (meridionalPolarProfile R l' α' r * zonalHarmonicDeriv l' θ)) * r ^ 2 * sin θ) =
          fun θ ↦ (meridionalRadialProfile R l α r * meridionalRadialProfile R l' α' r * r ^ 2) *
              (zonalHarmonic l θ * zonalHarmonic l' θ * sin θ) +
            (meridionalPolarProfile R l α r * meridionalPolarProfile R l' α' r * r ^ 2) *
              (zonalHarmonicDeriv l θ * zonalHarmonicDeriv l' θ * sin θ) := by
        funext θ
        ring
      rw [hfun, intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        integral_zonalHarmonic_mul_zonalHarmonic_mul_sin hl,
        integral_zonalHarmonicDeriv_mul_zonalHarmonicDeriv_mul_sin hl, mul_zero, mul_zero,
        add_zero]
      · exact (continuous_const.mul (((hS l).mul (hS l')).mul continuous_sin)).intervalIntegrable
          _ _
      · exact (continuous_const.mul (((hD l).mul (hD l')).mul continuous_sin)).intervalIntegrable
          _ _
    · simp only [mode_meridional_point, mode_azimuthal_point, inner_frame_azimuthal, zero_mul,
        intervalIntegral.integral_zero]
    · simp only [mode_meridional_point, mode_azimuthal_point, inner_azimuthal_frame, zero_mul,
        intervalIntegral.integral_zero]
    · have hl : l ≠ l' := fun h ↦ hne (by rw [h])
      simp only [mode_azimuthal_point, inner_azimuthal_azimuthal]
      have hfun : (fun θ ↦ azimuthalProfile R l α r * zonalHarmonicDeriv l θ *
          (azimuthalProfile R l' α' r * zonalHarmonicDeriv l' θ) * r ^ 2 * sin θ) =
          fun θ ↦ (azimuthalProfile R l α r * azimuthalProfile R l' α' r * r ^ 2) *
            (zonalHarmonicDeriv l θ * zonalHarmonicDeriv l' θ * sin θ) := by
        funext θ
        ring
      rw [hfun, intervalIntegral.integral_const_mul,
        integral_zonalHarmonicDeriv_mul_zonalHarmonicDeriv_mul_sin hl, mul_zero]
  simp only [hzero, integral_zero, mul_zero]

/-- Distinct modes with nonnegative boundary roots are orthogonal in `L²(B(0, R))`. -/
theorem mode_orthogonal {R : ℝ} (hR : 0 < R) {k k' : ModeKind} {l l' : ℕ} {α α' : ℝ}
    (hα : boundaryFunction k l α = 0) (hα' : boundaryFunction k' l' α' = 0) (h0 : 0 ≤ α)
    (h0' : 0 ≤ α') (hne : (k, l, α) ≠ (k', l', α')) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ⟪mode R k l α x, mode R k' l' α' x⟫ = 0 := by
  by_cases hkl : (k, l) = (k', l')
  · refine integral_inner_mode_eq_zero_of_sq_ne hR hα hα' fun hsq ↦ hne ?_
    have hαα : α = α' := (sq_eq_sq₀ h0 h0').mp hsq
    simp only [Prod.mk.injEq] at hkl
    rw [hkl.1, hkl.2, hαα]
  · exact integral_inner_mode_eq_zero_of_ne R α α' hkl

/-- Distinct modes with nonnegative boundary roots are orthogonal for the gradient pairing on
`B(0, R)`. -/
theorem mode_gradient_orthogonal {R : ℝ} (hR : 0 < R) {k k' : ModeKind} {l l' : ℕ} {α α' : ℝ}
    (hα : boundaryFunction k l α = 0) (hα' : boundaryFunction k' l' α' = 0) (h0 : 0 ≤ α)
    (h0' : 0 ≤ α') (hne : (k, l, α) ≠ (k', l', α')) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ∑ i, ∑ j,
        ∂[j] (fun y ↦ mode R k l α y i) x * ∂[j] (fun y ↦ mode R k' l' α' y i) x = 0 := by
  have h := mode_orthogonal hR hα hα' h0 h0' hne
  rw [mode_weak_eigen_of_contDiff hR hα (contDiff_one_mode R k' l' α')
    (fun x _ ↦ mode_divergence_eq_zero R k' l' α' x), h, mul_zero]

/-- A mode of nonzero boundary root is orthogonal to the zero mode `e_z` in `L²(B(0, R))`. -/
theorem integral_inner_mode_zeroMode {R : ℝ} (hR : 0 < R) {k : ModeKind} {l : ℕ} {α : ℝ}
    (hα : boundaryFunction k l α = 0) (hα0 : α ≠ 0) :
    ∫ x in Metric.ball (0 : ℝ^3) R, ⟪mode R k l α x, zeroMode x⟫ = 0 := by
  have h := mode_weak_eigen_of_contDiff hR hα (zeroMode_contDiff.of_le (by exact_mod_cast le_top))
    (fun x _ ↦ zeroMode_divergence_eq_zero x)
  have hz (i j : Fin 3) (x : ℝ^3) : ∂[j] (fun y ↦ zeroMode y i) x = 0 := by
    simp [zeroMode, partialDeriv]
  simp only [hz, mul_zero, Finset.sum_const_zero, integral_zero] at h
  have hκ : (α / R) ^ 2 ≠ 0 := pow_ne_zero 2 (div_ne_zero hα0 hR.ne')
  exact (mul_eq_zero.mp h.symm).resolve_left hκ

end PDE.Fluid.Stokes.Ball
