/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.AncientForward
public import PDE.Fluid.NavierStokes.Nonuniqueness.AncientFamilyEquation
public import PDE.Fluid.NavierStokes.Selfsimilar.ProfileMild

/-!
# The ancient correction in forward mild form

The ancient correction `U_cor` of an unstable profile at cutoff radius `R` solves the mixed
identity (2.15) of Hou, Wang and Yang: the homogeneous unstable part
`e^{μτ} s c₀ e`, plus the past integral of the stable kernel, minus the future integral of the
unstable kernel, against the forcing `N = F + L_far U_cor - (U_cor·∇)U_cor` of (2.11). This
identity determines `U_cor` on the whole half-line `τ ≤ 0` at once. We turn it into forward
equations that start at any time `σ ≤ 0`.

The profile evolution `S` on vector `H³` continues the stable kernel, `S(t) Ks(r) = Ks(t + r)`,
the unstable kernel, `S(t) Ku(r) = Ku(r - t)`, and the eigenvector, `S(t) e = e^{μt} e`, and at
positive lag `Ks(r) + Ku(-r) = S(r) Π` with the gain `S(r)` from vector `H²`. So for
`σ ≤ τ ≤ 0` (`forwardMild_of_mixed`)

`U_cor(τ) = S(τ - σ) U_cor(σ) + ∫_σ^τ S(τ - r) (Π N(r)) dr`.

Moving the transport `B` of the linearization at the profile into the forcing gives the forward
equation of the free self-similar evolution `S₀` (`forwardFreeMild_of_forwardMild`),

`U_cor(τ) = S₀(τ - σ) U_cor(σ) + ∫_σ^τ Π S₀(τ - r) (N(r) - B U_cor(r)) dr`,

with the projected free gain `Π S₀(r)` from vector `H²` to vector `H³`. This is the form in
which the parabolic smoothing of forward mild solutions applies.

Both forms hold for every fixed point `u = b c + G (N u)` of the ancient equation, with no
threshold on the cutoff radius (`forwardMild_of_fixedPoint`, `forwardFreeMild_of_fixedPoint`).
The ancient correction is the fixed point in the ball of radius `r` above the threshold.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 2.2, (2.11), p. 12, (2.15),
  p. 13, and the smoothness of the solutions for positive times, p. 15.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace HeatEquation.WholeSpace
open IncompressibleFlow PDE.Analysis.Evolution NavierStokes.SobolevConvection
open NavierStokes.Selfsimilar
open scoped NNReal Sobolev BoundedContinuousFunction

namespace NavierStokes.Nonuniqueness

/-- The forcing of (2.11) along a continuous path in vector `H³` is continuous. -/
theorem continuous_correctionForcing (D : UnstableProfile) (R : ℝ) {v : ℝ → VectorH 3 3}
    (hv : Continuous v) : Continuous (correctionForcing D R v) :=
  ((continuous_cutoffForcing D R 2).add ((continuous_cutoffCoefficient D R 2).clm_apply hv)).sub
    ((convection.continuous.comp hv).clm_apply hv)

variable {D : UnstableProfile} {R s : ℝ}

/-- At every time `t ≤ 0` the stable kernel against the forcing of (2.11) along the decoded
path of any `u` is integrable over positive lags. -/
theorem integrableOn_Ks_correctionForcing_ancientLift (u : Iic (0 : ℝ) →ᵇ VectorH 3 3) {t : ℝ}
    (ht : t ≤ 0) :
    IntegrableOn (fun r ↦ D.dichotomy.Ks r (correctionForcing D R
      (ancientLift D.dichotomy.η u) (t - r))) (Ioi 0) := by
  have h := integrableOn_ancientLift_of_joint (β := 2 * D.dichotomy.η)
    (by norm_num : (1 / 2 : ℝ) < 1) D.dichotomy.ω_lt D.dichotomy.Ms_nonneg
    D.dichotomy.continuousOn_Ks D.dichotomy.norm_Ks_le (ancientForcing D R u) t
  refine h.congr_fun (fun r hr ↦ ?_) measurableSet_Ioi
  dsimp only
  rw [ancientLift_ancientForcing _ (by linarith [mem_Ioi.mp hr])]

/-- At every time `t ≤ 0` the stable kernel against the forcing of the ancient correction is
integrable over positive lags. -/
theorem integrableOn_Ks_correctionForcing {t : ℝ} (ht : t ≤ 0) :
    IntegrableOn (fun r ↦ D.dichotomy.Ks r (correctionForcing D R
      (ancientLift D.dichotomy.η (ancientCorrection D R s)) (t - r))) (Ioi 0) :=
  integrableOn_Ks_correctionForcing_ancientLift _ ht

/-- **Fixed points of the ancient equation in forward mild form.** Every path `u` with
`u = b c + G (N u)` decodes, for `σ ≤ τ ≤ 0`, to a solution of the forward equation of the
profile evolution `S` on vector `H³` with the gain `S(r)` from vector `H²` and the forcing `N` of
(2.11),

`U(τ) = S(τ - σ) U(σ) + ∫_σ^τ S(τ - r) (Π N(r)) dr`. -/
theorem forwardMild_of_fixedPoint {c : ℝ} {u : Iic (0 : ℝ) →ᵇ VectorH 3 3}
    (hu : u = D.dichotomy.b c + D.ancientGreen (ancientForcing D R u))
    (σ τ : ℝ) (hστ : σ ≤ τ) (hτ : τ ≤ 0) :
    ancientLift D.dichotomy.η u τ =
      profileSemigroup 3 D.transportCoefficients D.stretchingCoefficients
          (D.profileCoefficientBounds 3) (τ - σ).toNNReal (ancientLift D.dichotomy.η u σ) +
        ∫ r in σ..τ, profileGain 2 D.transportCoefficients D.stretchingCoefficients
          (D.profileCoefficientBounds 2) (τ - r)
          (leraySobolev 3 2 (correctionForcing D R (ancientLift D.dichotomy.η u) r)) := by
  have hF := continuous_correctionForcing D R (ancientLift D.dichotomy.η u).continuous
  refine (eq_add_intervalIntegral_of_mixed
    (T := profileSemigroup 3 D.transportCoefficients D.stretchingCoefficients
      (D.profileCoefficientBounds 3))
    (G := fun r ↦ (profileGain 2 D.transportCoefficients D.stretchingCoefficients
      (D.profileCoefficientBounds 2) r).comp (leraySobolev 3 2))
    (h := fun t ↦ Real.exp (D.dichotomy.μ * t) • (c • D.dichotomy.e))
    D.dichotomy.semigroup_Ks D.dichotomy.semigroup_Ku
    (fun r hr x ↦
      (D.dichotomy.Ks_add_Ku_neg hr x).trans (ContinuousLinearMap.comp_apply _ _ _).symm)
    (fun t s' ↦ ?_) (fun t ht ↦ integrableOn_Ks_correctionForcing_ancientLift u ht)
    D.dichotomy.continuous_Ku hF.continuousOn (fun t ht ↦ ancientLift_eq_of_fixedPoint hu ht)
    hστ hτ).trans ?_
  · rw [map_smul, map_smul, D.dichotomy.semigroup_e, smul_comm c, smul_smul, ← Real.exp_add,
      mul_add]
  · simp only [ContinuousLinearMap.comp_apply]

/-- **Fixed points of the ancient equation in free forward mild form.** Every path `u` with
`u = b c + G (N u)` decodes, for `σ ≤ τ ≤ 0`, to a solution of the forward equation of the free
self-similar evolution `S₀` on vector `H³` with the projected free gain `Π S₀(r)` from vector
`H²`, the forcing `N` of (2.11) and the transport `B` of the linearization at the profile,

`U(τ) = S₀(τ - σ) U(σ) + ∫_σ^τ Π S₀(τ - r) (N(r) - B U(r)) dr`. -/
theorem forwardFreeMild_of_fixedPoint {c : ℝ} {u : Iic (0 : ℝ) →ᵇ VectorH 3 3}
    (hu : u = D.dichotomy.b c + D.ancientGreen (ancientForcing D R u))
    (σ τ : ℝ) (hστ : σ ≤ τ) (hτ : τ ≤ 0) :
    ancientLift D.dichotomy.η u τ =
      vectorSelfsimilarHeat 3 3 (τ - σ).toNNReal (ancientLift D.dichotomy.η u σ) +
        ∫ r in σ..τ, projectedSelfsimilarHeatGainKernel 3 2 (τ - r)
          (correctionForcing D R (ancientLift D.dichotomy.η u) r -
            (D.profileCoefficientBounds 2).transport (ancientLift D.dichotomy.η u r)) :=
  eq_freeMild_of_profileMild (D.profileCoefficientBounds 2) (D.profileCoefficientBounds 3) hστ
    (ancientLift D.dichotomy.η u).continuous.continuousOn
    (continuous_correctionForcing D R (ancientLift D.dichotomy.η u).continuous).continuousOn
    fun t ht ↦ forwardMild_of_fixedPoint hu σ t ht.1 (ht.2.trans hτ)

variable (D R s)

/-- **The ancient correction in forward mild form.** Above the threshold radius and for
`s ∈ [0, 1]`, the ancient correction `U_cor = ancientLift η (ancientCorrection D R s)` solves,
for `σ ≤ τ ≤ 0`, the forward equation of the profile evolution `S` on vector `H³` with the gain
`S(r)` from vector `H²` and the forcing `N` of (2.11),

`U_cor(τ) = S(τ - σ) U_cor(σ) + ∫_σ^τ S(τ - r) (Π N(r)) dr`. -/
theorem forwardMild_of_mixed (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    (σ τ : ℝ) (hστ : σ ≤ τ) (hτ : τ ≤ 0) :
    ancientLift D.dichotomy.η (ancientCorrection D R s) τ =
      profileSemigroup 3 D.transportCoefficients D.stretchingCoefficients
          (D.profileCoefficientBounds 3) (τ - σ).toNNReal
          (ancientLift D.dichotomy.η (ancientCorrection D R s) σ) +
        ∫ r in σ..τ, profileGain 2 D.transportCoefficients D.stretchingCoefficients
          (D.profileCoefficientBounds 2) (τ - r)
          (leraySobolev 3 2 (correctionForcing D R
            (ancientLift D.dichotomy.η (ancientCorrection D R s)) r)) :=
  forwardMild_of_fixedPoint (ancientCorrection_spec hR hs).2 σ τ hστ hτ

/-- **The ancient correction in free forward mild form.** Above the threshold radius and for
`s ∈ [0, 1]`, the ancient correction `U_cor` solves, for `σ ≤ τ ≤ 0`, the forward equation of the
free self-similar evolution `S₀` on vector `H³` with the projected free gain `Π S₀(r)` from vector
`H²`, the forcing `N` of (2.11) and the transport `B` of the linearization at the profile,

`U_cor(τ) = S₀(τ - σ) U_cor(σ) + ∫_σ^τ Π S₀(τ - r) (N(r) - B U_cor(r)) dr`. -/
theorem forwardFreeMild_of_forwardMild (hR : D.ancientThreshold ≤ R) (hs : s ∈ Icc (0 : ℝ) 1)
    (σ τ : ℝ) (hστ : σ ≤ τ) (hτ : τ ≤ 0) :
    ancientLift D.dichotomy.η (ancientCorrection D R s) τ =
      vectorSelfsimilarHeat 3 3 (τ - σ).toNNReal
          (ancientLift D.dichotomy.η (ancientCorrection D R s) σ) +
        ∫ r in σ..τ, projectedSelfsimilarHeatGainKernel 3 2 (τ - r)
          (correctionForcing D R (ancientLift D.dichotomy.η (ancientCorrection D R s)) r -
            (D.profileCoefficientBounds 2).transport
              (ancientLift D.dichotomy.η (ancientCorrection D R s) r)) :=
  forwardFreeMild_of_fixedPoint (ancientCorrection_spec hR hs).2 σ τ hστ hτ

end NavierStokes.Nonuniqueness
