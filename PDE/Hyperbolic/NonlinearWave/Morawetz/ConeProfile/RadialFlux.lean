/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.ConeProfile.Sobolev
public import PDE.Analysis.Integration.RadialSquareFlux.Translated

/-!
# Radial square flux of a cone profile

Finite cone densities give Sobolev membership. The Hardy-based radial identity
then applies without any regularity or limiting value at the tip.
-/

@[expose] public noncomputable section

open MeasureTheory Metric PDE PDE.Common PDE.Analysis NormedSpace
open scoped RealInnerProductSpace

namespace WaveEquation.ConeProfile

/-- The cone-profile square flux in dimension at least three, from integrated densities. -/
theorem radial_square_flux {n : ℕ} (hn : 3 ≤ n) {T r : ℝ} {c : ℝ^n} {u : ℝ^(n + 1) → ℝ} (hr : 0 < r)
    (hu : ∀ x ∈ closedBall c r, x ≠ c → ContDiffAt ℝ 1 u (timeSpaceCons (T - ‖x - c‖) x))
    (hgradient : IntegrableOn (fun x ↦ ‖coneProfileGradient T c u x‖ ^ 2) (ball c r))
    (hpotential : IntegrableOn (fun x ↦ coneProfile T c u x ^ 6) (ball c r)) :
    ((n : ℝ) - 1) * (∫ x in ball c r, coneProfile T c u x ^ 2 / ‖x - c‖) + 2 *
      (∫ x in ball c r, coneProfile T c u x * ⟪coneProfileGradient T c u x, normalize (x - c)⟫) =
      sphereIntegral n (fun x ↦ coneProfile T c u x ^ 2) c r := by
  obtain ⟨U, hU, _⟩ := exists_h1_of_integrable_densities (by omega : 2 ≤ n)
    (fun x hx hne ↦ hu x (ball_subset_closedBall hx) hne) hgradient hpotential
  have h := PDE.Analysis.RadialSquareFlux.radial_square_flux_of_h1_at hn hr U
    (fun x hx hne ↦ contDiffAt_coneProfile hne (hu x hx hne)) hU
  have he : (∫ x in ball c r, coneProfile T c u x *
      fderiv ℝ (coneProfile T c u) x (normalize (x - c))) = ∫ x in ball c r, coneProfile T c u x *
        ⟪coneProfileGradient T c u x, normalize (x - c)⟫ := by
    let : Nontrivial (ℝ^n) := Module.nontrivial_of_finrank_pos (R := ℝ)
      (by simpa using (show 0 < n by omega))
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet,
      ae_restrict_of_ae (volume.ae_ne c)] with x hx hne
    rw [fderiv_coneProfile_apply_eq_inner hne
      ((hu x (ball_subset_closedBall hx) hne).differentiableAt one_ne_zero)]
  rwa [he] at h

/-- In three dimensions the cone profile yields the half-sphere square term. -/
theorem radial_square_flux_three {T r : ℝ} {c : ℝ^3} {u : ℝ^4 → ℝ} (hr : 0 < r)
    (hu : ∀ x ∈ closedBall c r, x ≠ c → ContDiffAt ℝ 1 u (timeSpaceCons (T - ‖x - c‖) x))
    (hgradient : IntegrableOn (fun x ↦ ‖coneProfileGradient T c u x‖ ^ 2) (ball c r))
    (hpotential : IntegrableOn (fun x ↦ coneProfile T c u x ^ 6) (ball c r)) :
    (∫ x in ball c r, coneProfile T c u x ^ 2 / ‖x - c‖) + (∫ x in ball c r,
      coneProfile T c u x * ⟪coneProfileGradient T c u x, normalize (x - c)⟫) =
      (1 / 2 : ℝ) * sphereIntegral 3 (fun x ↦ coneProfile T c u x ^ 2) c r := by
  have h := radial_square_flux (by omega : 3 ≤ 3) hr hu hgradient hpotential
  norm_num at h
  linarith

end WaveEquation.ConeProfile
