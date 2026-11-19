/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.Nonconcentration.TerminalFlux
public import PDE.Hyperbolic.NonlinearWave.Morawetz.ConeProfile.Energy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Slice potential controlled by a radial square

The quintic equation supplies integrability of the scaling current. Removing its terminal cap, using
the exact cone-profile radial identity, and bounding the initial cap control the sixth-power slice
integral by a weighted radial square. Regularity is only on the open forward time band.

This is the first inequality of (15) in the proof of Evans, §12.4, Theorem 2: (9), (10) and (14)
together bound the sixth-power slice integral by the weighted square
`∫_Γ (T - t) |u_r - u_t + u/|x||² dS` on the cone.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.4, proof of Theorem 2, equations (9), (10), (14)
  and (15).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory PDE PDE.Common PDE.Analysis NormedSpace
open scoped RealInnerProductSpace Topology

namespace WaveEquation

/-- The equation bounds the full lateral scaling current by its initial cap.
Finite energy provides integrability. -/
theorem integral_scalingFlux_le_initialCap_of_wave {u : ℝ^4 → ℝ} {s T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3) (hs : 0 < s) (hsT : s < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0) :
    (∫ x in Metric.ball c (T - s),
      coneProfileScalingFlux (Real.signedPowerPotential 5) 1 T c u x) ≤
      ballIntegral 3 (fun x ↦
        scalingCurrentDensity (Real.signedPowerPotential 5) 1 (timeSpaceCons T c) u
          (timeSpaceCons s x)) c (T - s) := by
  obtain ⟨hG, hW⟩ := ConeProfile.integrable_densities_of_wave hu c hs
    (fun t ht ↦ hwave t ⟨hs.trans_le ht.1, ht.2⟩)
  obtain ⟨hD, hcross, _⟩ := ConeProfile.integrable_radial_terms (by omega : 3 ≤ 3) (sub_pos.mpr hsT)
    (fun _ hx hne ↦ ConeProfile.contDiffAt_cone_of_band hu hs c
      (Metric.ball_subset_closedBall hx) hne) hG hW
  apply integral_scalingFlux_le_initialCap_of_integrable hu c hs hsT hwave
  apply (hD.neg.sub hcross).congr
  filter_upwards [ae_restrict_of_ae (volume.ae_ne c)] with x hx
  simpa only [coneProfileScalingFlux, backwardConeGraph, one_mul, neg_mul,
    Pi.sub_apply, Pi.neg_apply] using
    (coneProfileScalingFlux_eq (Real.signedPowerPotential 5) 1 T c u hx).symm

/-- Initial potential energy on a shrinking ball is controlled by the
weighted radial square on its future cone. All integrability follows from the PDE. -/
theorem ballIntegral_quinticPotential_le_weightedSquare_of_wave {u : ℝ^4 → ℝ} {s T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3) (hs : 0 < s) (hsT : s < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator u (timeSpaceCons t x) + u (timeSpaceCons t x) ^ 5 = 0) :
    (T - s) * (∫ x in Metric.ball c (T - s), u (timeSpaceCons s x) ^ 6) / 6 ≤
      ∫ x in Metric.ball c (T - s), ‖x - c‖ *
      (⟪coneProfileGradient T c u x, normalize (x - c)⟫ + coneProfile T c u x / ‖x - c‖) ^ 2 := by
  have hcurrent := integral_scalingFlux_le_initialCap_of_wave hu c hs hsT hwave
  have hexact := ConeProfile.integral_scalingFlux_eq_boundary_sub_square_of_wave hu c hs hsT
    (fun t ht ↦ hwave t ⟨hs.trans_le ht.1, ht.2⟩)
  have hboundary : sphereIntegral 3 (fun x ↦ coneProfile T c u x ^ 2) c (T - s) =
      sphereIntegral 3 (fun x ↦ u (timeSpaceCons s x) ^ 2) c (T - s) := by
    refine sphereIntegral_congr_on_sphere (sub_pos.mpr hsT) fun x hx ↦ ?_
    have hρ : ‖x - c‖ = T - s := by simpa only [Metric.mem_sphere, dist_eq_norm] using hx
    simp only [coneProfile, hρ, sub_sub_cancel]
  rw [hboundary] at hexact
  have hopen : IsOpen {p : ℝ^4 | 0 < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hcap := ballIntegral_scalingCurrentDensity_le
    (Real.contDiff_one_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5)).continuous
    T s c hsT (fun x ↦ hu.contDiffAt (hopen.mem_nhds
      (by simpa only [mem_ofPred_eq, timeSpaceCons_zero] using And.intro hs hsT)))
  have hpot : ballIntegral 3
      (fun x ↦ Real.signedPowerPotential 5 (u (timeSpaceCons s x))) c (T - s) =
        (∫ x in Metric.ball c (T - s), u (timeSpaceCons s x) ^ 6) / 6 := by
    unfold ballIntegral
    simp only [Real.signedPowerPotential]
    norm_num [Real.rpow_ofNat, (show Even 6 by decide).pow_abs, integral_div]
  rw [hpot] at hcap
  have hcorrection : 0 ≤ ((3 : ℝ) - 1) / (2 * (T - s)) *
      ballIntegral 3 (fun x ↦ u (timeSpaceCons s x) ^ 2) c (T - s) := by
    apply mul_nonneg (by positivity)
    exact integral_nonneg fun x ↦ sq_nonneg _
  linarith

end WaveEquation
