/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.Burgers.Riemann.Profiles
public import PDE.Hyperbolic.ConservationLaw.Scalar.Entropy.AffineFan

/-!
# Boundary Integrals for Burgers Rarefaction Fans

The self-similar state `u(t, x) = x / t` and every entropy pair derived from it
form a smooth conservative pair on `t > 0`. We specialize the general
affine-interface and affine-fan integration theorems to those pairs.

The single-interface formulas expose the boundary flux at `x = s t`. The
whole-fan formulas show that the left, middle, and right boundary terms cancel
when the middle profile has the prescribed endpoint traces.
-/

@[expose] public section

namespace BurgersEquation.Riemann

noncomputable section

open PDE.Hyperbolic.ConservationLaw.Scalar
open MeasureTheory
open PDE.Common
open PDE.Hyperbolic.ConservationLaw

open scoped Distributions

private theorem ratio_interface (s t : ℝ) (ht : t ≠ 0) :
    ratio (AffineInterface.interface s t) = s := by
  simp [ratio, AffineInterface.interface, ht]

private theorem contDiffAt_flux_ratio {p : ℝ^2} (ht : p 0 ≠ 0) :
    ContDiffAt ℝ 1 (fun x : ℝ^2 ↦ flux (ratio x)) p := by
  have hflux : ContDiffAt ℝ 1 flux (ratio p) := by
    unfold flux
    fun_prop
  exact hflux.comp p (contDiffAt_ratio ht)

private theorem entropy_conservation_ratio
    (E : PDE.Hyperbolic.ConservationLaw.Scalar.EntropyPair (fun r : ℝ ↦ deriv flux r))
    {p : ℝ^2} (ht : p 0 ≠ 0) :
    (∂[(0 : Fin 2)] (fun x : ℝ^2 ↦ E.η (ratio x))) p +
        (∂[(1 : Fin 2)] (fun x : ℝ^2 ↦ E.q (ratio x))) p = 0 := by
  have hpde : (∂[(0 : Fin 2)] ratio) p + (fun r : ℝ ↦ deriv flux r) (ratio p) *
            (∂[(1 : Fin 2)] ratio) p = 0 := by
    simpa [deriv_flux] using pde_ratio p ht
  exact _root_.PDE.Hyperbolic.ConservationLaw.Scalar.entropy_identity_of_pde E
    (differentiableAt_ratio ht) hpde

/-- The Burgers flux of the self-similar ratio reduces to its
affine-interface trace. -/
theorem setIntegral_ratio_leftHalfSpace (φ : 𝓓^{1}(forwardHalfSpace, ℝ)) (s : ℝ) :
    (∫ p in AffineInterface.leftHalfSpace s, (ratio p * (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p +
      flux (ratio p) * (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p) ∂volume) = (flux s - s * s) * ∫ t : ℝ,
      φ (AffineInterface.interface s t) ∂volume := by
  apply AffineFan.setIntegral_conservative_pair_leftHalfSpace
      φ s ratio (fun p : ℝ^2 ↦ flux (ratio p)) (fun p hp ↦ contDiffAt_ratio (ne_of_gt hp))
      (fun _ hp ↦ contDiffAt_flux_ratio (ne_of_gt hp))
      (fun p hp ↦ conservation_ratio p (ne_of_gt hp)) s (flux s)
  · exact fun t ht ↦ ratio_interface s t (ne_of_gt ht)
  · intro t ht
    rw [ratio_interface s t (ne_of_gt ht)]

/-- Every Burgers entropy pair of the self-similar ratio reduces to its
affine-interface trace. -/
theorem setIntegral_entropy_ratio_leftHalfSpace (φ : 𝓓^{1}(forwardHalfSpace, ℝ))
    (E : PDE.Hyperbolic.ConservationLaw.Scalar.EntropyPair (fun r : ℝ ↦ deriv flux r)) (s : ℝ) :
    (∫ p in AffineInterface.leftHalfSpace s,
        (E.η (ratio p) *
            (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p +
          E.q (ratio p) *
            (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p) ∂volume) =
      (E.q s - s * E.η s) *
        ∫ t : ℝ, φ (AffineInterface.interface s t) ∂volume := by
  apply AffineFan.setIntegral_conservative_pair_leftHalfSpace φ s (fun p : ℝ^2 ↦ E.η (ratio p))
      (fun p : ℝ^2 ↦ E.q (ratio p)) (fun p hp ↦ E.eta_contDiff.contDiffAt.comp p
        (contDiffAt_ratio (ne_of_gt hp))) (fun p hp ↦ E.entropyFlux_contDiff.contDiffAt.comp p
        (contDiffAt_ratio (ne_of_gt hp))) (fun _ hp ↦ entropy_conservation_ratio E (ne_of_gt hp))
      (E.η s) (E.q s)
  · intro t ht
    rw [ratio_interface s t (ne_of_gt ht)]
  · intro t ht
    rw [ratio_interface s t (ne_of_gt ht)]

/-- The constant states and self-similar Burgers profile form a conservative
pair across an ordered affine fan. -/
theorem integral_ratio_affine_fan_eq_zero (φ : 𝓓^{1}(forwardHalfSpace, ℝ)) {uL uR : ℝ}
    (h : uL ≤ uR) :
    (∫ p : ℝ^2, (AffineFan.profile uL uR uL ratio uR p * (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p +
      AffineFan.profile uL uR (flux uL) (fun x : ℝ^2 ↦ flux (ratio x)) (flux uR) p *
      (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p) ∂volume) = 0 := by
  apply AffineFan.integral_conservative_pair_profile_eq_zero
      φ uL uR h ratio (fun p : ℝ^2 ↦ flux (ratio p)) uL (flux uL) uR (flux uR)
      (fun p hp ↦ contDiffAt_ratio (ne_of_gt hp)) (fun _ hp ↦ contDiffAt_flux_ratio (ne_of_gt hp))
      (fun p hp ↦ conservation_ratio p (ne_of_gt hp.1))
  · exact fun t ht ↦ ratio_interface uL t (ne_of_gt ht)
  · intro t ht
    rw [ratio_interface uL t (ne_of_gt ht)]
  · exact fun t ht ↦ ratio_interface uR t (ne_of_gt ht)
  · intro t ht
    rw [ratio_interface uR t (ne_of_gt ht)]

/-- Composing the self-similar Burgers fan with an entropy pair gives a
globally conservative entropy pair. -/
theorem integral_entropy_ratio_affine_fan_eq_zero (φ : 𝓓^{1}(forwardHalfSpace, ℝ))
    (E : PDE.Hyperbolic.ConservationLaw.Scalar.EntropyPair (fun r : ℝ ↦ deriv flux r)) {uL uR : ℝ}
    (h : uL ≤ uR) :
    (∫ p : ℝ^2,
        (AffineFan.profile uL uR (E.η uL)
              (fun x : ℝ^2 ↦ E.η (ratio x)) (E.η uR) p *
            (∂[(0 : Fin 2)] (φ : ℝ^2 → ℝ)) p +
          AffineFan.profile uL uR (E.q uL)
              (fun x : ℝ^2 ↦ E.q (ratio x)) (E.q uR) p *
            (∂[(1 : Fin 2)] (φ : ℝ^2 → ℝ)) p) ∂volume) = 0 := by
  apply E.integral_affineFan_eq_zero φ h (fun _ hp ↦ contDiffAt_ratio (ne_of_gt hp))
  · intro p hp
    simpa only [deriv_flux] using pde_ratio p (ne_of_gt hp.1)
  · exact fun t ht ↦ ratio_interface uL t (ne_of_gt ht)
  · exact fun t ht ↦ ratio_interface uR t (ne_of_gt ht)

end

end BurgersEquation.Riemann
