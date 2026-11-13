/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.ExteriorKernel
public import PDE.Hyperbolic.Models.Wave.Strichartz.NewtonShell
public import PDE.Hyperbolic.Models.Wave.Strichartz.ShellProfile

/-!
# The integrated Newtonian spherical mean

The spherical shell identity holds off the characteristic sphere, whose volume
is zero. Differentiating the resulting integral against an L¹ datum gives the
exterior Newtonian convolution, including translation of its center.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology
open PDE.Analysis

namespace WaveEquation.Strichartz

/-- Off the characteristic sphere, time times the Newtonian spherical mean is the shell profile. -/
theorem mul_unitSphereAverage_inv_norm_eq_profile {x : ℝ^3} {t : ℝ} (ht : 0 < t) (hxt : ‖x‖ ≠ t) :
    t * unitSphereAverage 3 (fun y : ℝ^3 ↦ ‖y‖⁻¹) x t = t / max t ‖x‖ := by
  rcases lt_or_gt_of_ne hxt with h | h
  · rw [unitSphereAverage_inv_norm_of_norm_lt ht h, max_eq_left h.le,
      mul_inv_cancel₀ ht.ne', div_self ht.ne']
  · rw [unitSphereAverage_inv_norm_of_lt ht h, max_eq_right h.le, div_eq_mul_inv]

/-- Integrating the Newtonian spherical mean removes the exceptional characteristic sphere. -/
theorem integral_mul_unitSphereAverage_inv_norm_eq_profile (f : ℝ^3 → ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ y, (t * unitSphereAverage 3 (fun z : ℝ^3 ↦ ‖z‖⁻¹) y t) * f y) =
      ∫ y, (t / max t ‖y‖) * f y := by
  apply integral_congr_ae
  have hnull : ∀ᵐ y : ℝ^3, y ∉ Metric.sphere 0 t := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using
      Measure.addHaar_sphere_of_ne_zero (volume : Measure (ℝ^3)) 0 ht.ne'
  filter_upwards [hnull] with y hy
  rw [mul_unitSphereAverage_inv_norm_eq_profile ht (fun h ↦ hy (mem_sphere_zero_iff_norm.mpr h))]

/-- Differentiating the integrated Newtonian spherical mean gives an exterior convolution. -/
theorem hasDerivAt_integral_mul_unitSphereAverage_inv_norm {f : ℝ^3 → ℝ}
    (hf : Integrable f) (x : ℝ^3) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ ∫ y, (s * unitSphereAverage 3 (fun z : ℝ^3 ↦ ‖z‖⁻¹) y s) * f (x - y))
      (∫ y, exteriorNewtonKernel t (x - y) * f y) t := by
  have h := hasDerivAt_integral_shell_profile (hf.comp_sub_left x) ht
  have heq : (fun s ↦ ∫ y,
      (s * unitSphereAverage 3 (fun z : ℝ^3 ↦ ‖z‖⁻¹) y s) * f (x - y)) =ᶠ[nhds t]
        (fun s ↦ ∫ y, (s / max s ‖y‖) * f (x - y)) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact integral_mul_unitSphereAverage_inv_norm_eq_profile (fun y ↦ f (x - y)) hs
  have hi : (∫ y, (if t < ‖y‖ then ‖y‖⁻¹ else 0) * f (x - y)) =
      ∫ y, exteriorNewtonKernel t (x - y) * f y := by
    have hc := integral_sub_left_eq_self (fun y ↦ exteriorNewtonKernel t y * f (x - y)) volume x
    simpa only [exteriorNewtonKernel, Set.indicator_apply, Set.mem_ofPred_eq,
      sub_sub_cancel] using hc.symm
  rw [hi] at h
  exact h.congr_of_eventuallyEq heq

end WaveEquation.Strichartz
