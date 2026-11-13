/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Calculus.SpaceTime
import PDE.FDeriv.Calculus

/-!
# Classical wave calculus on an open time strip

Ordinary derivatives of time traces identify the coordinate velocity
and acceleration. Only regularity before the terminal time is required.
-/

@[expose] public noncomputable section

open PDE PDE.Common Set Filter
open scoped Topology

namespace WaveEquation.SmallData.Classical

variable {n : ℕ} {b : ℝ} {u : ℝ^(n + 1) → ℝ}

/-- Joint regularity before a terminal time gives the corresponding germ. -/
theorem contDiffAt_of_before (hu : ContDiffOn ℝ 2 u {p | p 0 < b}) {t : ℝ} (ht : t < b) (x : ℝ^n) :
    ContDiffAt ℝ 2 u (timeSpaceCons t x) := by
  apply hu.contDiffAt
  apply (isOpen_lt (PiLp.continuous_apply 2 _ 0) continuous_const).mem_nhds
  simpa only [mem_ofPred_eq, timeSpaceCons_zero] using ht

/-- A differentiated time trace is the time-coordinate partial derivative. -/
theorem partialDeriv_eq_of_trace_derivative (hu : ContDiffOn ℝ 2 u {p | p 0 < b}) {t v : ℝ}
    (ht : t < b) (x : ℝ^n) (hd : HasDerivAt (fun s ↦ u (timeSpaceCons s x)) v t) :
    (∂[0] u) (timeSpaceCons t x) = v :=
  (hasDerivAt_timeSpaceCons u t x
    ((contDiffAt_of_before hu ht x).differentiableAt (by norm_num))).unique hd

/-- The wave operator equals the observed acceleration minus the
Laplacian of the spatial slice. -/
theorem waveOperator_eq_of_trace_derivatives (hu : ContDiffOn ℝ 2 u {p | p 0 < b})
    (v a : ℝ → ℝ^n → ℝ) (hQ : ∀ t < b, ∀ x, HasDerivAt (fun s ↦ u (timeSpaceCons s x)) (v t x) t)
    (hV : ∀ t < b, ∀ x, HasDerivAt (fun s ↦ v s x) (a t x) t) {t : ℝ} (ht : t < b) (x : ℝ^n) :
    waveOperator u (timeSpaceCons t x) = a t x - laplacian (fun y ↦ u (timeSpaceCons t y)) x := by
  have hr := contDiffAt_of_before hu ht x
  have he : (fun s ↦ (∂[0] u) (timeSpaceCons s x)) =ᶠ[𝓝 t] fun s ↦ v s x := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact partialDeriv_eq_of_trace_derivative hu hs x (hQ s hs x)
  have hsecond := (hV t ht x).congr_of_eventuallyEq he
  have hp := hasDerivAt_timeSpaceCons (∂[0] u) t x
    ((contDiffAt_partialDeriv 1 hr 0).differentiableAt one_ne_zero)
  rw [waveOperator, ← laplacian_timeSlice_of_contDiffAt u t x hr, hp.unique hsecond]

end WaveEquation.SmallData.Classical
