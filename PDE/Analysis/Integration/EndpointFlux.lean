/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Vanishing integrated endpoint flux

A current that is uniformly bounded on a finite time interval and compactly
supported in space at each time has vanishing integrated flux through the two
endpoints as their distance tends to infinity. Dominated convergence is applied
in time; no common spatial support radius is needed.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis

/-- Uniformly bounded currents with separately compact spatial support have
vanishing integrated endpoint flux on a finite time interval. -/
theorem tendsto_integral_endpoint_flux_zero
    {j : ℝ → ℝ → ℝ} {a b C : ℝ}
    (hj : ∀ x, ContinuousOn (fun t ↦ j t x) (Icc a b))
    (hs : ∀ t ∈ Icc a b, HasCompactSupport (j t))
    (hbound : ∀ t ∈ Icc a b, ∀ x, ‖j t x‖ ≤ C) :
    Tendsto (fun R : ℝ ↦ ∫ t in Icc a b, j t R - j t (-R)) atTop (𝓝 0) := by
  have hmeas (R : ℝ) : AEStronglyMeasurable
      (fun t ↦ j t R - j t (-R)) (volume.restrict (Icc a b)) :=
    ((hj R).sub (hj (-R))).aestronglyMeasurable measurableSet_Icc
  have hb (R : ℝ) : ∀ᵐ t ∂volume.restrict (Icc a b),
      ‖j t R - j t (-R)‖ ≤ 2 * C := by
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro t ht
    calc
      _ ≤ ‖j t R‖ + ‖j t (-R)‖ := norm_sub_le _ _
      _ ≤ 2 * C := by linarith [hbound t ht R, hbound t ht (-R)]
  have hlim : ∀ᵐ t ∂volume.restrict (Icc a b),
      Tendsto (fun R : ℝ ↦ j t R - j t (-R)) atTop (𝓝 (0 : ℝ)) := by
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro t ht
    have hp := (hs t ht).is_zero_at_infty.mono_left
      (atTop_le_cocompact : (atTop : Filter ℝ) ≤ cocompact ℝ)
    have hm := ((hs t ht).is_zero_at_infty.mono_left
      (atBot_le_cocompact : (atBot : Filter ℝ) ≤ cocompact ℝ)).comp
      tendsto_neg_atTop_atBot
    simpa using hp.sub hm
  simpa using tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ ↦ 2 * C) (Eventually.of_forall hmeas) (Eventually.of_forall hb)
    (integrableOn_const (s := Icc a b) (C := 2 * C) (hs := isCompact_Icc.measure_lt_top.ne)) hlim

end PDE.Analysis
