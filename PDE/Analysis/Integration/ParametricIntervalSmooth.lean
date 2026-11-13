/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuity of fixed-interval integrals

Continuity on an arbitrary parameter set times a compact interval gives continuity
of the parameter integral. No condition is imposed outside that product. The
endpoints may have either order or coincide.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open MeasureTheory Set
open scoped Interval Topology

/-- Continuity on a parameter set times a compact interval gives continuity of the integral
on that parameter set. The endpoints may have either order or coincide. -/
theorem continuousOn_intervalIntegral
    {X Y : Type*} [TopologicalSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {S : Set X} {a b : ℝ} {H : X × ℝ → Y}
    (hH : ContinuousOn H (S ×ˢ uIcc a b)) :
    ContinuousOn (fun x ↦ ∫ t in a..b, H (x, t)) S := by
  let π : ℝ → Icc (min a b) (max a b) :=
    projIcc (min a b) (max a b) min_le_max
  have hπ : Continuous π := continuous_projIcc
  let G : S → ℝ → Y := fun x t ↦ H (x.val, (π t).val)
  have hG : Continuous G.uncurry :=
    hH.comp_continuous
      (continuous_fst.subtype_val.prodMk (hπ.subtype_val.comp continuous_snd))
      (fun p ↦ ⟨p.1.property, (π p.2).property⟩)
  have hI : Continuous (fun x : S ↦ ∫ t in a..b, G x t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) hG a b
  rw [continuousOn_iff_continuous_domRestrict]
  apply hI.congr
  intro x
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [G, π, projIcc_of_mem min_le_max ht]

end PDE.Analysis
