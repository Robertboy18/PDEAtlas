/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Analytic functions determined by their derivatives

Two analytic maps with equal iterated Fréchet derivatives of every order at a point
coincide on a neighborhood of that point. Mathlib identifies both maps with the common
Taylor series. The codomain may be any Banach space over a nontrivially normed field
of characteristic zero.
-/

@[expose] public section

open Filter Metric Set
open scoped Topology

/-- Two analytic functions with equal iterated Fréchet derivatives of every order at a point
coincide on a neighborhood of that point. The condition at order zero includes equality
of their values. -/
theorem AnalyticAt.eventuallyEq_of_iteratedFDeriv_eq
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {f g : E → F} {x : E}
    (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 𝕜 g x)
    (hderiv : ∀ k : ℕ, iteratedFDeriv 𝕜 k f x = iteratedFDeriv 𝕜 k g x) :
    f =ᶠ[𝓝 x] g := by
  obtain ⟨p, rp, hp⟩ := hf
  obtain ⟨q, rq, hq⟩ := hg
  filter_upwards [Metric.eball_mem_nhds x hp.r_pos,
    Metric.eball_mem_nhds x hq.r_pos] with y hyp hyq
  have hsumf :
      HasSum (fun k : ℕ ↦
        (k.factorial : 𝕜)⁻¹ • iteratedFDeriv 𝕜 k f x (fun _ ↦ y - x)) (f y) := by
    have hy : y - x ∈ Metric.eball 0 rp := by
      simpa [edist_eq_enorm_sub] using hyp
    simpa only [add_sub_cancel] using hp.hasSum_iteratedFDeriv hy
  have hsumg :
      HasSum (fun k : ℕ ↦
        (k.factorial : 𝕜)⁻¹ • iteratedFDeriv 𝕜 k g x (fun _ ↦ y - x)) (g y) := by
    have hy : y - x ∈ Metric.eball 0 rq := by
      simpa [edist_eq_enorm_sub] using hyq
    simpa only [add_sub_cancel] using hq.hasSum_iteratedFDeriv hy
  have hsum :
      HasSum (fun k : ℕ ↦
        (k.factorial : 𝕜)⁻¹ • iteratedFDeriv 𝕜 k g x (fun _ ↦ y - x)) (f y) := by
    simpa only [hderiv] using hsumf
  exact hsum.unique hsumg
