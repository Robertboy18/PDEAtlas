/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Strict convexity on a common interval for nearby parameters

A positive second derivative of one slice of a jointly C² function persists
for nearby parameters. Continuity of the Hessian gives one common
interval; the one-dimensional second-derivative criterion gives strict
convexity there. No uniform modulus of continuity is required.
-/

@[expose] public section

namespace PDE.Analysis

open Filter Metric Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem iteratedDeriv_two_firstSlice
    {f : ℝ × E → ℝ} {s : ℝ} {q : E} (hf : ContDiffAt ℝ 2 f (s, q)) :
    iteratedDeriv 2 (fun t ↦ f (t, q)) s =
      fderiv ℝ (fderiv ℝ f) (s, q) (1, 0) (1, 0) := by
  have hd : deriv (fun t : ℝ ↦ (t, q)) = fun _ ↦ (1, 0) := by
    funext t
    exact ((hasDerivAt_id t).prodMk (hasDerivAt_const t q)).deriv
  have hdd : iteratedDeriv 2 (fun t : ℝ ↦ (t, q)) s = 0 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
    exact deriv_const _ _
  have h := iteratedDeriv_vcomp_two hf
    ((contDiffAt_id : ContDiffAt ℝ 2 (fun t : ℝ ↦ t) s).prodMk contDiffAt_const)
  simpa only [Function.comp_def, id_eq, iteratedFDeriv_two_apply, hd, hdd, map_zero,
    add_zero] using h

/-- Positive slice curvature at a point of joint C² regularity yields strict
convexity on one common interval for all nearby parameters. -/
theorem exists_uniform_strictConvexOn_of_iteratedDeriv_pos
    {f : ℝ × E → ℝ} {q₀ : E} (hf : ContDiffAt ℝ 2 f (0, q₀))
    (hpos : 0 < iteratedDeriv 2 (fun s ↦ f (s, q₀)) 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ ball q₀ δ,
      StrictConvexOn ℝ (Ioo (-δ) δ) (fun s ↦ f (s, q)) := by
  have hDf : ContDiffAt ℝ 1 (fderiv ℝ f) (0, q₀) :=
    hf.fderiv_right (by norm_num)
  have hcont : ContinuousAt
      (fun p ↦ fderiv ℝ (fderiv ℝ f) p (1, 0) (1, 0)) (0, q₀) :=
    ((hDf.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const).clm_apply
      continuousAt_const
  have hpositive : 0 < fderiv ℝ (fderiv ℝ f) (0, q₀) (1, 0) (1, 0) := by
    rwa [← iteratedDeriv_two_firstSlice hf]
  have hnear : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀),
      ContDiffAt ℝ 2 f p ∧ 0 < fderiv ℝ (fderiv ℝ f) p (1, 0) (1, 0) :=
    (hf.eventually (by simp)).and (hcont (Ioi_mem_nhds hpositive))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ, hδ, ?_⟩
  intro q hq
  have hmem {s : ℝ} (hs : s ∈ Ioo (-δ) δ) : (s, q) ∈ ball ((0 : ℝ), q₀) δ := by
    rw [← ball_prod_same]
    refine ⟨?_, hq⟩
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hs
  apply strictConvexOn_of_deriv2_pos' (convex_Ioo (-δ) δ)
  · intro s hs
    have hc : ContinuousAt (fun t : ℝ ↦ f (t, q)) s :=
      ((hball (hmem hs)).1.continuousAt).comp (f := fun t : ℝ ↦ (t, q))
        (continuousAt_id.prodMk continuousAt_const)
    exact hc.continuousWithinAt
  · intro s hs
    rw [← iteratedDeriv_eq_iterate, iteratedDeriv_two_firstSlice (hball (hmem hs)).1]
    exact (hball (hmem hs)).2

/-- Negative slice curvature gives strict concavity on a common interval for
nearby parameters, with the same local C² hypothesis. -/
theorem exists_uniform_strictConcaveOn_of_iteratedDeriv_neg
    {f : ℝ × E → ℝ} {q₀ : E} (hf : ContDiffAt ℝ 2 f (0, q₀))
    (hneg : iteratedDeriv 2 (fun s ↦ f (s, q₀)) 0 < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ ball q₀ δ,
      StrictConcaveOn ℝ (Ioo (-δ) δ) (fun s ↦ f (s, q)) := by
  have hpos : 0 < iteratedDeriv 2 (fun s ↦ -f (s, q₀)) 0 := by
    rw [iteratedDeriv_fun_neg]
    exact neg_pos.mpr hneg
  obtain ⟨δ, hδ, hc⟩ := exists_uniform_strictConvexOn_of_iteratedDeriv_pos hf.neg hpos
  refine ⟨δ, hδ, fun q hq ↦ ?_⟩
  have he : -(fun s : ℝ ↦ -f (s, q)) = fun s ↦ f (s, q) := by
    funext s
    exact neg_neg _
  have h := (hc q hq).neg
  rwa [he] at h

end PDE.Analysis
