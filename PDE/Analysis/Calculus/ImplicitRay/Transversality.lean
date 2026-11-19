/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Uniform monotonicity transverse to a parameter slice

If a jointly `C¹` scalar function has positive derivative in the real variable
at a point, its real-variable slices are strictly increasing on one common
interval for all nearby parameters. Continuity of the partial derivative
supplies the uniform neighborhood; the mean value theorem gives monotonicity.
This turns an infinitesimal orientation into a uniform sign along local curves.
-/

@[expose] public section

namespace PDE.Analysis.Calculus

open Filter Metric Set
open scoped ContDiff Topology

/-- Positive transverse derivative gives a common interval of strict monotonicity
for all nearby parameters of a jointly `C¹` function. -/
theorem exists_uniform_strictMonoOn_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → ℝ} {q₀ : E} (hf : ContDiffAt ℝ 1 f (0, q₀))
    (hpos : 0 < fderiv ℝ f (0, q₀) (1, 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ ball q₀ δ,
      StrictMonoOn (fun s ↦ f (s, q)) (Ioo (-δ) δ) := by
  have hcont : ContinuousAt (fun p ↦ fderiv ℝ f p (1, 0)) (0, q₀) :=
    (hf.continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
  have hnear : ∀ᶠ p in 𝓝 ((0 : ℝ), q₀),
      ContDiffAt ℝ 1 f p ∧ 0 < fderiv ℝ f p (1, 0) :=
    (hf.eventually (by simp)).and (hcont (Ioi_mem_nhds hpos))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ, hδ, ?_⟩
  intro q hq
  have hmem {s : ℝ} (hs : s ∈ Ioo (-δ) δ) : (s, q) ∈ ball ((0 : ℝ), q₀) δ := by
    rw [← ball_prod_same]
    refine ⟨?_, hq⟩
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_lt, mem_Ioo] using hs
  have hderiv {s : ℝ} (hs : s ∈ Ioo (-δ) δ) :
      HasDerivAt (fun t ↦ f (t, q)) (fderiv ℝ f (s, q) (1, 0)) s := by
    have hd := ((hball (hmem hs)).1.differentiableAt one_ne_zero).hasFDerivAt
    simpa only [Function.comp_def, id_eq] using hd.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s q))
  apply strictMonoOn_of_deriv_pos (convex_Ioo (-δ) δ)
  · exact fun s hs ↦ (hderiv hs).continuousAt.continuousWithinAt
  · intro s hs
    have hs' : s ∈ Ioo (-δ) δ := interior_subset hs
    rw [(hderiv hs').deriv]
    exact (hball (hmem hs')).2

/-- The same uniform monotonicity conclusion, expressed using the derivative of
the real-variable slice. -/
theorem exists_uniform_strictMonoOn_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × E → ℝ} {q₀ : E} {a : ℝ}
    (hf : ContDiffAt ℝ 1 f (0, q₀))
    (hd : HasDerivAt (fun s ↦ f (s, q₀)) a 0) (ha : 0 < a) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ ball q₀ δ,
      StrictMonoOn (fun s ↦ f (s, q)) (Ioo (-δ) δ) := by
  apply exists_uniform_strictMonoOn_of_contDiffAt hf
  have hpartial : HasDerivAt (fun s ↦ f (s, q₀))
      (fderiv ℝ f (0, q₀) (1, 0)) 0 := by
    simpa only [Function.comp_def, id_eq] using
      hf.differentiableAt_one.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) q₀))
  rwa [hpartial.unique hd]

end PDE.Analysis.Calculus
