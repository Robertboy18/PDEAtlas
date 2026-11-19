/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Directional chain rules

The second chain rule separates the Hessian of the outer function from the
curvature of the inner map. The spaces and the codomain need not be finite
dimensional. The trajectory rule uses the joint derivative in time and space.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace PDE.Analysis

variable {D E F : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The second chain rule, evaluated in two fixed directions, under local `C²`
hypotheses on both maps. -/
theorem fderiv_fderiv_comp_apply {f : E → F} {g : D → E} {x : D}
    (hf : ContDiffAt ℝ 2 f (g x)) (hg : ContDiffAt ℝ 2 g x) (v w : D) :
    fderiv ℝ (fun y ↦ fderiv ℝ (f ∘ g) y w) x v =
      fderiv ℝ (fderiv ℝ f) (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) +
        fderiv ℝ f (g x) (fderiv ℝ (fun y ↦ fderiv ℝ g y w) x v) := by
  have hnear : (fun y ↦ fderiv ℝ (f ∘ g) y w) =ᶠ[𝓝 x]
      fun y ↦ fderiv ℝ f (g y) (fderiv ℝ g y w) := by
    filter_upwards [hg.continuousAt (hf.eventually (by norm_num)),
      hg.eventually (by norm_num)] with y hyf hyg
    change ContDiffAt ℝ 2 f (g y) at hyf
    rw [fderiv_comp y (hyf.differentiableAt (by norm_num))
      (hyg.differentiableAt (by norm_num))]
    rfl
  have hDf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hDg := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hgd := hg.differentiableAt (by norm_num)
  rw [hnear.fderiv_eq]
  change fderiv ℝ (fun y ↦ ((fderiv ℝ f) ∘ g) y (fderiv ℝ g y w)) x v = _
  rw [fderiv_clm_apply (hDf.comp x hgd) (hDg.clm_apply (differentiableAt_const w)),
    fderiv_comp x hDf hgd]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

/-- Differentiation along a time-parametrized trajectory evaluates the joint
derivative on the spacetime velocity `(1, X'(t))`. -/
theorem HasFDerivAt.hasDerivAt_trajectory {f : ℝ × D → E} {X : ℝ → D}
    {t : ℝ} {v : D} {A : (ℝ × D) →L[ℝ] E}
    (hf : HasFDerivAt f A (t, X t)) (hX : HasDerivAt X v t) :
    HasDerivAt (fun s ↦ f (s, X s)) (A (1, v)) t :=
  hf.comp_hasDerivAt t ((hasDerivAt_id t).prodMk hX)

end PDE.Analysis
