/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jet.Closure
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Closure

/-!
# Closure regularity of a differential along a classical map

Continuous extensions of the first two derivatives of a scalar function give
first-order closure regularity of its differential along a `C¹` map. The extensions
need not be differentiable at boundary points. This is useful for classical fluxes
whose arguments include both a map and its Jacobian.
-/

@[expose] public noncomputable section

open Set

namespace PDE.Analysis.ContinuousSecondJetOn

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} {Ω : Set (ℝ^n)} {s : Set E} {f : E → ℝ} {g : ℝ^n → E}

/-- The differential of a function with a continuous second closure jet, evaluated
on a fixed vector along an ambient `C¹` map, has raw first-order closure regularity. -/
theorem contDiffUpToBoundary_fderiv_apply_const_comp
    (hf : ContinuousSecondJetOn f s) (hs : IsOpen s)
    (hbounded : Bornology.IsBounded Ω) (hg : ContDiff ℝ 1 g)
    (hmap : MapsTo g Ω s) (v : E) :
    SobolevSpace.ContDiffUpToBoundary 1 (fun x ↦ fderiv ℝ f (g x) v) Ω := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ f) s :=
    hf.contDiffOn.fderiv_of_isOpen hs (by norm_num)
  have hcl : MapsTo g (closure Ω) (closure s) := hmap.closure hg.continuous
  have hval : ContinuousOn (fun x ↦ hf.first (g x) v) (closure Ω) :=
    (hf.continuousOn_first.comp hg.continuous.continuousOn hcl).clm_apply
      continuousOn_const
  apply SobolevSpace.ContDiffUpToBoundary.of_continuous_first_derivative_extensions
    ((hd.comp hg.contDiffOn hmap).clm_apply contDiffOn_const) hbounded hval
    (fun x hx ↦ congrArg (fun A ↦ A v) (hf.first_eq (hmap hx)))
  intro i
  let e := EuclideanSpace.single i (1 : ℝ)
  refine ⟨fun x ↦ hf.second (g x) (fderiv ℝ g x e) v, ?_, ?_⟩
  · exact ((hf.continuousOn_second.comp hg.continuous.continuousOn hcl).clm_apply
      ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const).continuousOn)
        |>.clm_apply continuousOn_const
  · intro x hx
    have hdf := ((hd.contDiffAt (hs.mem_nhds (hmap hx))).differentiableAt
      (by norm_num)).hasFDerivAt
    have hcomp := (hdf.comp x (hg.differentiable (by norm_num) x).hasFDerivAt)
      |>.clm_apply (hasFDerivAt_const v x)
    dsimp only [Function.comp_def] at hcomp
    change hf.second (g x) (fderiv ℝ g x e) v =
      fderiv ℝ (fun y ↦ fderiv ℝ f (g y) v) x e
    rw [hf.second_eq (hmap hx)]
    have heq := congrArg (fun A : ℝ^n →L[ℝ] ℝ ↦ A e) hcomp.fderiv
    simpa using heq.symm

end PDE.Analysis.ContinuousSecondJetOn
