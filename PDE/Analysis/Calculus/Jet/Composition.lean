/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jet.Closure
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Chain rules for continuous closure jets

Composition with a classical C² map preserves the continuous second jet on the
closure. The first and second extensions are the actual chain-rule expressions,
so their values remain available at boundary points.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace PDE.Analysis.ContinuousSecondJetOn

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f : E → F} {s : Set E}

/-- Inside an open domain, the second extension differentiates the first
extension itself. -/
theorem hasFDerivAt_first (h : ContinuousSecondJetOn f s)
    (hs : IsOpen s) {x : E} (hx : x ∈ s) :
    HasFDerivAt h.first (h.second x) x := by
  have hd := ((h.contDiffOn.contDiffAt (hs.mem_nhds hx)).fderiv_right
    (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt
  rw [← h.second_eq hx] at hd
  exact hd.congr_of_eventuallyEq (h.first_eq.eventuallyEq_of_mem (hs.mem_nhds hx))

/-- The second extension is symmetric at every interior point. -/
theorem second_apply_comm (h : ContinuousSecondJetOn f s)
    (hs : IsOpen s) {x : E} (hx : x ∈ s) (v w : E) :
    h.second x v w = h.second x w v := by
  rw [h.second_eq hx]
  exact (h.contDiffOn.contDiffAt (hs.mem_nhds hx)).isSymmSndFDerivAt (by norm_num) v w

/-- Postcomposition preserves a raw continuous closure jet. The outside map
needs only C² regularity, and no extension of the inside map beyond its domain
is assumed. -/
def comp {g : F → G} (hg : ContDiff ℝ 2 g)
    (h : ContinuousSecondJetOn f s) (hs : IsOpen s) :
    ContinuousSecondJetOn (g ∘ f) s where
  contDiffOn := hg.comp_contDiffOn h.contDiffOn
  continuousOn := hg.continuous.comp_continuousOn h.continuousOn
  first x := (fderiv ℝ g (f x)).comp (h.first x)
  second x :=
    (ContinuousLinearMap.compL ℝ E F G (fderiv ℝ g (f x))).comp (h.second x) +
      ((ContinuousLinearMap.compL ℝ E F G).flip (h.first x)).comp
        ((fderiv ℝ (fderiv ℝ g) (f x)).comp (h.first x))
  continuousOn_first := by
    have hA := (hg.continuous_fderiv (by norm_num)).comp_continuousOn h.continuousOn
    exact hA.clm_comp h.continuousOn_first
  continuousOn_second := by
    have hA := (hg.continuous_fderiv (by norm_num)).comp_continuousOn h.continuousOn
    have hB := ((hg.fderiv_right (m := 1) (by norm_num)).continuous_fderiv
      (by norm_num)).comp_continuousOn h.continuousOn
    exact (((ContinuousLinearMap.compL ℝ E F G).continuous.comp_continuousOn hA).clm_comp
      h.continuousOn_second).add
        ((((ContinuousLinearMap.compL ℝ E F G).flip.continuous.comp_continuousOn
          h.continuousOn_first)).clm_comp (hB.clm_comp h.continuousOn_first))
  first_eq x hx := by
    exact ((hg.differentiable (by norm_num) (f x)).hasFDerivAt.comp x
      (h.hasFDerivAt hs hx)).fderiv.symm
  second_eq x hx := by
    have hDg := ((hg.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) (f x)).hasFDerivAt.comp x (h.hasFDerivAt hs hx)
    have hd := hDg.clm_comp (h.hasFDerivAt_first hs hx)
    have heq : fderiv ℝ (g ∘ f) =ᶠ[𝓝 x]
        (fun y ↦ (fderiv ℝ g (f y)).comp (h.first y)) := by
      filter_upwards [hs.mem_nhds hx] with y hy
      exact ((hg.differentiable (by norm_num) (f y)).hasFDerivAt.comp y
        (h.hasFDerivAt hs hy)).fderiv
    exact (hd.congr_of_eventuallyEq heq).fderiv.symm

end PDE.Analysis.ContinuousSecondJetOn
