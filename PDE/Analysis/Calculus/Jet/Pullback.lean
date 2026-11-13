/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Jet.Composition

/-!
# Restriction and linear pullback of closure jets

Restrictions retain the same derivative extensions. Linear changes of independent
variables pull back those extensions by the ordinary first and second chain
rules, including on the closure of the new domain.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace PDE.Analysis.ContinuousSecondJetOn

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f : E → F} {s t : Set E}

/-- Restrict a closure jet to a smaller domain, retaining its extensions. -/
def mono (h : ContinuousSecondJetOn f s) (hts : t ⊆ s) :
    ContinuousSecondJetOn f t where
  contDiffOn := h.contDiffOn.mono hts
  continuousOn := h.continuousOn.mono (closure_mono hts)
  first := h.first
  second := h.second
  continuousOn_first := h.continuousOn_first.mono (closure_mono hts)
  continuousOn_second := h.continuousOn_second.mono (closure_mono hts)
  first_eq := h.first_eq.mono hts
  second_eq := h.second_eq.mono hts

/-- Pull back the independent variables through a continuous linear map.
The new open domain need only map into the old one. -/
def compContinuousLinearMap (h : ContinuousSecondJetOn f s) (hs : IsOpen s)
    (L : G →L[ℝ] E) {u : Set G} (hu : IsOpen u) (hmaps : MapsTo L u s) :
    ContinuousSecondJetOn (f ∘ L) u where
  contDiffOn := h.contDiffOn.comp L.contDiff.contDiffOn hmaps
  continuousOn := h.continuousOn.comp L.continuous.continuousOn
    (hmaps.closure_of_continuousOn L.continuous.continuousOn)
  first x := (h.first (L x)).comp L
  second x := ((ContinuousLinearMap.compL ℝ G E F).flip L).comp
    ((h.second (L x)).comp L)
  continuousOn_first :=
    (h.continuousOn_first.comp L.continuous.continuousOn
      (hmaps.closure_of_continuousOn L.continuous.continuousOn)).clm_comp continuousOn_const
  continuousOn_second :=
    continuousOn_const.clm_comp
      ((h.continuousOn_second.comp L.continuous.continuousOn
        (hmaps.closure_of_continuousOn L.continuous.continuousOn)).clm_comp continuousOn_const)
  first_eq x hx := ((h.hasFDerivAt hs (hmaps hx)).comp x L.hasFDerivAt).fderiv.symm
  second_eq x hx := by
    have hd := ((ContinuousLinearMap.compL ℝ G E F).flip L).hasFDerivAt.comp x
      ((h.hasFDerivAt_first hs (hmaps hx)).comp x L.hasFDerivAt)
    have heq : fderiv ℝ (f ∘ L) =ᶠ[𝓝 x] (fun y ↦ (h.first (L y)).comp L) := by
      filter_upwards [hu.mem_nhds hx] with y hy
      exact ((h.hasFDerivAt hs (hmaps hy)).comp y L.hasFDerivAt).fderiv
    exact (hd.congr_of_eventuallyEq heq).fderiv.symm

end PDE.Analysis.ContinuousSecondJetOn
