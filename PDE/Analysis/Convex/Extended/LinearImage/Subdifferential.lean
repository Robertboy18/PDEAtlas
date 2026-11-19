/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Convex.Extended.LinearImage.Basic
public import PDE.Analysis.Convex.Subdifferential.Basic
public import PDE.Analysis.Convex.Differentiable.Supporting
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Ambient subgradients of an included differentiable energy

The subgradient in the ambient Hilbert space represents the derivative
on the included space through the inclusion map. In particular, the
inner product used here is the ambient one; this does not identify the
ambient subgradient with the Riesz gradient for a stronger Sobolev norm.
-/

@[expose] public section

namespace PDE.Analysis.Convex

open Set
open scoped RealInnerProductSpace

variable {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Ambient subgradients are exactly the representations of the
Fréchet derivative through the inclusion. Competitors outside its range
have energy `+∞` and impose no additional restriction. -/
theorem mem_subdifferential_linearImageEnergy_iff
    (j : V →L[ℝ] H) (hj : Function.Injective j) {J : V → ℝ}
    (hJ : ConvexOn ℝ univ J) {u : V} {D : V →L[ℝ] ℝ}
    (hD : HasFDerivAt J D u) (v : H) :
    v ∈ subdifferential (linearImageEnergy j J) (j u) ↔
      D = (innerSL ℝ v).comp j := by
  have hproper := isProper_linearImageEnergy j J
  constructor
  · intro hv
    have hs := (mem_subdifferential_iff hproper).mp hv
    have hmin : IsLocalMin (fun w ↦ J w - ⟪v, j w⟫) u := by
      apply Filter.Eventually.of_forall
      intro w
      have hw := hs.2 (j w) (by
        rw [linearImageEnergy_apply j hj]
        exact EReal.coe_ne_top _)
      simp only [linearImageEnergy_apply j hj, EReal.toReal_coe, inner_sub_right] at hw
      linarith
    have hz := hmin.hasFDerivAt_eq_zero (hD.sub ((innerSL ℝ v).comp j).hasFDerivAt)
    exact sub_eq_zero.mp hz
  · intro hv
    apply (mem_subdifferential_iff hproper).mpr
    refine ⟨by rw [linearImageEnergy_apply j hj]; exact EReal.coe_ne_top _, ?_⟩
    intro x hx
    obtain ⟨w, rfl⟩ := (linearImageEnergy_ne_top_iff j hj J x).mp hx
    have hs := PDE.Analysis.fderiv_apply_sub_le_sub_of_convex
      hJ hD w (mem_univ _) (mem_univ _)
    rw [hv] at hs
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, map_sub] at hs
    simp only [linearImageEnergy_apply j hj, EReal.toReal_coe, inner_sub_right]
    linarith

end PDE.Analysis.Convex
