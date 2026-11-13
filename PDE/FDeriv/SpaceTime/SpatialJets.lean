/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime

/-!
# Spatial derivatives of a smooth spacetime field

The spatial coordinates of `timeSpaceCons t x` are the successor coordinates of the
spacetime vector. The chain rule identifies first and mixed second derivatives in
these two conventions, including their joint continuity in time and space.
-/

@[expose] public section

open PDE.Common

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace PDE

/-- Two spatial derivatives of a slice are the corresponding mixed spacetime derivatives. -/
theorem secondPartialDeriv_timeSpaceCons_spatial
    (u : ℝ^(n + 1) → E) (hu : ContDiff ℝ 2 u)
    (t : ℝ) (x : ℝ^n) (i j : Fin n) :
    (∂[i] (∂[j] (fun y ↦ u (timeSpaceCons t y)))) x =
      (∂[i.succ] (∂[j.succ] u)) (timeSpaceCons t x) := by
  have heq : (∂[j] (fun y ↦ u (timeSpaceCons t y))) =
      fun y ↦ (∂[j.succ] u) (timeSpaceCons t y) :=
    funext fun y ↦ partialDeriv_timeSpaceCons_spatial j u t y
      (hu.differentiable (by norm_num) _)
  rw [heq]
  exact partialDeriv_timeSpaceCons_spatial i (∂[j.succ] u) t x
    ((contDiff_partialDeriv_of_succ hu).differentiable one_ne_zero _)

/-- The spatial coordinate derivatives of a `C¹` spacetime field are jointly continuous. -/
theorem continuous_partialDeriv_timeSpaceCons_spatial
    (u : ℝ^(n + 1) → E) (hu : ContDiff ℝ 1 u) (i : Fin n) :
    Continuous (fun p : ℝ × ℝ^n ↦
      (∂[i] (fun x ↦ u (timeSpaceCons p.1 x))) p.2) := by
  have hfirst : ContDiff ℝ 0 (∂[i.succ] u) :=
    contDiff_partialDeriv_of_succ hu
  simp_rw [partialDeriv_timeSpaceCons_spatial _ _ _ _ (hu.differentiable one_ne_zero _)]
  exact hfirst.continuous.comp (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous

/-- All mixed second spatial derivatives of a `C²` spacetime field are jointly continuous. -/
theorem continuous_secondPartialDeriv_timeSpaceCons_spatial
    (u : ℝ^(n + 1) → E) (hu : ContDiff ℝ 2 u) (i j : Fin n) :
    Continuous (fun p : ℝ × ℝ^n ↦
      (∂[i] (∂[j] (fun x ↦ u (timeSpaceCons p.1 x)))) p.2) := by
  have hfirst : ContDiff ℝ 1 (∂[j.succ] u) :=
    contDiff_partialDeriv_of_succ hu
  have hsecond : ContDiff ℝ 0 (∂[i.succ] (∂[j.succ] u)) :=
    contDiff_partialDeriv_of_succ hfirst
  simp_rw [secondPartialDeriv_timeSpaceCons_spatial _ hu]
  exact hsecond.continuous.comp (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous

end PDE
