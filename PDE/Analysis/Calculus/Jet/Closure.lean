/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Continuous extensions of a classical second jet

These data express finite classical regularity up to a boundary: interior `C²`
regularity, continuous closure values, and continuous extensions of the first two
Fréchet derivatives. No differentiability outside the domain is required.
Continuity is local on the closure, so unbounded domains impose no global uniform
continuity or growth condition.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set
open scoped ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Raw continuous closure data for a classical second jet on a set.
The extension fields need only be continuous on the closure. -/
structure ContinuousSecondJetOn (f : E → F) (s : Set E) where
  /-- Interior classical regularity. -/
  contDiffOn : ContDiffOn ℝ 2 f s
  /-- The prescribed values are the continuous closure values. -/
  continuousOn : ContinuousOn f (closure s)
  /-- Continuous extension of the first derivative `fderiv ℝ f`. -/
  first : E → E →L[ℝ] F
  /-- Continuous extension of the second derivative `fderiv ℝ (fderiv ℝ f)`. -/
  second : E → E →L[ℝ] E →L[ℝ] F
  /-- Continuity of the extended first derivative. -/
  continuousOn_first : ContinuousOn first (closure s)
  /-- Continuity of the extended second derivative. -/
  continuousOn_second : ContinuousOn second (closure s)
  /-- Agreement with `fderiv ℝ f` on `s`. -/
  first_eq : EqOn first (fderiv ℝ f) s
  /-- Agreement with `fderiv ℝ (fderiv ℝ f)` on `s`. -/
  second_eq : EqOn second (fderiv ℝ (fderiv ℝ f)) s

namespace ContinuousSecondJetOn

variable {f : E → F} {s : Set E}

/-- Ambient C² regularity supplies raw closure data on every set. -/
def ofContDiff (hf : ContDiff ℝ 2 f) (s : Set E) : ContinuousSecondJetOn f s where
  contDiffOn := hf.contDiffOn
  continuousOn := hf.continuous.continuousOn
  first := fderiv ℝ f
  second := fderiv ℝ (fderiv ℝ f)
  continuousOn_first := (hf.continuous_fderiv (by norm_num)).continuousOn
  continuousOn_second :=
    ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv
      (by norm_num)).continuousOn
  first_eq := fun _ _ ↦ rfl
  second_eq := fun _ _ ↦ rfl

/-- On an open domain, `f` has derivative `h.first x` at every `x ∈ s`. -/
theorem hasFDerivAt (h : ContinuousSecondJetOn f s) (hs : IsOpen s)
    {x : E} (hx : x ∈ s) : HasFDerivAt f (h.first x) x := by
  rw [h.first_eq hx]
  exact (h.contDiffOn.contDiffAt (hs.mem_nhds hx)).differentiableAt (by norm_num)
    |>.hasFDerivAt

end ContinuousSecondJetOn

end PDE.Analysis
