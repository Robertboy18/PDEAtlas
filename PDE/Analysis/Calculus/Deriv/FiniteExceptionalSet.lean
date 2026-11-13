/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Right derivatives across a finite exceptional set

A function on `[a, b]` that is continuous, has the derivative `d` off a finite subset of `(a, b)`,
and whose candidate derivative `d` is right-continuous, has the right derivative `d x` at every
`x ∈ [a, b)`, including the left endpoint and the exceptional points. This is the form in which
one-sided differential inequalities are applied to functions with finitely many corners.

## Main results

* `hasDerivWithinAt_Ici_of_off_finite`: `f` has the right derivative `d x` at every
  `x ∈ [a, b)`.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace PDE.Analysis.Calculus

/-- **Right derivatives across a finite exceptional set.** Let `f` be continuous on `[a, b]` with
derivative `d y` at every `y ∈ (a, b)` outside a finite set `s`, and let `d` be right-continuous
on `[a, b)`. Then `d x` is the right derivative of `f` at every `x ∈ [a, b)`. This covers corners
of `f` at the points of `s` and at `a`. -/
theorem hasDerivWithinAt_Ici_of_off_finite {f d : ℝ → ℝ} {a b x : ℝ} {s : Set ℝ}
    (hs : s.Finite) (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ y ∈ Ioo a b \ s, HasDerivAt f (d y) y)
    (hd : ∀ y ∈ Ico a b, ContinuousWithinAt d (Ici y) y) (hx : x ∈ Ico a b) :
    HasDerivWithinAt f (d x) (Ici x) x := by
  have hns : ∀ᶠ y in 𝓝[>] x, y ∉ s := by
    have hc : (s \ {x})ᶜ ∈ 𝓝 x :=
      (hs.sdiff.isClosed).isOpen_compl.mem_nhds fun h ↦ h.2 rfl
    filter_upwards [nhdsWithin_le_nhds hc, self_mem_nhdsWithin] with y hy hy'
    exact fun hys ↦ hy ⟨hys, ne_of_gt hy'⟩
  have hS : Ioo x b \ s ∈ 𝓝[>] x := by
    filter_upwards [Ioo_mem_nhdsGT hx.2, hns] with y hy hy' using ⟨hy, hy'⟩
  have hsub : Ioo x b \ s ⊆ Ioo a b \ s := fun y hy ↦
    ⟨⟨hx.1.trans_lt hy.1.1, hy.1.2⟩, hy.2⟩
  refine hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo x b \ s)
    (fun y hy ↦ (hderiv y (hsub hy)).differentiableAt.differentiableWithinAt)
    ((hf x (Ico_subset_Icc_self hx)).mono fun y hy ↦
      ⟨hx.1.trans (le_of_lt hy.1.1), le_of_lt hy.1.2⟩) hS ?_
  have hlim : Filter.Tendsto d (𝓝[>] x) (𝓝 (d x)) :=
    (hd x hx).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
  refine hlim.congr' ?_
  filter_upwards [hS] with y hy
  exact ((hderiv y (hsub hy)).deriv).symm

end PDE.Analysis.Calculus
