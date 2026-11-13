/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.PartialDeriv

/-!
# Regularity of coordinate derivatives of ordinary functions

Linearity and the scalar product rule for coordinate derivatives of `ContDiff`
functions, as equalities of functions, and continuity of the coordinate derivatives
of `C¹` functions. On a set, taking a coordinate derivative costs one derivative
when the set is open. At a boundary, `ContDiffOn` alone does not control the ambient total
`fderiv` used by `partialDeriv`.
-/

@[expose] public noncomputable section

open PDE
open scoped ContDiff

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : ℝ^n → E} {x : ℝ^n} {s : Set (ℝ^n)} {k r : WithTop ℕ∞}

/-- Coordinate differentiation distributes over addition of positive-order
`ContDiff` functions, as an equality of functions. The two orders may differ. -/
theorem ContDiff.partialDeriv_add {g : ℝ^n → E} {q : WithTop ℕ∞}
    (hf : ContDiff ℝ r f) (hg : ContDiff ℝ q g) (i : Fin n)
    (hr : r ≠ 0 := by norm_num) (hq : q ≠ 0 := by norm_num) :
    ∂[i] (f + g) = ∂[i] f + ∂[i] g :=
  (hf.differentiable hr).partialDeriv_add (hg.differentiable hq) i

/-- Coordinate differentiation distributes over subtraction of positive-order
`ContDiff` functions, as an equality of functions. The two orders may differ. -/
theorem ContDiff.partialDeriv_sub {g : ℝ^n → E} {q : WithTop ℕ∞}
    (hf : ContDiff ℝ r f) (hg : ContDiff ℝ q g) (i : Fin n)
    (hr : r ≠ 0 := by norm_num) (hq : q ≠ 0 := by norm_num) :
    ∂[i] (f - g) = ∂[i] f - ∂[i] g :=
  (hf.differentiable hr).partialDeriv_sub (hg.differentiable hq) i

/-- The scalar–vector product rule for positive-order `ContDiff` functions,
as an equality of functions. The two orders may differ. -/
theorem ContDiff.partialDeriv_smul {c : ℝ^n → ℝ} {q : WithTop ℕ∞}
    (hc : ContDiff ℝ q c) (hf : ContDiff ℝ r f) (i : Fin n)
    (hq : q ≠ 0 := by norm_num) (hr : r ≠ 0 := by norm_num) :
    ∂[i] (c • f) = c • ∂[i] f + ∂[i] c • f :=
  (hc.differentiable hq).partialDeriv_smul (hf.differentiable hr) i

/-- On an open domain the ordinary coordinate partial loses one order of
regularity. Openness identifies the ambient and within derivatives. -/
theorem ContDiffOn.partialDeriv (hf : ContDiffOn ℝ r f s) (i : Fin n)
    (hs : IsOpen s) (hkr : k + 1 ≤ r) : ContDiffOn ℝ k (∂[i] f) s := by
  change ContDiffOn ℝ k (fun y ↦ fderiv ℝ f y (EuclideanSpace.single i (1 : ℝ))) s
  exact (hf.fderiv_of_isOpen hs hkr).clm_apply contDiffOn_const

/-- A C¹ germ has continuous coordinate partials at its base point. -/
theorem ContDiffAt.continuousAt_partialDeriv (hf : ContDiffAt ℝ 1 f x) (i : Fin n) :
    ContinuousAt (∂[i] f) x :=
  (hf.partialDeriv i (k := 0) (by simp)).continuousAt

/-- A C¹ map into any real normed space has continuous coordinate partials. -/
theorem ContDiff.continuous_partialDeriv (hf : ContDiff ℝ 1 f) (i : Fin n) :
    Continuous (∂[i] f) :=
  (hf.partialDeriv i (k := 0) (by simp)).continuous

/-- C¹ regularity on an open domain gives continuous ordinary coordinate
partials on that domain. -/
theorem ContDiffOn.continuousOn_partialDeriv (hf : ContDiffOn ℝ 1 f s) (i : Fin n)
    (hs : IsOpen s) : ContinuousOn (∂[i] f) s :=
  (hf.partialDeriv i hs (k := 0) (by simp)).continuousOn
