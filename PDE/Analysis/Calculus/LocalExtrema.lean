/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Derivatives at local extrema

At a maximum or minimum on an interval, the derivative has a sign even at an
endpoint, and local extrema have the expected curvature. These facts are used in
contact estimates, maximum principles, and second-order variational conditions.
-/

@[expose] public section

/-- At a maximum on an interval, the derivative is nonnegative if earlier
points of the interval are available. The maximum may be at the right endpoint. -/
theorem IsMaxOn.deriv_nonneg_of_left_lt {f : ℝ → ℝ} {a b t : ℝ}
    (hmax : IsMaxOn f (Set.Icc a b) t) (hat : a < t) (htb : t ≤ b)
    (hf : DifferentiableAt ℝ f t) :
    0 ≤ deriv f t := by
  have htangent : a - t ∈ posTangentConeAt (Set.Icc a b) t :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc a b).segment_subset ⟨hat.le, htb⟩ ⟨le_rfl, hat.le.trans htb⟩)
  have hdir := hmax.isLocalMaxOn.hasFDerivWithinAt_nonpos
    hf.hasDerivAt.hasFDerivAt.hasFDerivWithinAt htangent
  simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul] at hdir
  nlinarith

/-- At a minimum supported by an interval extending to the left, the derivative
is nonpositive, including at the interval's right endpoint. -/
theorem IsMinOn.deriv_nonpos_of_left_lt {f : ℝ → ℝ} {a b t : ℝ}
    (hmin : IsMinOn f (Set.Icc a b) t) (hat : a < t) (htb : t ≤ b)
    (hf : DifferentiableAt ℝ f t) :
    deriv f t ≤ 0 := by
  simpa only [deriv.fun_neg, neg_nonneg] using
    hmin.neg.deriv_nonneg_of_left_lt hat htb hf.neg

/-- At a local maximum where a real function is continuous, its totalized second derivative
is nonpositive.

Mathlib's second-derivative test supplies the converse implication from a positive second
derivative to a local minimum. If a point were simultaneously a local maximum and such a local
minimum, the function would be locally constant; differentiating that germ twice contradicts
strict positivity. -/
theorem IsLocalMax.deriv_deriv_nonpos {f : ℝ → ℝ} {x : ℝ}
    (hmax : IsLocalMax f x) (hf : ContinuousAt f x) :
    deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hpos : 0 < deriv (deriv f) x := lt_of_not_ge h
  have hmin : IsLocalMin f x :=
    isLocalMin_of_deriv_deriv_pos hpos hmax.deriv_eq_zero hf
  have hconst : f =ᶠ[nhds x] fun _ ↦ f x := by
    filter_upwards [hmax, hmin] with y hymax hymin
    exact le_antisymm hymax hymin
  have hderiv : deriv f =ᶠ[nhds x] fun _ ↦ 0 := by
    simpa using hconst.deriv
  have hzero : deriv (deriv f) x = 0 := by
    simpa using hderiv.deriv_eq
  linarith
