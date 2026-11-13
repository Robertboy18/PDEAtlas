/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.AbsoluteContinuity
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Moving Hilbert-space tests on a time interval

A curve with a continuous derivative is absolutely continuous on every compact interval.
For two absolutely continuous Hilbert-space curves, the scalar inner product satisfies
the integrated product rule with their almost-everywhere derivatives. The scalar FTC
is applied only after absolute continuity of the product has been established.

These facts allow time-dependent spatial tests against an absolutely continuous
regularization of a weak solution.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped InnerProductSpace NNReal Topology

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E]
variable {a b : ℝ}

section

variable [NormedSpace ℝ E]

/-- A continuous derivative is bounded on a compact interval; the mean value theorem
therefore makes the curve Lipschitz, hence absolutely continuous, on that interval. -/
theorem absolutelyContinuousOnInterval_of_continuous_derivative
    {u v : ℝ → E} (hv : ContinuousOn v (uIcc a b))
    (hu : ∀ t ∈ uIcc a b, HasDerivAt u (v t) t) :
    AbsolutelyContinuousOnInterval u a b := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ t ∈ uIcc a b, ‖v t‖ ≤ M :=
    isCompact_uIcc.exists_bound_of_continuousOn hv
  let K : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  have hbound (t : ℝ) (ht : t ∈ uIcc a b) : ‖v t‖₊ ≤ K := by
    change ‖v t‖ ≤ max M 0
    exact (hM t ht).trans (le_max_left M 0)
  exact (Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_uIcc a b)
    (fun t ht ↦ (hu t ht).hasDerivWithinAt) hbound).absolutelyContinuousOnInterval

end

/-- Integrated product rule for absolutely continuous real Hilbert-space curves.
The derivatives are specified almost everywhere; no continuity of either derivative
is assumed. The conclusion keeps the two summands under one integral. -/
theorem integrated_inner_product_of_ae_hasDerivAt
    [InnerProductSpace ℝ E] {u du y dy : ℝ → E}
    (hu : AbsolutelyContinuousOnInterval u a b)
    (hy : AbsolutelyContinuousOnInterval y a b)
    (hdu : ∀ᵐ t ∂volume.restrict (uIoc a b), HasDerivAt u (du t) t)
    (hdy : ∀ᵐ t ∂volume.restrict (uIoc a b), HasDerivAt y (dy t) t) :
    inner ℝ (u b) (y b) - inner ℝ (u a) (y a) =
      ∫ t in a..b, inner ℝ (u t) (dy t) + inner ℝ (du t) (y t) := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  let c : ℝ → E →L[ℝ] ℝ := fun t ↦ B (u t)
  have hc : AbsolutelyContinuousOnInterval c a b :=
    B.lipschitzWith.comp_absolutelyContinuousOnInterval hu
  have happly : AbsolutelyContinuousOnInterval (fun t ↦ c t (y t)) a b :=
    PDE.Analysis.Evolution.AbsolutelyContinuousOnInterval.clm_apply
      (E := E) (F := ℝ) (c := c) (u := y) hc hy
  have hinner : AbsolutelyContinuousOnInterval (fun t ↦ inner ℝ (u t) (y t)) a b := by
    have hcurve : (fun t ↦ c t (y t)) = (fun t ↦ inner ℝ (u t) (y t)) := by
      funext t
      rfl
    exact hcurve ▸ happly
  have hderiv :
      (fun t ↦ deriv (fun s ↦ inner ℝ (u s) (y s)) t) =ᵐ[volume.restrict (uIoc a b)]
        (fun t ↦ inner ℝ (u t) (dy t) + inner ℝ (du t) (y t)) := by
    filter_upwards [hdu, hdy] with t hut hyt
    have ht : HasDerivAt (fun s ↦ inner ℝ (u s) (y s))
        (inner ℝ (u t) (dy t) + inner ℝ (du t) (y t)) t :=
      HasDerivAt.inner (E := E) ℝ hut hyt
    exact ht.deriv
  have hFTC :
      (∫ t in a..b, deriv (fun s ↦ inner ℝ (u s) (y s)) t) =
        inner ℝ (u b) (y b) - inner ℝ (u a) (y a) :=
    _root_.AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
      (f := fun t ↦ inner ℝ (u t) (y t)) (a := a) (b := b) hinner
  exact hFTC.symm.trans (intervalIntegral.integral_congr_ae_restrict hderiv)

end PDE.Analysis.Evolution
