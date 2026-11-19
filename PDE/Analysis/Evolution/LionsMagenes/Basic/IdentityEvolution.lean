/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.LionsMagenes.Basic.IntegratedDerivative
public import PDE.Analysis.Evolution.Time.AbsoluteContinuity
import PDE.Analysis.Evolution.Time.FundamentalTheorem
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Strong time regularity for the identity Gelfand triple

For the identity triple, the dual embedding sends `x` to the functional `y ↦ ⟪x,y⟫`.
It preserves distances, so an integrated dual derivative already gives absolute continuity
of the original curve. In a complete real inner product space, the inverse Riesz map also
recovers its strong derivative from any almost-everywhere specified pivot-valued velocity.

The absolute-continuity conclusion includes both endpoints. The derivative conclusion is
almost everywhere on `(a,b]`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set

namespace PDE.Analysis.Evolution.HasIntegratedDualDerivativeOn

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {u : ℝ → H} {g : ℝ → StrongDual ℝ H} {a b : ℝ}

/-- For the identity triple, the integrated dual formula makes the original curve
absolutely continuous. Completeness of the inner product space is not needed here. -/
theorem absolutelyContinuousOnInterval_identity
    (h : HasIntegratedDualDerivativeOn (GelfandTriple.identity H) u g a b) :
    AbsolutelyContinuousOnInterval u a b := by
  have hprimitive : AbsolutelyContinuousOnInterval (dualPrimitive g a) a b := by
    exact IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_normedSpace
      h.intervalIntegrable left_mem_uIcc
  have hconstant : AbsolutelyContinuousOnInterval
      (fun _ : ℝ ↦ (GelfandTriple.identity H).pivotToDual (u a)) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  have hdual : AbsolutelyContinuousOnInterval
      (fun t ↦ (GelfandTriple.identity H).pivotToDual (u t)) a b := by
    apply (hconstant.add hprimitive).congr
    intro t ht
    exact (h.eq_add_integral t ht).symm
  have heq (x : H) :
      (GelfandTriple.identity H).pivotToDual x = InnerProductSpace.toDualMap ℝ H x := by
    ext y
    rfl
  unfold _root_.AbsolutelyContinuousOnInterval at hdual ⊢
  simpa only [heq, LinearIsometry.dist_map] using hdual

/-- In a real Hilbert space, a velocity whose Riesz image is the integrated dual
derivative is the strong derivative almost everywhere. The velocity itself needs no
pointwise continuity assumption. -/
theorem ae_hasDerivAt_identity_of_ae_eq [CompleteSpace H]
    (h : HasIntegratedDualDerivativeOn (GelfandTriple.identity H) u g a b)
    (hab : a < b) {v : ℝ → H}
    (hv : g =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ (GelfandTriple.identity H).pivotToDual (v t)) :
    ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt u (v t) t := by
  let R := InnerProductSpace.toDual ℝ H
  let L : StrongDual ℝ H →L[ℝ] H :=
    R.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have heq (x : H) : (GelfandTriple.identity H).pivotToDual x = R x := by
    ext y
    rfl
  have hleft (x : H) : L ((GelfandTriple.identity H).pivotToDual x) = x := by
    change R.symm ((GelfandTriple.identity H).pivotToDual x) = x
    rw [heq, R.symm_apply_apply]
  filter_upwards [h.ae_hasDerivAt_pivotToDual hab, hv] with t ht hvt
  have hcomp := L.hasFDerivAt.comp_hasDerivAt t ht
  simpa only [Function.comp_def, hvt, hleft] using hcomp

end PDE.Analysis.Evolution.HasIntegratedDualDerivativeOn
