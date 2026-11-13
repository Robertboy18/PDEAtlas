/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.H1Operator

/-!
# Parameter continuity after mollifying a coefficient derivative

Suppose the base coordinate of a W¹,∞ coefficient depends continuously on a
parameter in L∞, and one weak derivative coordinate has a uniform L∞ bound.
That derivative coordinate need not depend continuously on the parameter.
Nevertheless, after applying a fixed positive-scale mollifier, its product with
an L² input depends jointly continuously on the parameter and the input.

For an H¹ input, the weak product rule writes the expression using only the
coefficient's base coordinate. The derivative bound gives a common Lipschitz
constant in the L² input. Density then extends continuity to all L² inputs.
The parameter set can be a closed time interval, but no time derivative or
continuity outside that set is required.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology Sobolev

namespace SobolevSpace.Approximation

open GraphSpace

variable {n : ℕ}

local notation "L2" => DerivLp n 2 univ

/-- With continuous base coefficients and a uniform bound on the indicated weak
derivative, mollifying its product gives a jointly continuous L²-valued function.
No parameter continuity of the weak derivative itself is assumed. -/
theorem continuousOn_mollifierRowCLM_coefficientDerivative_mul
    {X : Type*} [TopologicalSpace X]
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε)
    (A : X → W^{1,∞}(ℝ^n)) {s : Set X}
    (hA : ContinuousOn
      (fun t ↦ (A t : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)) s)
    (j : Fin n) (L : ℝ≥0)
    (hL : ∀ t ∈ s, ‖(A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)‖ ≤ L) :
    ContinuousOn (fun z : X × L2 ↦
      mollifierRowCLM μ hε
        (((A z.1 : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)) • z.2))
      (s ×ˢ univ) := by
  let a : X → DerivLp n ∞ univ := fun t ↦
    (A t : WkpAmbientOn n 1 ∞ univ) (baseIndex n 1)
  let da : X → DerivLp n ∞ univ := fun t ↦
    (A t : WkpAmbientOn n 1 ∞ univ) (singleDerivIndex n j)
  let J : L2 →L[ℝ] L2 := mollifierRowCLM μ hε
  let D : L2 →L[ℝ] L2 := mollifierDerivativeRowCLM μ hε j
  let M : X → L2 →L[ℝ] L2 := fun t ↦ J.comp (mulLpLeft (da t))
  let T : DerivLp n ∞ univ →L[ℝ] L2 →L[ℝ] L2 :=
    (ContinuousLinearMap.lsmul ℝ ℝ :
      ℝ →L[ℝ] ℝ →L[ℝ] ℝ).holderL (domainMeasure n univ) ∞ 2 2
  have hT (c : DerivLp n ∞ univ) (w : L2) : T c w = c • w := by
    apply Lp.ext
    filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ :
      ℝ →L[ℝ] ℝ →L[ℝ] ℝ).coeFn_holder (r := 2) c w,
      Lp.coeFn_lpSMul (r := 2) c w] with x hleft hright
    exact hleft.trans hright.symm
  have hmul (w : L2) : ContinuousOn (fun t ↦ a t • w : X → L2) s := by
    have h : ContinuousOn (fun t ↦ T (a t) w) s :=
      (T.continuous.comp_continuousOn hA).clm_apply continuousOn_const
    simpa only [hT] using h
  have hdense (U : W^{1,2}(ℝ^n)) :
      ContinuousOn (fun t ↦ M t (wkpCoordinateCLM (baseIndex n 1) U)) s := by
    have hcont : ContinuousOn (fun t ↦
        D (a t • wkpCoordinateCLM (baseIndex n 1) U) -
          J (a t • wkpCoordinateCLM (singleDerivIndex n j) U)) s :=
      (D.continuous.comp_continuousOn (hmul _)).sub
        (J.continuous.comp_continuousOn (hmul _))
    apply hcont.congr
    intro t _
    have hprod := mollifierDerivativeRowCLM_base μ hε j
      (w1TopMultiplierCLM isOpen_univ (A t) U)
    simp only [wkpCoordinateCLM_apply, w1TopMultiplierCLM_apply_coe,
      w1TopMultiplierAmbient_base, w1TopMultiplierAmbient_singleDeriv] at hprod
    change D (a t • wkpCoordinateCLM (baseIndex n 1) U) =
      J (a t • wkpCoordinateCLM (singleDerivIndex n j) U +
        da t • wkpCoordinateCLM (baseIndex n 1) U) at hprod
    rw [map_add] at hprod
    change J (da t • wkpCoordinateCLM (baseIndex n 1) U) =
      D (a t • wkpCoordinateCLM (baseIndex n 1) U) -
        J (a t • wkpCoordinateCLM (singleDerivIndex n j) U)
    apply (eq_sub_iff_add_eq).2
    rw [hprod]
    exact add_comm _ _
  have hLip (t : X) (ht : t ∈ s) : LipschitzWith L (M t) := by
    apply ContinuousLinearMap.lipschitzWith_of_opNorm_le
    apply (M t).opNorm_le_bound L.prop
    intro w
    calc
      ‖M t w‖ ≤ ‖da t • w‖ := norm_mollifierRowCLM_apply_le μ hε _
      _ ≤ ‖da t‖ * ‖w‖ := Lp.norm_smul_le _ _
      _ ≤ (L : ℝ) * ‖w‖ := mul_le_mul_of_nonneg_right (hL t ht) (norm_nonneg _)
  change ContinuousOn (fun z : X × L2 ↦ M z.1 z.2) (s ×ˢ univ)
  refine continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith'
    (fun z : X × L2 ↦ M z.1 z.2)
    (t' := Set.range (baseCoordCLM (n := n) (Ω := univ)))
    (subset_univ _) ?_ L ?_ ?_
  · intro w _
    exact baseCoordCLM_denseRange isOpen_univ w
  · intro t ht
    exact (hLip t ht).lipschitzOnWith
  · rintro _ ⟨U, rfl⟩
    exact hdense U.1

end SobolevSpace.Approximation
