/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Notation

/-!
# Banach-valued Sobolev spaces of order zero

The order-zero graph has a single `Lp` coordinate. Its empty weak derivative
identity follows from local Bochner integrability, so it imposes no further
constraint for `1 ≤ p ≤ ∞`. The resulting identification preserves the graph
norm exactly, including in dimension zero.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Regard an `Lp` class as the sole coordinate of an order-zero Sobolev graph. -/
def lpToZeroOrder (u : Lp F p (domainMeasure n Ω)) : W^{0,p}(Ω; F) :=
  ⟨WithLp.toLp p (fun _ ↦ u), by
    intro a
    rw [a.eq_baseIndex_of_order_zero, baseIndex_toList]
    exact hasWeakDerivativeOn_nil
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((Lp.memLp u).locallyIntegrable Fact.out))⟩

/-- The order-zero lift retains its `Lp` coordinate exactly. -/
@[simp] theorem lpToZeroOrder_apply (u : Lp F p (domainMeasure n Ω))
    (a : DerivIndex n 0) :
    (lpToZeroOrder u).val a = u :=
  rfl

/-- The order-zero lift preserves the `Lp` norm at both exponent endpoints. -/
theorem norm_lpToZeroOrder (u : Lp F p (domainMeasure n Ω)) :
    ‖lpToZeroOrder u‖ = ‖u‖ := by
  let : Unique (DerivIndex n 0) :=
    ⟨⟨baseIndex n 0⟩, fun a ↦ a.eq_baseIndex_of_order_zero⟩
  change ‖WithLp.toLp p (Function.const (DerivIndex n 0) u)‖ = ‖u‖
  simpa using PiLp.norm_toLp_const' (p := p) (ι := DerivIndex n 0) u

/-- Banach-valued `Lp` and the order-zero Sobolev graph are linearly isometric. -/
def lpEquivZeroOrder : Lp F p (domainMeasure n Ω) ≃ₗᵢ[ℝ] W^{0,p}(Ω; F) where
  toFun := lpToZeroOrder
  invFun := coordinateCLM (baseIndex n 0)
  left_inv _ := rfl
  right_inv U := by
    apply Subtype.ext
    apply PiLp.ext
    intro a
    rw [a.eq_baseIndex_of_order_zero]
    rfl
  map_add' u v := by
    apply Subtype.ext
    rfl
  map_smul' c u := by
    apply Subtype.ext
    rfl
  norm_map' := norm_lpToZeroOrder

/-- The inverse isometry reads the base `Lp` coordinate. -/
@[simp] theorem lpEquivZeroOrder_symm_apply (U : W^{0,p}(Ω; F)) :
    lpEquivZeroOrder.symm U = U.val (baseIndex n 0) :=
  rfl

/-- The order-zero graph norm equals the norm of its physical `Lp` coordinate. -/
theorem norm_eq_norm_base_of_order_zero (U : W^{0,p}(Ω; F)) :
    ‖U‖ = ‖U.val (baseIndex n 0)‖ :=
  (lpEquivZeroOrder.symm.norm_map U).symm

end SobolevSpace.VectorValued
