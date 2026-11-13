/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction

/-!
# Zeroth-order Sobolev spaces

There is just one derivative index at order zero, so `W^{0,p}(Ω)` is isometrically
`L^p(Ω)`. The empty weak derivative constraint follows from local integrability.
This identification includes `p = ∞` and requires no boundary regularity.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- Regard an `L^p` class as a zeroth-order Sobolev element. -/
def lpToZeroOrder (u : DerivLp n p Ω) : W^{0,p}(Ω) :=
  ⟨WithLp.toLp p (fun _ ↦ u), by
    intro a
    rw [a.eq_baseIndex_of_order_zero, baseIndex_toList]
    exact hasWeakDerivativeOn_nil (memLp_locallyIntegrableOn_domain (Lp.memLp u) Fact.out)⟩

/-- The zeroth-order lift preserves its only coordinate exactly. -/
theorem wkpBaseCoordinateCLM_lpToZeroOrder (u : DerivLp n p Ω) :
    wkpBaseCoordinateCLM (lpToZeroOrder u) = u :=
  rfl

/-- The zeroth-order Sobolev norm is exactly the `L^p` norm, also at infinity. -/
theorem norm_lpToZeroOrder (u : DerivLp n p Ω) :
    ‖lpToZeroOrder u‖ = ‖u‖ := by
  let : Unique (DerivIndex n 0) :=
    ⟨⟨baseIndex n 0⟩, fun a ↦ a.eq_baseIndex_of_order_zero⟩
  change ‖WithLp.toLp p (Function.const (DerivIndex n 0) u)‖ = ‖u‖
  simpa using PiLp.norm_toLp_const' (p := p) (ι := DerivIndex n 0) u

/-- The canonical linear isometry between `L^p` and zeroth-order Sobolev space. -/
def lpEquivZeroOrder : DerivLp n p Ω ≃ₗᵢ[ℝ] W^{0,p}(Ω) where
  toFun := lpToZeroOrder
  invFun := wkpBaseCoordinateCLM
  left_inv := wkpBaseCoordinateCLM_lpToZeroOrder
  right_inv u := by
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

end SobolevSpace.GraphSpace
