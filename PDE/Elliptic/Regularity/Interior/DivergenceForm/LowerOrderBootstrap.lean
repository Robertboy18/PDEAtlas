/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.InteriorLowerOrder
public import PDE.Spaces.Sobolev.Calculus.Product.HigherOrderOperator
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# Sobolev regularity of the lower-order forcing

If the state has `m + 1` derivatives and the drift and potential have `m` bounded
derivatives, their contribution belongs to `H^m`. This turns the full weak equation
into the principal equation with a higher-order Sobolev forcing.
-/

@[expose] public noncomputable section

open scoped Sobolev

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.GraphSpace

variable {n m : ℕ} {Ω : Set (ℝ^n)}

/-- The lower-order contribution gains the regularity of the state and
coefficients. The state is arbitrary H¹, with no boundary condition. -/
theorem exists_lowerOrder_forcing
    (hm : 0 < m) (hΩ : IsOpen Ω)
    (B : Fin n → W^{m,∞}(Ω)) (C : W^{m,∞}(Ω))
    (U : W^{m + 1,2}(Ω)) (u : H¹(Ω))
    (hU : wkpBaseCoordinateCLM U = wkpBaseCoordinateCLM u) :
    ∃ G : W^{m,2}(Ω),
      wkpBaseCoordinateCLM G =
        interiorLowerOrderOperator (fun i ↦ wkpBaseCoordinateCLM (B i))
          (wkpBaseCoordinateCLM C) u := by
  classical
  let U₀ : W^{m,2}(Ω) := lowerOrderCLM (by omega) U
  let U₁ : H¹(Ω) := lowerOrderCLM (by omega) U
  have hU₁ : U₁ = u := by
    apply wkpBaseCoordinateCLM_injective hΩ
    simpa [U₁] using hU
  let D (i : Fin n) : W^{m,2}(Ω) :=
    derivativeWordCLM [i] (by simp [Nat.add_comm]) U
  have hD (i : Fin n) :
      wkpBaseCoordinateCLM (D i) = wkpCoordinateCLM (singleDerivIndex n i) u := by
    have hcoord := congrArg
      (fun V : H¹(Ω) ↦ (V : WkpAmbientOn n 1 2 Ω) (singleDerivIndex n i)) hU₁
    simpa [U₁, D, derivativeWordCLM_apply, derivIndexOfList_singleton] using hcoord
  refine ⟨(∑ i, wkTopProduct hm hΩ (B i) (D i)) + wkTopProduct hm hΩ C U₀, ?_⟩
  simp only [map_add, map_sum, wkpBaseCoordinate_wkTopProduct,
    mulLpLeft_apply, interiorLowerOrderOperator_apply, hD]
  have hU₀ : wkpBaseCoordinateCLM U₀ = wkpBaseCoordinateCLM u := by
    simpa [U₀] using hU
  rw [hU₀]

end SobolevSpace.GraphSpace
