/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Graph.Construction
public import PDE.Analysis.Evolution.ODE.InvariantGraph.Differentiability.AtZero
public import PDE.Analysis.Normed.ContinuousMap.Bounded.Constant

/-!
# Tangency of the constructed graph at the equilibrium

A nonlinear remainder with zero derivative at the origin contributes no
first variation there. The derivative of the graph is the center projection,
so its restriction to the center space is tangent to that space.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {ι : Type*} [Fintype ι] {η : ℝ}
  {L M : ℝ≥0} {N : (ι → ℝ) → (ι → ℝ)}

/-- The graph is tangent to the center space when the nonlinear
remainder vanishes to first order at the equilibrium. -/
theorem hasFDerivAt_diagonalInvariantGraph_zero
    (hη : 0 < η) (rate : ι → ℝ)
    (hgap1 : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hgap2 : ∀ i, rate i ≠ 0 → 2 * η < |rate i|)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hN2 : ContDiff ℝ 2 N)
    (hDN : LipschitzWith M (fderiv ℝ N)) (hDN0 : fderiv ℝ N 0 = 0)
    (hsmall1 : ‖diagonalGreen hη rate hgap1‖ * L < 1)
    (hsmall2 : ‖diagonalGreen (by linarith : 0 < 2 * η) rate hgap2‖ * L < 1) :
    HasFDerivAt (diagonalInvariantGraph hη rate hgap1 hN hN0 hsmall1)
      (diagonalCenterProjection rate) 0 := by
  let G := diagonalGreen hη rate hgap1
  let H := diagonalGreen (by linarith : 0 < 2 * η) rate hgap2
  let P := perronPath η G hN hN0 hsmall1
  let J := increaseExponentialWeight (E := ι → ℝ) (by linarith : η ≤ 2 * η)
  let S := ((increaseExponentialWeight hη.le).comp (constCLM ℝ ℝ (ι → ℝ))).comp
    (diagonalCenterProjection rate)
  let ev : (ℝ →ᵇ (ι → ℝ)) →L[ℝ] (ι → ℝ) := evalCLM ℝ (0 : ℝ)
  have h12 (x : ℝ →ᵇ (ι → ℝ)) :
      increaseExponentialWeight (by linarith : η ≤ 2 * η) (G x) =
        H (increaseExponentialWeight (by linarith : η ≤ 2 * η) x) :=
    increaseExponentialWeight_diagonalGreen hη (by linarith : η ≤ 2 * η)
      rate hgap1 hgap2 x
  have hp : HasFDerivAt (fun z ↦ J (P z)) J (S 0) := by
    simpa only [map_zero] using
      hasFDerivAt_increaseExponentialWeight_perronPath_zero hη.le G H h12
        hN hN0 hN2 hDN hDN0 hsmall1 hsmall2
  have hd := ev.hasFDerivAt.comp 0 (hp.comp 0 S.hasFDerivAt)
  have he : (fun ξ ↦ ev (J (P (S ξ)))) =
      diagonalInvariantGraph hη rate hgap1 hN hN0 hsmall1 := by
    funext ξ
    have hz := congrArg (fun u : C(ℝ, ι → ℝ) ↦ u 0)
      (exponentialLift_increaseExponentialWeight (by linarith : η ≤ 2 * η) (P (S ξ)))
    simpa only [exponentialLift_zero, P, S, G, J, ev, ContinuousLinearMap.comp_apply,
      constCLM_apply, diagonalInvariantGraph, centerSeed, evalCLM_apply] using hz
  have hD : ev.comp (J.comp S) = diagonalCenterProjection rate := by
    apply ContinuousLinearMap.ext
    intro ξ
    have hz := congrArg (fun u : C(ℝ, ι → ℝ) ↦ u 0)
      (exponentialLift_increaseExponentialWeight (by linarith : η ≤ 2 * η) (S ξ))
    have hs := exponentialLift_centerSeed hη.le (diagonalCenterProjection rate ξ) 0
    have hz' : ev (J (S ξ)) = S ξ 0 := by
      simpa only [exponentialLift_zero, ev, J, evalCLM_apply] using hz
    refine hz'.trans ?_
    simpa only [exponentialLift_zero, S, ContinuousLinearMap.comp_apply, constCLM_apply,
      centerSeed] using hs
  change HasFDerivAt (fun ξ ↦ ev (J (P (S ξ)))) (ev.comp (J.comp S)) 0 at hd
  rwa [he, hD] at hd

end PDE.Analysis.Evolution
