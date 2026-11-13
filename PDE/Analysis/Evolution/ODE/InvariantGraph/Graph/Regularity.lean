/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Graph.Construction
public import PDE.Analysis.Evolution.ODE.InvariantGraph.Differentiability.ContDiff
public import PDE.Analysis.Normed.ContinuousMap.Bounded.Constant

/-!
# C² regularity of the constructed diagonal graph

The diagonal Green operators commute with changes of exponential
weight. Constant center seeds depend linearly on their finite-dimensional
parameter, and evaluation at zero is continuous linear. The weighted `C²`
theorem therefore applies to the graph constructed by the contraction.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {ι : Type*} [Fintype ι] {η : ℝ}
  {L M K : ℝ≥0} {N : (ι → ℝ) → (ι → ℝ)}

/-- Three diagonal Green contractions give a C² graph over the center
coordinates, including an empty fast complement. -/
theorem contDiff_diagonalInvariantGraph
    (hη : 0 < η) (rate : ι → ℝ)
    (hgap1 : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hgap2 : ∀ i, rate i ≠ 0 → 2 * η < |rate i|)
    (hgap3 : ∀ i, rate i ≠ 0 → 3 * η < |rate i|)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hN3 : ContDiff ℝ 3 N)
    (hDN : LipschitzWith M (fderiv ℝ N))
    (hDDN : LipschitzWith K (fderiv ℝ (fderiv ℝ N)))
    (hsmall1 : ‖diagonalGreen hη rate hgap1‖ * L < 1)
    (hsmall2 : ‖diagonalGreen (by linarith : 0 < 2 * η) rate hgap2‖ * L < 1)
    (hsmall3 : ‖diagonalGreen (by linarith : 0 < 3 * η) rate hgap3‖ * L < 1) :
    ContDiff ℝ 2 (diagonalInvariantGraph hη rate hgap1 hN hN0 hsmall1) := by
  let G := diagonalGreen hη rate hgap1
  let H := diagonalGreen (by linarith : 0 < 2 * η) rate hgap2
  let V := diagonalGreen (by linarith : 0 < 3 * η) rate hgap3
  let P := perronPath η G hN hN0 hsmall1
  let J := increaseExponentialWeight (E := ι → ℝ) (by linarith : η ≤ 3 * η)
  let S := ((increaseExponentialWeight hη.le).comp (constCLM ℝ ℝ (ι → ℝ))).comp
    (diagonalCenterProjection rate)
  have h12 (x : ℝ →ᵇ (ι → ℝ)) :
      increaseExponentialWeight (by linarith : η ≤ 2 * η) (G x) =
        H (increaseExponentialWeight (by linarith : η ≤ 2 * η) x) :=
    increaseExponentialWeight_diagonalGreen hη (by linarith : η ≤ 2 * η)
      rate hgap1 hgap2 x
  have h23 (x : ℝ →ᵇ (ι → ℝ)) :
      increaseExponentialWeight (by linarith : 2 * η ≤ 3 * η) (H x) =
        V (increaseExponentialWeight (by linarith : 2 * η ≤ 3 * η) x) :=
    increaseExponentialWeight_diagonalGreen (by linarith : 0 < 2 * η)
      (by linarith : 2 * η ≤ 3 * η) rate hgap2 hgap3 x
  have hp := contDiff_two_increaseExponentialWeight_perronPath hη.le G H V
    h12 h23 hN hN0 hN3 hDN hDDN hsmall1 hsmall2 hsmall3
  have hd := (evalCLM ℝ (0 : ℝ) : (ℝ →ᵇ (ι → ℝ)) →L[ℝ] (ι → ℝ)).contDiff.comp
    (hp.comp S.contDiff)
  have he : (fun ξ ↦ (J (P (S ξ))) 0) =
      diagonalInvariantGraph hη rate hgap1 hN hN0 hsmall1 := by
    funext ξ
    have hz := congrArg (fun u : C(ℝ, ι → ℝ) ↦ u 0)
      (exponentialLift_increaseExponentialWeight (by linarith : η ≤ 3 * η) (P (S ξ)))
    simpa only [exponentialLift_zero, P, S, G, J, ContinuousLinearMap.comp_apply,
      constCLM_apply, diagonalInvariantGraph, centerSeed] using hz
  change ContDiff ℝ 2 (fun ξ ↦ (J (P (S ξ))) 0) at hd
  rwa [he] at hd

end PDE.Analysis.Evolution
