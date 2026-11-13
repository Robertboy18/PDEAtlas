/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Containment

/-!
# The graph constructed from center data

Evaluation at zero of the Perron path gives a graph over the diagonal
center space. Projection recovers its parameter. Every constructed orbit stays
on this graph, and every equilibrium lies on it.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {ι : Type*} [Fintype ι] {η : ℝ} {L : ℝ≥0} {N : (ι → ℝ) → (ι → ℝ)}

/-- Evaluate the constructed path with the given center projection at zero.
The parameter may be any vector; only its center coordinates are used. -/
def diagonalInvariantGraph (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (hsmall : ‖diagonalGreen hη rate hgap‖ * L < 1) (ξ : ι → ℝ) : ι → ℝ :=
  perronPath η (diagonalGreen hη rate hgap) hN hN0 hsmall
    (centerSeed hη.le (diagonalCenterProjection rate ξ)) 0

/-- The constructed graph depends only on the center projection of its
parameter. -/
theorem diagonalInvariantGraph_diagonalCenterProjection
    (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (hsmall : ‖diagonalGreen hη rate hgap‖ * L < 1) (ξ : ι → ℝ) :
    diagonalInvariantGraph hη rate hgap hN hN0 hsmall
        (diagonalCenterProjection rate ξ) =
      diagonalInvariantGraph hη rate hgap hN hN0 hsmall ξ := by
  unfold diagonalInvariantGraph
  rw [diagonalCenterProjection_eq_self rate (diagonalCenterProjection rate ξ)
    (rate_mul_diagonalCenterProjection rate ξ)]

/-- Center projection recovers exactly the prescribed center coordinates. -/
theorem diagonalCenterProjection_diagonalInvariantGraph
    (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (hsmall : ‖diagonalGreen hη rate hgap‖ * L < 1) (ξ : ι → ℝ) :
    diagonalCenterProjection rate (diagonalInvariantGraph hη rate hgap hN hN0 hsmall ξ) =
      diagonalCenterProjection rate ξ := by
  ext i
  by_cases hi : rate i = 0
  · simp only [diagonalCenterProjection_apply, ite_eq_left hi]
    exact (perronPath_zero_apply_of_rate_eq_zero hη rate hgap hN hN0 hsmall
      (diagonalCenterProjection rate ξ) i hi).trans
        (by simp only [diagonalCenterProjection_apply, ite_eq_left hi])
  · simp only [diagonalCenterProjection_apply, ite_eq_right hi]

/-- The origin is on the graph when the nonlinear remainder vanishes there. -/
@[simp] theorem diagonalInvariantGraph_zero
    (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (hsmall : ‖diagonalGreen hη rate hgap‖ * L < 1) :
    diagonalInvariantGraph hη rate hgap hN hN0 hsmall 0 = 0 := by
  have hc : const ℝ (0 : ι → ℝ) = 0 := by
    ext t
    rfl
  simp [diagonalInvariantGraph, centerSeed, hc]

/-- Every equilibrium is a point of the constructed graph. -/
theorem equilibrium_eq_diagonalInvariantGraph
    (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (hsmall : ‖diagonalGreen hη rate hgap‖ * L < 1)
    (x : ι → ℝ) (hx : ∀ i, rate i * x i + N x i = 0) :
    x = diagonalInvariantGraph hη rate hgap hN hN0 hsmall x :=
  equilibrium_eq_perronPath_zero hη rate hgap hN hN0 hsmall x hx

/-- Every point of a constructed orbit belongs to the graph with its
own center coordinates. -/
theorem exponentialLift_perronPath_eq_diagonalInvariantGraph
    (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (hsmall : ‖diagonalGreen hη rate hgap‖ * L < 1) (ξ : ι → ℝ) (τ : ℝ) :
    let u := perronPath η (diagonalGreen hη rate hgap) hN hN0 hsmall
      (centerSeed hη.le (diagonalCenterProjection rate ξ))
    exponentialLift η u τ =
      diagonalInvariantGraph hη rate hgap hN hN0 hsmall (exponentialLift η u τ) := by
  let u := perronPath η (diagonalGreen hη rate hgap) hN hN0 hsmall
    (centerSeed hη.le (diagonalCenterProjection rate ξ))
  have ht := translateWeightedPath_perronPath hη rate hgap hN hN0 hsmall
    (diagonalCenterProjection rate ξ) (rate_mul_diagonalCenterProjection rate ξ) τ
  have hv := congrArg (fun v : ℝ →ᵇ (ι → ℝ) ↦ v 0) ht
  have hz : translateWeightedPath hη.le τ u 0 = exponentialLift η u τ := by
    simpa only [exponentialLift_zero, zero_add] using
      exponentialLift_translateWeightedPath hη.le τ u 0
  exact hz.symm.trans hv

/-- Every bounded complete solution of the differential equation lies on the
constructed graph at each time, with its own center coordinates. -/
theorem eq_diagonalInvariantGraph_of_bounded
    (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (hsmall : ‖diagonalGreen hη rate hgap‖ * L < 1)
    (u : C(ℝ, ι → ℝ)) (C : ℝ) (hbound : ∀ t, ‖u t‖ ≤ C)
    (hu : ∀ t, HasDerivAt u (fun i ↦ rate i * u t i + N (u t) i) t) (t : ℝ) :
    u t = diagonalInvariantGraph hη rate hgap hN hN0 hsmall (u t) := by
  have heq := eq_exponentialLift_perronPath_of_bounded
    hη rate hgap hN hN0 hsmall u C hbound hu
  have ht := congrArg (fun v : C(ℝ, ι → ℝ) ↦ v t) heq
  rw [ht]
  exact exponentialLift_perronPath_eq_diagonalInvariantGraph
    hη rate hgap hN hN0 hsmall (u 0) t

end PDE.Analysis.Evolution
