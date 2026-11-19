/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Graph.Construction

/-!
# Differential invariance of the constructed graph

Differentiate the identity identifying every constructed orbit with the graph
of its center projection. This gives the vector field on the graph by applying
its derivative to the projected vector field.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {ι : Type*} [Fintype ι] {η : ℝ} {L : ℝ≥0} {N : (ι → ℝ) → (ι → ℝ)}

/-- At a differentiability point in the center space, the derivative of the
constructed graph carries its reduced vector field to the full vector field. -/
theorem fderiv_diagonalInvariantGraph_apply_center
    (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (hsmall : ‖diagonalGreen hη rate hgap‖ * L < 1)
    (ξ : ι → ℝ) (hξ : ∀ i, rate i * ξ i = 0)
    (hφ : DifferentiableAt ℝ (diagonalInvariantGraph hη rate hgap hN hN0 hsmall) ξ) :
    let φ := diagonalInvariantGraph hη rate hgap hN hN0 hsmall
    let v := fun i ↦ rate i * φ ξ i + N (φ ξ) i
    fderiv ℝ φ ξ (diagonalCenterProjection rate v) = v := by
  let φ := diagonalInvariantGraph hη rate hgap hN hN0 hsmall
  let Pc := diagonalCenterProjection rate
  let u := perronPath η (diagonalGreen hη rate hgap) hN hN0 hsmall
    (centerSeed hη.le (Pc ξ))
  let X := exponentialLift η u
  have hX0 : X 0 = φ ξ := exponentialLift_zero η u
  have hcenter : Pc (X 0) = ξ := by
    rw [hX0]
    exact (diagonalCenterProjection_diagonalInvariantGraph
      hη rate hgap hN hN0 hsmall ξ).trans (diagonalCenterProjection_eq_self rate ξ hξ)
  have hdX : HasDerivAt X (fun i ↦ rate i * φ ξ i + N (φ ξ) i) 0 := by
    have hd := hasDerivAt_perronPath hη rate hgap hN hN0 hsmall (Pc ξ)
      (rate_mul_diagonalCenterProjection rate ξ) 0
    change HasDerivAt X (fun i ↦ rate i * X 0 i + N (X 0) i) 0 at hd
    rwa [hX0] at hd
  have he : φ ∘ (Pc ∘ X) = X := by
    funext t
    exact (diagonalInvariantGraph_diagonalCenterProjection
      hη rate hgap hN hN0 hsmall (X t)).trans
      (exponentialLift_perronPath_eq_diagonalInvariantGraph
        hη rate hgap hN hN0 hsmall ξ t).symm
  have hd := hφ.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (Pc.hasFDerivAt.comp_hasDerivAt 0 hdX) hcenter.symm
  rw [he] at hd
  exact hd.unique hdX

end PDE.Analysis.Evolution
