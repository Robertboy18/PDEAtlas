/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Invariance

/-!
# Containment of bounded complete orbits

A bounded solution of the differential equation is exponentially bounded
at every positive weight. The differential characterization then identifies it
with the path constructed from its center coordinates at zero. In particular,
every equilibrium lies on the constructed graph.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {ι : Type*} [Fintype ι] {η : ℝ} {L : ℝ≥0} {N : (ι → ℝ) → (ι → ℝ)}

/-- Every bounded solution of the nonlinear diagonal equation on `ℝ` is the
constructed path with its own center data. -/
theorem eq_exponentialLift_perronPath_of_bounded (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (hsmall : ‖diagonalGreen hη rate hgap‖ * L < 1)
    (u : C(ℝ, ι → ℝ)) (C : ℝ) (hbound : ∀ t, ‖u t‖ ≤ C)
    (hu : ∀ t, HasDerivAt u (fun i ↦ rate i * u t i + N (u t) i) t) :
    u = exponentialLift η
      (perronPath η (diagonalGreen hη rate hgap) hN hN0 hsmall
        (centerSeed hη.le (diagonalCenterProjection rate (u 0)))) := by
  have hC : 0 ≤ C := (norm_nonneg (u 0)).trans (hbound 0)
  have hg (t : ℝ) : ‖u t‖ ≤ Real.exp (η * |t|) * C := by
    apply (hbound t).trans
    exact le_mul_of_one_le_left hC
      (Real.one_le_exp_iff.mpr (mul_nonneg hη.le (abs_nonneg t)))
  let v := ofExponentialBound η u C hg
  have heq : exponentialLift η v = u := exponentialLift_ofExponentialBound η u C hg
  have hv := eq_perronPath_of_hasDerivAt hη rate hgap hN hN0 hsmall
    (diagonalCenterProjection rate (u 0)) (rate_mul_diagonalCenterProjection rate _) v
    (by simpa only [heq] using hu) (by
      intro i hi
      have hz := congrArg (fun g : C(ℝ, ι → ℝ) ↦ g 0 i) heq
      simpa only [exponentialLift_zero, diagonalCenterProjection_apply, ite_eq_left hi] using hz)
  exact heq.symm.trans (congrArg (exponentialLift η) hv)

/-- An equilibrium belongs to the constructed graph, with its own
center projection as parameter. -/
theorem equilibrium_eq_perronPath_zero (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (hsmall : ‖diagonalGreen hη rate hgap‖ * L < 1)
    (x : ι → ℝ) (hx : ∀ i, rate i * x i + N x i = 0) :
    x = perronPath η (diagonalGreen hη rate hgap) hN hN0 hsmall
      (centerSeed hη.le (diagonalCenterProjection rate x)) 0 := by
  have hfield : (fun i ↦ rate i * x i + N x i) = 0 := funext hx
  have heq := eq_exponentialLift_perronPath_of_bounded hη rate hgap hN hN0 hsmall
    (ContinuousMap.const ℝ x) ‖x‖ (fun _ ↦ le_rfl) (by
      intro t
      change HasDerivAt (fun _ : ℝ ↦ x) (fun i ↦ rate i * x i + N x i) t
      rw [hfield]
      exact hasDerivAt_const t x)
  simpa only [ContinuousMap.const_apply, exponentialLift_zero] using
    congrArg (fun u : C(ℝ, ι → ℝ) ↦ u 0) heq

end PDE.Analysis.Evolution
