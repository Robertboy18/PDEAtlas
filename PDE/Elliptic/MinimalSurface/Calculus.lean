/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Gradient
public import PDE.FDeriv.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import CAS.ExactTactic

/-!
# Divergence and nondivergence forms of the minimal-graph equation

For a C² graph, the normalized gradient is C¹. In the plane, its divergence is the
nondivergence residual divided by `(sqrt (1 + ‖∇ u‖²))³`. The denominator is strictly
positive, so the two equations are equivalent, including at critical points of u.
The quotient rule and symmetry of the second derivatives give the identity.

This is the passage to equation (24) in Evans, *Partial Differential Equations*,
second edition (2010), §4.4.3(b), p. 210. No nonsingularity or convexity assumption
is needed here.
-/

@[expose] public noncomputable section

open scoped Gradient

namespace PDE.Elliptic.MinimalSurface

/-- The planar minimal-graph equation in nondivergence form. -/
def residual (u : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  (1 + (∂[1] u x) ^ 2) * (∂[0] (∂[0] u)) x -
    2 * (∂[0] u x) * (∂[1] u x) * (∂[0] (∂[1] u)) x +
    (1 + (∂[0] u x) ^ 2) * (∂[1] (∂[1] u)) x

/-- A C² graph has a C¹ normalized gradient, even where its gradient vanishes. -/
theorem contDiffAt_normalizedGradient {n : ℕ} {u : ℝ^n → ℝ} {x : ℝ^n}
    (hu : ContDiffAt ℝ 2 u x) :
    ContDiffAt ℝ 1 (fun y ↦ (Real.sqrt (1 + ‖∇ u y‖ ^ 2))⁻¹ • ∇ u y) x := by
  have hg := PDE.Analysis.contDiffAt_gradient (m := 1) hu
  have hpos : 0 < 1 + ‖∇ u x‖ ^ 2 := by positivity
  exact (((contDiffAt_const.add (hg.norm_sq ℝ)).sqrt (ne_of_gt hpos)).inv
    (ne_of_gt (Real.sqrt_pos.2 hpos))).smul hg

/-- The divergence of the normalized gradient is the planar second-order
minimal-graph residual divided by the cube of the graph's area density. -/
theorem divergence_normalizedGradient_eq {u : ℝ^2 → ℝ} {x : ℝ^2}
    (hu : ContDiffAt ℝ 2 u x) :
    (∇· (fun y ↦ (Real.sqrt (1 + ‖∇ u y‖ ^ 2))⁻¹ • ∇ u y)) x =
      residual u x / Real.sqrt (1 + ‖∇ u x‖ ^ 2) ^ 3 := by
  let q : ℝ^2 → ℝ := fun y ↦ 1 + (∂[0] u y) ^ 2 + (∂[1] u y) ^ 2
  have hq (y : ℝ^2) : 0 < q y := by
    dsimp [q]
    positivity
  have hn (y : ℝ^2) : 1 + ‖∇ u y‖ ^ 2 = q y := by
    simp [q, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, add_assoc]
  have hd (i : Fin 2) : DifferentiableAt ℝ (∂[i] u) x :=
    (contDiffAt_partialDeriv 1 hu i).differentiableAt_one
  have hdq : DifferentiableAt ℝ q x :=
    (((hd 0).fun_pow 2).const_add 1).add ((hd 1).fun_pow 2)
  have hroot : Real.sqrt (q x) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hq x))
  have hpartial (i : Fin 2) :
      (∂[i] (fun y ↦ Real.sqrt (q y))) x =
        ((∂[0] u x) * (∂[i] (∂[0] u)) x +
          (∂[1] u x) * (∂[i] (∂[1] u)) x) / Real.sqrt (q x) := by
    have hs := (hdq.hasFDerivAt.sqrt (ne_of_gt (hq x))).fderiv
    change fderiv ℝ (fun y ↦ Real.sqrt (q y)) x _ = _
    rw [hs]
    change (1 / (2 * Real.sqrt (q x))) * (∂[i] q) x = _
    dsimp only [q]
    rw [partialDeriv_add (((hd 0).fun_pow 2).const_add 1) ((hd 1).fun_pow 2),
      partialDeriv_add (differentiableAt_const 1) ((hd 0).fun_pow 2),
      partialDeriv_const, partialDeriv_sq i (hd 0), partialDeriv_sq i (hd 1)]
    cas using hroot
  change (∑ i : Fin 2, (∂[i]
    (fun y ↦ ((Real.sqrt (1 + ‖∇ u y‖ ^ 2))⁻¹ • ∇ u y) i)) x) = _
  simp only [hn, PiLp.smul_apply, smul_eq_mul, gradient_apply_eq_partialDeriv,
    inv_mul_eq_div, Fin.sum_univ_two]
  rw [partialDeriv_div 0 _ _ x (hd 0) (hdq.sqrt (ne_of_gt (hq x))) hroot,
    partialDeriv_div 1 _ _ x (hd 1) (hdq.sqrt (ne_of_gt (hq x))) hroot,
    hpartial, hpartial, partialDeriv_partialDeriv_comm_at 1 0 hu]
  have hsquare : Real.sqrt (q x) ^ 2 = q x := Real.sq_sqrt (le_of_lt (hq x))
  unfold residual
  dsimp only [q] at hsquare ⊢
  cas using [hroot, hsquare]

/-- For a C² planar graph, the divergence and nondivergence equations are equivalent. -/
theorem divergence_normalizedGradient_eq_zero_iff {u : ℝ^2 → ℝ} {x : ℝ^2}
    (hu : ContDiffAt ℝ 2 u x) :
    (∇· (fun y ↦ (Real.sqrt (1 + ‖∇ u y‖ ^ 2))⁻¹ • ∇ u y)) x = 0 ↔
      residual u x = 0 := by
  have h : Real.sqrt (1 + ‖∇ u x‖ ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by positivity))
  rw [divergence_normalizedGradient_eq hu]
  simp [h]

end PDE.Elliptic.MinimalSurface
