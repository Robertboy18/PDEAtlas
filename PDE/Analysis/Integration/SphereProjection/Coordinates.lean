/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.InnerProductSpace.Euclidean.CoordinateProjection
public import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Signed radial coordinates over a Euclidean ball

The two hemispheres are parametrized by the open unit ball in one fewer
coordinate. A nonzero signed radius distinguishes them. The chart has norm
exactly the absolute radius, in every dimension.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

variable {n : ℕ}

/-- Signed radial coordinates based on the two graphs over the unit ball. -/
def hemisphereRadialMap (p : ℝ^(n + 1)) : ℝ^(n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i : Fin n ↦ |p (Fin.last n)| * p i.castSucc)
    (p (Fin.last n) * √(1 - ‖coordinateProjection p‖ ^ 2)))

/-- The unit ball times a nonzero signed radius of absolute value less than one. -/
def hemisphereRadialDomain : Set (ℝ^(n + 1)) :=
  {p | ‖coordinateProjection p‖ ^ 2 < 1 ∧ |p (Fin.last n)| < 1 ∧ p (Fin.last n) ≠ 0}

/-- Retained coordinates of the signed radial chart. -/
@[simp]
theorem hemisphereRadialMap_castSucc (p : ℝ^(n + 1)) (i : Fin n) :
    hemisphereRadialMap p i.castSucc = |p (Fin.last n)| * p i.castSucc := by
  simp [hemisphereRadialMap]

/-- The last coordinate records the signed height of the hemisphere. -/
@[simp]
theorem hemisphereRadialMap_last (p : ℝ^(n + 1)) :
    hemisphereRadialMap p (Fin.last n) =
      p (Fin.last n) * √(1 - ‖coordinateProjection p‖ ^ 2) := by
  simp [hemisphereRadialMap]

/-- Projection of the signed radial chart is radial scaling in the base ball. -/
@[simp]
theorem coordinateProjection_hemisphereRadialMap (p : ℝ^(n + 1)) :
    coordinateProjection (hemisphereRadialMap p) =
      |p (Fin.last n)| • coordinateProjection p := by
  ext i
  simp

/-- The hemisphere has strictly positive height over the open base ball. -/
theorem hemisphereRadialDomain_sqrt_pos {p : ℝ^(n + 1)}
    (hp : p ∈ hemisphereRadialDomain) :
    0 < √(1 - ‖coordinateProjection p‖ ^ 2) :=
  Real.sqrt_pos.2 (sub_pos.2 hp.1)

/-- The norm of the parametrized point is the absolute signed radius. -/
theorem norm_hemisphereRadialMap {p : ℝ^(n + 1)} (hp : p ∈ hemisphereRadialDomain) :
    ‖hemisphereRadialMap p‖ = |p (Fin.last n)| := by
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [norm_sq_coordinateProjection, coordinateProjection_hemisphereRadialMap,
    hemisphereRadialMap_last, norm_smul, Real.norm_eq_abs, abs_abs, mul_pow, mul_pow,
    Real.sq_sqrt (sub_nonneg.2 hp.1.le), sq_abs]
  ring

/-- The chart is differentiable away from the equator and the base-ball boundary. -/
theorem differentiableAt_hemisphereRadialMap {p : ℝ^(n + 1)}
    (hp : p ∈ hemisphereRadialDomain) : DifferentiableAt ℝ hemisphereRadialMap p := by
  apply (differentiableAt_piLp 2).2
  intro i
  have hc (j : Fin (n + 1)) : DifferentiableAt ℝ (fun q : ℝ^(n + 1) ↦ q j) p :=
    (PiLp.hasFDerivAt_apply 2 p j).differentiableAt
  have hs : DifferentiableAt ℝ
      (fun q : ℝ^(n + 1) ↦ √(1 - ‖coordinateProjection q‖ ^ 2)) p :=
    ((hasFDerivAt_const (x := p) (c := (1 : ℝ))).sub
      coordinateProjection.hasFDerivAt.norm_sq).sqrt
        (sub_pos.2 hp.1).ne' |>.differentiableAt
  cases i using Fin.lastCases with
  | last => simpa only [hemisphereRadialMap_last] using (hc (Fin.last n)).fun_mul hs
  | cast i =>
      simpa only [hemisphereRadialMap_castSucc] using
        ((hc (Fin.last n)).abs hp.2.2).fun_mul (hc i.castSucc)

/-- The two hemispheres have disjoint images, and each radial chart is injective. -/
theorem injOn_hemisphereRadialMap :
    Set.InjOn (hemisphereRadialMap (n := n)) hemisphereRadialDomain := by
  intro p hp q hq he
  have hr : |p (Fin.last n)| = |q (Fin.last n)| := by
    simpa only [norm_hemisphereRadialMap hp, norm_hemisphereRadialMap hq] using
      congrArg norm he
  have hxy : coordinateProjection p = coordinateProjection q := by
    have h := congrArg coordinateProjection he
    simp only [coordinateProjection_hemisphereRadialMap, ← hr] at h
    exact (smul_right_injective _ (abs_ne_zero.2 hp.2.2)) h
  have hz : p (Fin.last n) = q (Fin.last n) := by
    have h := congrArg (fun z : ℝ^(n + 1) ↦ z (Fin.last n)) he
    simp only [hemisphereRadialMap_last, ← hxy] at h
    exact mul_right_cancel₀ (hemisphereRadialDomain_sqrt_pos hp).ne' h
  ext i
  cases i using Fin.lastCases with
  | last => exact hz
  | cast i => exact congrArg (fun z : ℝ^n ↦ z i) hxy

end PDE.Analysis
