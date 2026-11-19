/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.CanonicalForm2D.Algebra
public import PDE.Analysis.Calculus.Jacobian.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import CAS.ExactTactic

/-!
# A fixed shear of the independent variables

The shear and its inverse are smooth. Its chain rule transports null coordinate
covectors and preserves the determinant of a subsequently constructed chart.
-/

@[expose] public noncomputable section

open PDE.Analysis

namespace Hyperbolic.CanonicalForm2D

/-- A shear of the first independent variable by the second. -/
def shearCoordinates (k : ℝ) (x : ℝ^2) : ℝ^2 :=
  !₂[x 0 + k * x 1, x 1]

/-- Reversing the shear parameter gives its inverse. -/
theorem shearCoordinates_neg_apply (k : ℝ) (x : ℝ^2) :
    shearCoordinates (-k) (shearCoordinates k x) = x := by
  ext i
  fin_cases i
  · change x 0 + k * x 1 + -k * x 1 = x 0
    cas
  · rfl

/-- A fixed shear is smooth at every point. -/
theorem contDiffAt_shearCoordinates (k : ℝ) (x : ℝ^2) {r : WithTop ℕ∞} :
    ContDiffAt ℝ r (shearCoordinates k) x := by
  refine (contDiffAt_piLp 2).mpr fun i ↦ ?_
  fin_cases i
  · exact (contDiffAt_piLp_apply 2 (i := (0 : Fin 2))).add
      (contDiffAt_const.mul (contDiffAt_piLp_apply 2 (i := (1 : Fin 2))))
  · exact contDiffAt_piLp_apply 2

private theorem partialDeriv_shearCoordinates_zero (k : ℝ) (i : Fin 2) (x : ℝ^2) :
    (∂[i] (fun y ↦ shearCoordinates k y 0)) x = if i = 0 then 1 else k := by
  change (∂[i] (fun y : ℝ^2 ↦ y 0 + k * y 1)) x = _
  have h₀ : DifferentiableAt ℝ (fun y : ℝ^2 ↦ y 0) x :=
    (EuclideanSpace.proj 0 : ℝ^2 →L[ℝ] ℝ).differentiableAt
  have h₁ : DifferentiableAt ℝ (fun y : ℝ^2 ↦ k * y 1) x := (differentiableAt_const k).mul
      (EuclideanSpace.proj 1 : ℝ^2 →L[ℝ] ℝ).differentiableAt
  have hadd := PDE.partialDeriv_add (i := i) h₀ h₁
  change (∂[i] (fun y : ℝ^2 ↦ y 0 + k * y 1)) x =
    (∂[i] (fun y : ℝ^2 ↦ y 0)) x + (∂[i] (fun y : ℝ^2 ↦ k * y 1)) x at hadd
  rw [hadd]
  have hmul : (∂[i] (fun y : ℝ^2 ↦ k * y 1)) x =
      k * (∂[i] (fun y : ℝ^2 ↦ y 1)) x := PDE.partialDeriv_const_smul k
  rw [hmul]
  fin_cases i <;> simp [PDE.partialDeriv_coord]

/-- The first derivative through a shear has no transverse correction. -/
theorem partialDeriv_zero_comp_shearCoordinates (k : ℝ) (f : ℝ^2 → ℝ) (x : ℝ^2)
    (hf : DifferentiableAt ℝ f (shearCoordinates k x)) :
    (∂[0] (f ∘ shearCoordinates k)) x = (∂[0] f) (shearCoordinates k x) := by
  change (∂[0] (fun y ↦ f (shearCoordinates k y))) x = _
  rw [PDE.partialDeriv_comp 0 f (shearCoordinates k) x hf
    ((contDiffAt_shearCoordinates k x (r := 1)).differentiableAt (by norm_num))]
  simp only [Fin.sum_univ_two, partialDeriv_shearCoordinates_zero, ↓reduceIte, mul_one]
  change _ + _ * (∂[0] (fun y : ℝ^2 ↦ y 1)) x = _
  simp [PDE.partialDeriv_coord]

/-- The second derivative through a shear is the corresponding linear combination. -/
theorem partialDeriv_one_comp_shearCoordinates (k : ℝ) (f : ℝ^2 → ℝ) (x : ℝ^2)
    (hf : DifferentiableAt ℝ f (shearCoordinates k x)) :
    (∂[1] (f ∘ shearCoordinates k)) x =
      k * (∂[0] f) (shearCoordinates k x) + (∂[1] f) (shearCoordinates k x) := by
  change (∂[1] (fun y ↦ f (shearCoordinates k y))) x = _
  rw [PDE.partialDeriv_comp 1 f (shearCoordinates k) x hf
    ((contDiffAt_shearCoordinates k x (r := 1)).differentiableAt (by norm_num))]
  simp only [Fin.sum_univ_two, partialDeriv_shearCoordinates_zero, Fin.isValue,
    one_ne_zero, ↓reduceIte]
  change _ * k + _ * (∂[1] (fun y : ℝ^2 ↦ y 1)) x = _
  simp [PDE.partialDeriv_coord, mul_comm]

/-- Precomposition with a shear preserves the signed Jacobian determinant. -/
theorem det_jacobianMatrix_comp_shearCoordinates (k : ℝ) (Φ : ℝ^2 → ℝ^2) (x : ℝ^2)
    (hΦ : DifferentiableAt ℝ Φ (shearCoordinates k x)) :
    (jacobianMatrix (Φ ∘ shearCoordinates k) x).det =
      (jacobianMatrix Φ (shearCoordinates k x)).det := by
  have hcoord (j : Fin 2) : DifferentiableAt ℝ (fun y ↦ Φ y j) (shearCoordinates k x) :=
    (EuclideanSpace.proj j : ℝ^2 →L[ℝ] ℝ).differentiableAt.comp _ hΦ
  simp only [Matrix.det_fin_two, jacobianMatrix, jacobianColumn, Matrix.of_apply]
  change (∂[0] ((fun y ↦ Φ y 0) ∘ shearCoordinates k)) x *
      (∂[1] ((fun y ↦ Φ y 1) ∘ shearCoordinates k)) x -
      (∂[1] ((fun y ↦ Φ y 0) ∘ shearCoordinates k)) x *
      (∂[0] ((fun y ↦ Φ y 1) ∘ shearCoordinates k)) x = _
  rw [partialDeriv_zero_comp_shearCoordinates k _ x (hcoord 0),
    partialDeriv_one_comp_shearCoordinates k _ x (hcoord 1),
    partialDeriv_one_comp_shearCoordinates k _ x (hcoord 0),
    partialDeriv_zero_comp_shearCoordinates k _ x (hcoord 1)]
  ring

end Hyperbolic.CanonicalForm2D
