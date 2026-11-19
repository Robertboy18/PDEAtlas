/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.FirstVariation.Coordinates
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.JetComposition

/-!
# Classical closure regularity of Lagrangian derivatives

The matrix and value derivatives are the partial derivatives with the other variables
frozen. Their closure regularity follows from the density's continuous second jet and
the classical Jacobian of the map.
-/

@[expose] public noncomputable section

open Set
open scoped Matrix.Norms.Elementwise

namespace PDE.CalculusOfVariations

open Analysis

variable {n m : ℕ} {Ω : Set (ℝ^n)}
  {L : Matrix (Fin m) (Fin n) ℝ → ℝ^m → ℝ^n → ℝ} {u : ℝ^n → ℝ^m}

/-- Matrix-gradient entries have first-order closure regularity. -/
theorem contDiffUpToBoundary_lagrangian_matrix_deriv
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      {a | a.2.2 ∈ Ω})
    (hu : ContDiff ℝ 2 u) (k : Fin m) (i : Fin n) :
    SobolevSpace.ContDiffUpToBoundary 1
      (fun x ↦ fderiv ℝ (fun P ↦ L P (u x) x) (jacobianMatrix u x)
        (Matrix.single k i 1)) Ω := by
  have hg : ContDiff ℝ 1
      (fun x ↦ (jacobianMatrix u x, (u x, x))) :=
    (contDiff_jacobianMatrix hu).prodMk
      ((hu.of_le (by norm_num)).prodMk contDiff_id)
  have h := hL.contDiffUpToBoundary_fderiv_apply_const_comp
    (hopen.preimage (continuous_snd.comp continuous_snd)) hbounded hg
      (fun _ hx ↦ hx) (Matrix.single k i 1, (0, 0))
  apply h.congr hopen
  intro x hx
  exact fderiv_lagrangian_matrix_apply
    (hL.hasFDerivAt (hopen.preimage (continuous_snd.comp continuous_snd))
      (show (jacobianMatrix u x, (u x, x)) ∈ {a | a.2.2 ∈ Ω} from hx)).differentiableAt _

/-- Value-gradient entries have first-order closure regularity. -/
theorem contDiffUpToBoundary_lagrangian_value_deriv
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hL : ContinuousSecondJetOn
      (fun a : Matrix (Fin m) (Fin n) ℝ × (ℝ^m × ℝ^n) ↦ L a.1 a.2.1 a.2.2)
      {a | a.2.2 ∈ Ω})
    (hu : ContDiff ℝ 2 u) (k : Fin m) :
    SobolevSpace.ContDiffUpToBoundary 1
      (fun x ↦ fderiv ℝ (fun z ↦ L (jacobianMatrix u x) z x) (u x)
        (EuclideanSpace.single k 1)) Ω := by
  have hg : ContDiff ℝ 1
      (fun x ↦ (jacobianMatrix u x, (u x, x))) :=
    (contDiff_jacobianMatrix hu).prodMk
      ((hu.of_le (by norm_num)).prodMk contDiff_id)
  have h := hL.contDiffUpToBoundary_fderiv_apply_const_comp
    (hopen.preimage (continuous_snd.comp continuous_snd)) hbounded hg
      (fun _ hx ↦ hx) (0, (EuclideanSpace.single k 1, 0))
  apply h.congr hopen
  intro x hx
  exact fderiv_lagrangian_value_apply
    (hL.hasFDerivAt (hopen.preimage (continuous_snd.comp continuous_snd))
      (show (jacobianMatrix u x, (u x, x)) ∈ {a | a.2.2 ∈ Ω} from hx)).differentiableAt _

end PDE.CalculusOfVariations
