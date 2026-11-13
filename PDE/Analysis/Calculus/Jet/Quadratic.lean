/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Quadratic realization of a second jet

A value, a continuous linear map, and a symmetric continuous bilinear map are the
second jet of a globally smooth quadratic polynomial. For the actual second derivative
of a `C²` germ, symmetry follows from Schwarz's theorem. Thus every such germ has a
globally smooth representative with exactly the same value and first two derivatives
at its base point.

The construction works in real normed spaces without finite-dimensionality or
completeness. Equality of second derivatives is equality of the full bilinear maps.
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace PDE.Analysis

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The quadratic polynomial centered at `x` with value `z`, linear part `A`, and
bilinear part `B`. Only the symmetric part of `B` contributes. -/
def quadraticJet (x : E) (z : F) (A : E →L[ℝ] F)
    (B : E →L[ℝ] E →L[ℝ] F) (y : E) : F :=
  z + A (y - x) + (1 / 2 : ℝ) • B (y - x) (y - x)

/-- Evaluation at the center recovers the prescribed value. -/
@[simp]
theorem quadraticJet_self (x : E) (z : F) (A : E →L[ℝ] F)
    (B : E →L[ℝ] E →L[ℝ] F) : quadraticJet x z A B x = z := by
  simp [quadraticJet]

/-- A continuous bilinear polynomial is smooth at every order. -/
theorem contDiff_quadraticJet (x : E) (z : F) (A : E →L[ℝ] F)
    (B : E →L[ℝ] E →L[ℝ] F) : ContDiff ℝ ∞ (quadraticJet x z A B) := by
  have hshift : ContDiff ℝ ∞ (fun y : E ↦ y - x) :=
    contDiff_id.sub contDiff_const
  exact (contDiff_const.add (A.contDiff.comp hshift)).add
    (contDiff_const.smul ((B.contDiff.comp hshift).clm_apply hshift))

/-- Differentiating the diagonal bilinear term symmetrizes its two slots. -/
theorem hasFDerivAt_quadraticJet (x : E) (z : F) (A : E →L[ℝ] F)
    (B : E →L[ℝ] E →L[ℝ] F) (y : E) :
    HasFDerivAt (quadraticJet x z A B)
      (A + (1 / 2 : ℝ) • (B (y - x) + B.flip (y - x))) y := by
  have hshift := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const x
  have hlinear : HasFDerivAt (fun y ↦ A (y - x)) A y := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      A.hasFDerivAt.comp y hshift
  have hbilinear : HasFDerivAt (fun y ↦ B (y - x) (y - x))
      (B (y - x) + B.flip (y - x)) y := by
    simpa using (B.hasFDerivAt.comp y hshift).clm_apply hshift
  exact (hlinear.const_add z).add (hbilinear.const_smul (1 / 2 : ℝ))

/-- The actual first derivative of the quadratic polynomial, at an arbitrary point. -/
theorem fderiv_quadraticJet (x : E) (z : F) (A : E →L[ℝ] F)
    (B : E →L[ℝ] E →L[ℝ] F) (y : E) :
    fderiv ℝ (quadraticJet x z A B) y =
      A + (1 / 2 : ℝ) • (B (y - x) + B.flip (y - x)) :=
  (hasFDerivAt_quadraticJet x z A B y).fderiv

/-- Evaluation of the first derivative at the center recovers the linear part. -/
@[simp]
theorem fderiv_quadraticJet_self (x : E) (z : F) (A : E →L[ℝ] F)
    (B : E →L[ℝ] E →L[ℝ] F) :
    fderiv ℝ (quadraticJet x z A B) x = A := by
  simp [fderiv_quadraticJet]

/-- The second derivative is constant and equals the symmetric part of the bilinear data. -/
theorem fderiv_fderiv_quadraticJet (x : E) (z : F) (A : E →L[ℝ] F)
    (B : E →L[ℝ] E →L[ℝ] F) (y : E) :
    fderiv ℝ (fderiv ℝ (quadraticJet x z A B)) y =
      (1 / 2 : ℝ) • (B + B.flip) := by
  have hshift := (hasFDerivAt_id (𝕜 := ℝ) y).sub_const x
  have hB : HasFDerivAt (fun y ↦ B (y - x)) B y := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      B.hasFDerivAt.comp y hshift
  have hflip : HasFDerivAt (fun y ↦ B.flip (y - x)) B.flip y := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      B.flip.hasFDerivAt.comp y hshift
  rw [show fderiv ℝ (quadraticJet x z A B) =
    (fun y ↦ A + (1 / 2 : ℝ) • (B (y - x) + B.flip (y - x))) from
      funext (fderiv_quadraticJet x z A B)]
  exact (((hB.add hflip).const_smul (1 / 2 : ℝ)).const_add A).fderiv

/-- Symmetric bilinear data are realized without losing any mixed second derivatives. -/
theorem fderiv_fderiv_quadraticJet_of_symmetric (x : E) (z : F)
    (A : E →L[ℝ] F) (B : E →L[ℝ] E →L[ℝ] F)
    (hB : ∀ v w, B v w = B w v) (y : E) :
    fderiv ℝ (fderiv ℝ (quadraticJet x z A B)) y = B := by
  have hflip : B.flip = B := by
    ext v w
    exact hB w v
  rw [fderiv_fderiv_quadraticJet, hflip, ← two_smul ℝ B, smul_smul]
  norm_num

/-- Every `C²` germ has a globally smooth realization of its full second jet.
Symmetry is a consequence of the original map's regularity. -/
theorem exists_contDiff_same_secondJet {u : E → F} {x : E}
    (hu : ContDiffAt ℝ 2 u x) :
    ∃ q : E → F, ContDiff ℝ ∞ q ∧ q x = u x ∧
      fderiv ℝ q x = fderiv ℝ u x ∧
      fderiv ℝ (fderiv ℝ q) x = fderiv ℝ (fderiv ℝ u) x := by
  refine ⟨quadraticJet x (u x) (fderiv ℝ u x) (fderiv ℝ (fderiv ℝ u) x),
    contDiff_quadraticJet .., quadraticJet_self .., fderiv_quadraticJet_self .., ?_⟩
  exact fderiv_fderiv_quadraticJet_of_symmetric _ _ _ _
    (hu.isSymmSndFDerivAt (by norm_num)) _

end PDE.Analysis
