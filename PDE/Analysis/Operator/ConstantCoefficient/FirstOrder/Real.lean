/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Matrix.Complexification.Euclidean
public import PDE.Analysis.Operator.ConstantCoefficient.FirstOrder.Uniqueness

/-!
# Classical uniqueness for real constant matrix systems

Complexification preserves the derivatives and full matrix action.
The generic constant-coefficient uniqueness theorem therefore applies to real
classical solutions without assumptions on their growth or the matrix spectra.
-/

@[expose] public noncomputable section

open Set
open scoped Matrix.Norms.L2Operator

namespace PDE.Analysis

variable {n m : ℕ}

/-- Complexification carries a real first-order equation to the
corresponding complex equation, at the same spacetime point. -/
theorem firstOrder_ofReal_eq_zero
    (B : Fin n → Matrix (Fin m) (Fin m) ℝ)
    {u : ℝ × ℝ^n → ℝ^m} {p : ℝ × ℝ^n} (hu : DifferentiableAt ℝ u p)
    (heq : fderiv ℝ u p (1, 0) + ∑ j,
      Matrix.toEuclideanCLM (𝕜 := ℝ) (B j)
        (fderiv ℝ u p (0, EuclideanSpace.single j 1)) = 0) :
    fderiv ℝ (EuclideanSpace.ofRealCLM (Fin m) ∘ u) p (1, 0) + ∑ j,
      Matrix.toEuclideanCLM (𝕜 := ℂ) ((B j).map Complex.ofReal)
        (fderiv ℝ (EuclideanSpace.ofRealCLM (Fin m) ∘ u) p
          (0, EuclideanSpace.single j 1)) = 0 := by
  let C := EuclideanSpace.ofRealCLM (Fin m)
  have hd := C.hasFDerivAt.comp p hu.hasFDerivAt
  rw [hd.fderiv]
  have h := congrArg C heq
  simpa only [map_add, map_sum, map_zero, ContinuousLinearMap.comp_apply,
    C, EuclideanSpace.ofRealCLM_toEuclideanCLM] using h

/-- Real classical solutions with the same initial data agree. The
equations hold in the open slab and the solutions are continuous at its time
faces; neither growth nor a spectral condition is imposed. -/
theorem eq_of_realMatrix_firstOrder
    (B : Fin n → Matrix (Fin m) (Fin m) ℝ) {u v : ℝ × ℝ^n → ℝ^m} {T : ℝ}
    (hT : 0 ≤ T)
    (hu : ContDiffOn ℝ 1 u (Ioo 0 T ×ˢ univ))
    (hv : ContDiffOn ℝ 1 v (Ioo 0 T ×ˢ univ))
    (huc : ContinuousOn u (Icc 0 T ×ˢ univ))
    (hvc : ContinuousOn v (Icc 0 T ×ˢ univ))
    (hi : ∀ x, u (0, x) = v (0, x))
    (heu : ∀ t ∈ Ioo 0 T, ∀ x, fderiv ℝ u (t, x) (1, 0) + ∑ j,
      Matrix.toEuclideanCLM (𝕜 := ℝ) (B j)
        (fderiv ℝ u (t, x) (0, EuclideanSpace.single j 1)) = 0)
    (hev : ∀ t ∈ Ioo 0 T, ∀ x, fderiv ℝ v (t, x) (1, 0) + ∑ j,
      Matrix.toEuclideanCLM (𝕜 := ℝ) (B j)
        (fderiv ℝ v (t, x) (0, EuclideanSpace.single j 1)) = 0)
    (x : ℝ^n) : u (T, x) = v (T, x) := by
  let C := EuclideanSpace.ofRealCLM (Fin m)
  have hcu : ContDiffOn ℝ 1 (C ∘ u) (Ioo 0 T ×ˢ univ) :=
    C.contDiff.comp_contDiffOn hu
  have hcv : ContDiffOn ℝ 1 (C ∘ v) (Ioo 0 T ×ˢ univ) :=
    C.contDiff.comp_contDiffOn hv
  have hpu (t : ℝ) (ht : t ∈ Ioo 0 T) (y : ℝ^n) : DifferentiableAt ℝ u (t, y) := by
    have hopen : IsOpen (Ioo 0 T ×ˢ (univ : Set (ℝ^n))) :=
      isOpen_Ioo.prod isOpen_univ
    have hp : (t, y) ∈ Ioo 0 T ×ˢ (univ : Set (ℝ^n)) := ⟨ht, mem_univ y⟩
    exact (hu.contDiffAt (hopen.mem_nhds hp)).differentiableAt one_ne_zero
  have hpv (t : ℝ) (ht : t ∈ Ioo 0 T) (y : ℝ^n) : DifferentiableAt ℝ v (t, y) := by
    have hopen : IsOpen (Ioo 0 T ×ˢ (univ : Set (ℝ^n))) :=
      isOpen_Ioo.prod isOpen_univ
    have hp : (t, y) ∈ Ioo 0 T ×ˢ (univ : Set (ℝ^n)) := ⟨ht, mem_univ y⟩
    exact (hv.contDiffAt (hopen.mem_nhds hp)).differentiableAt one_ne_zero
  have h := eq_of_firstOrder
    (fun j ↦ Matrix.toEuclideanCLM (𝕜 := ℂ) ((B j).map Complex.ofReal))
    hT hcu hcv (C.continuous.comp_continuousOn huc)
    (C.continuous.comp_continuousOn hvc)
    (fun y ↦ congrArg C (hi y))
    (fun t ht y ↦ firstOrder_ofReal_eq_zero B (hpu t ht y) (heu t ht y))
    (fun t ht y ↦ firstOrder_ofReal_eq_zero B (hpv t ht y) (hev t ht y)) x
  have hr := congrArg (EuclideanSpace.realPartCLM (Fin m)) h
  simpa only [Function.comp_def, C, EuclideanSpace.realPartCLM_ofRealCLM] using hr

end PDE.Analysis
