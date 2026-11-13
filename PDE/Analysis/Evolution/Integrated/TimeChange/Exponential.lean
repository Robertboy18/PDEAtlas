/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.Solution

/-!
# Reversing the exponential change of variables

Exponential multiplication is invertible on a finite time interval and
commutes with continuous linear maps. These facts let us move between an
evolution equation and its mass-shifted equation in either direction,
including when the forcing depends on the solution.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

/-- Opposite exponential weights cancel on Bochner classes. -/
@[simp]
theorem exponentialMulLp_neg_cancel
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {a b : ℝ} (gamma : ℝ)
    (u : Lp X 2 (volume.restrict (Ioc a b))) :
    exponentialMulLp (-gamma) (exponentialMulLp gamma u) = u := by
  apply Lp.ext
  filter_upwards [exponentialMulLp_apply_ae (-gamma) (exponentialMulLp gamma u),
    exponentialMulLp_apply_ae gamma u] with t ht hu
  rw [ht, hu, smul_smul]
  simp [neg_mul, Real.exp_neg]

/-- Exponential multiplication commutes with the Bochner lift of a continuous
linear map, in particular with either embedding of a Gelfand triple. -/
theorem _root_.ContinuousLinearMap.compLpL_exponentialMulLp
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : X →L[ℝ] Y) {a b : ℝ} (gamma : ℝ)
    (u : Lp X 2 (volume.restrict (Ioc a b))) :
    A.compLpL 2 (volume.restrict (Ioc a b)) (exponentialMulLp gamma u) =
      exponentialMulLp gamma (A.compLpL 2 (volume.restrict (Ioc a b)) u) := by
  apply Lp.ext
  filter_upwards [A.coeFn_compLpL (exponentialMulLp gamma u),
    exponentialMulLp_apply_ae gamma u,
    exponentialMulLp_apply_ae gamma (A.compLpL 2 (volume.restrict (Ioc a b)) u),
    A.coeFn_compLpL u] with t hA hu hweight hAu
  rw [hA, hu, hweight, hAu, map_smul]

/-- Multiplying a weak solution by `exp (-gamma * (t-a))` adds the pivot mass
`gamma J*J` to its form. The initial datum is unchanged because the weight
equals one at the initial time. -/
theorem IsGelfandIntegratedWeakSolution.exponential_gardingShift
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {a b gamma : ℝ} {T : GelfandTriple (V := V) (H := H)}
    {B : ℝ → V →L[ℝ] StrongDual ℝ V}
    (hBmeas : ∀ v, AEStronglyMeasurable (fun t ↦ B t v)
      (volume.restrict (Ioc a b)))
    (MB : ℝ)
    (hBbound : ∀ᵐ t ∂volume.restrict (Ioc a b), ‖B t‖ ≤ MB)
    {ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    {u : Lp V 2 (volume.restrict (Ioc a b))} {uInit : H}
    (hu : IsGelfandIntegratedWeakSolution T B ell u uInit) :
    IsGelfandIntegratedWeakSolution T (gardingShiftForm T B gamma)
      (exponentialMulLp (-gamma) ell) (exponentialMulLp (-gamma) u) uInit := by
  have hshift : gardingShiftForm T (gardingShiftForm T B gamma) (-gamma) = B := by
    funext t
    ext v w
    simp only [gardingShiftForm_apply]
    ring
  have hcancel : exponentialMulLp (-(-gamma)) (exponentialMulLp (-gamma) ell) = ell :=
    exponentialMulLp_neg_cancel (-gamma) ell
  have hweighted : IsGelfandIntegratedWeakSolution T
      (gardingShiftForm T (gardingShiftForm T B gamma) (-gamma))
      (exponentialMulLp (-(-gamma)) (exponentialMulLp (-gamma) ell)) u uInit := by
    simpa only [hshift, hcancel] using hu
  apply hweighted.of_exponential_gardingShift
    (aestronglyMeasurable_gardingShiftForm T hBmeas)
    (MB + ‖gamma‖ * ‖T.energyToDual‖)
  filter_upwards [hBbound] with t ht
  exact (norm_gardingShiftForm_le T B gamma t).trans (add_le_add ht le_rfl)

end PDE.Analysis.Evolution
