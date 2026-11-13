/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Calculus.Convolution
import PDE.FDeriv.Laplacian.Isometry

/-!
# Spatial regularization of a tested wave equation

Testing with a translated, reflected kernel identifies the time acceleration
of the spatial convolution. The Laplacian falls on the kernel, so the original
field needs only local spatial integrability. The force is convolved as well;
for a nonlinear equation it is not replaced by the reaction of the convolution.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Convolution

namespace WaveEquation

/-- A compact C² spatial convolution of a tested wave satisfies the forced
wave equation at each point where the tested time acceleration is known. -/
theorem hasDerivAt_deriv_convolution_of_tested_wave {n : ℕ} {u F : ℝ → ℝ^n → ℝ} {t : ℝ}
    (hu : LocallyIntegrable (u t) volume)
    (hw : ∀ φ : ℝ^n → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → HasDerivAt
      (deriv (fun s ↦ ∫ y, u s y * φ y)) ((∫ y, u t y * PDE.laplacian φ y) + ∫ y, F t y * φ y) t)
    {κ : ℝ^n → ℝ} (hκ : ContDiff ℝ 2 κ) (hκs : HasCompactSupport κ) (x : ℝ^n) :
    HasDerivAt (deriv (fun s ↦ (u s ⋆[ContinuousLinearMap.mul ℝ ℝ] κ) x))
      (PDE.laplacian (u t ⋆[ContinuousLinearMap.mul ℝ ℝ] κ) x +
        (F t ⋆[ContinuousLinearMap.mul ℝ ℝ] κ) x) t := by
  let φ : ℝ^n → ℝ := fun y ↦ κ (x - y)
  have hφ : ContDiff ℝ 2 φ := hκ.comp (contDiff_const.sub contDiff_id)
  have hφs : HasCompactSupport φ := hκs.comp_homeomorph (Homeomorph.subLeft x)
  have hΔ (y : ℝ^n) : PDE.laplacian φ y = PDE.laplacian κ (x - y) := by
    have hi := PDE.laplacian_comp_isometry_add_at (LinearIsometryEquiv.neg ℝ) x
      (hκ.contDiffAt : ContDiffAt ℝ 2 κ (-y + x))
    change PDE.laplacian (fun z ↦ κ (-z + x)) y = PDE.laplacian κ (-y + x) at hi
    simpa only [φ, sub_eq_add_neg, add_comm] using hi
  have hd := hw φ hφ hφs
  simp_rw [hΔ] at hd
  rw [PDE.laplacian_convolution_right hu hκs hκ]
  simpa only [convolution_def, ContinuousLinearMap.mul_apply', φ] using hd

end WaveEquation
