/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Strichartz.KirchhoffNewton
public import PDE.Hyperbolic.Models.Wave.Strichartz.SpacetimeOperator

/-!
# The time-integrated wave on Newtonian potentials

The Kirchhoff formula on a Newtonian potential agrees with the exterior Newtonian
kernel for every nonzero signed time. Integrating this identity discards only the
time diagonal, and the dual mixed-norm estimate supplies absolute integrability
almost everywhere. The factor `(4 * π)⁻¹` uses the Poisson normalization in dimension three.

This identifies the classical wave expression underlying the operator used in the
Strichartz argument.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace WaveEquation.Strichartz

/-- Time integration of the free wave applied to Newtonian potentials is the
Poisson-normalized exterior-kernel operator. Only the time diagonal is discarded. -/
theorem integral_kirchhoffFormula_newton_eq {F : ℝ × ℝ^3 → ℝ}
    (hF : ∀ s, ContDiff ℝ 1 (fun y ↦ F (s, y)))
    (hFc : ∀ s, HasCompactSupport (fun y ↦ F (s, y))) (t : ℝ) (x : ℝ^3) :
    (∫ s : ℝ, kirchhoffFormula (convolution (PotentialTheory.fundamentalSolution 3)
      (fun y ↦ F (s, y)) (ContinuousLinearMap.mul ℝ ℝ)) (fun _ ↦ 0) x (t - s)) =
      (4 * Real.pi)⁻¹ * spacetimeNewtonIntegral F t x := by
  rw [spacetimeNewtonIntegral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne t] with s hs
  exact kirchhoffFormula_convolution_fundamentalSolution (hF s) (hFc s) x (sub_ne_zero.mpr hs.symm)

/-- Finite dual mixed norm makes the time-integrated wave/Newton expression
absolutely integrable almost everywhere in output spacetime. -/
theorem ae_integrable_kirchhoffFormula_newton {F : ℝ × ℝ^3 → ℝ} (hF : Measurable F)
    (hFs : ∀ s, ContDiff ℝ 1 (fun y ↦ F (s, y))) (hFc : ∀ s, HasCompactSupport (fun y ↦ F (s, y)))
    (hFfin : MemLp (fun s ↦ eLpNorm (fun y ↦ F (s, y)) (12 / 11) volume) (4 / 3) volume) :
    ∀ᵐ t ∂volume, ∀ᵐ x ∂volume, Integrable (fun s : ℝ ↦ kirchhoffFormula
      (convolution (PotentialTheory.fundamentalSolution 3) (fun y ↦ F (s, y))
        (ContinuousLinearMap.mul ℝ ℝ)) (fun _ ↦ 0) x (t - s)) volume := by
  filter_upwards [ae_integrable_spacetimeNewtonKernel hF hFfin] with t ht
  filter_upwards [ht] with x hx
  apply (hx.integral_prod_left.const_mul (4 * Real.pi)⁻¹).congr
  filter_upwards [volume.ae_ne t] with s hs
  exact (kirchhoffFormula_convolution_fundamentalSolution (hFs s) (hFc s) x
    (sub_ne_zero.mpr hs.symm)).symm

end WaveEquation.Strichartz
