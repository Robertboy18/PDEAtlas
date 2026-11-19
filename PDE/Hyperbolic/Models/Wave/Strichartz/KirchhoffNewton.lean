/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Convolution.SphericalMean
public import PDE.Elliptic.PotentialTheory.FundamentalSolution
public import PDE.Hyperbolic.Models.Wave.KirchhoffRepresentation
public import PDE.Hyperbolic.Models.Wave.Strichartz.ShellConvolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import CAS.ExactTactic
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar

/-!
# Kirchhoff evolution of the Newtonian potential

For compactly supported C¹ data, the free wave of its Newtonian potential equals
convolution with the exterior Newtonian kernel at every nonzero signed time.
The normalized identity uses the fundamental solution of the Laplacian,
including its factor `1 / (4 * π)`.

The proof differentiates the spherical average of the potential. Local integrability of the
Newtonian kernel and compact support justify convolution regularity and Fubini.
-/

@[expose] public section

open MeasureTheory PDE.Analysis Set Filter
open scoped Topology

namespace WaveEquation.Strichartz

/-- The free wave of the Newtonian potential is the exterior Newtonian convolution. -/
private theorem kirchhoffFormula_integral_inv_norm_of_pos {f : ℝ^3 → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (x : ℝ^3) {t : ℝ} (ht : 0 < t) :
    kirchhoffFormula (fun z ↦ ∫ y, ‖z - y‖⁻¹ * f y) (fun _ ↦ 0) x t =
      ∫ y, exteriorNewtonKernel t (x - y) * f y := by
  have hk : LocallyIntegrable (fun z : ℝ^3 ↦ ‖z‖⁻¹) volume := by
    apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1)
      (by norm_num [finrank_euclideanSpace_fin]) (by norm_num [finrank_euclideanSpace_fin])
    · refine Filter.Eventually.of_forall fun z ↦ ?_
      simp only [norm_inv, norm_norm, one_mul, Real.rpow_neg_one, le_refl]
    · exact measurable_norm.inv.aestronglyMeasurable
  have hg (z : ℝ^3) : (∫ y, ‖z - y‖⁻¹ * f y) =
      convolution (fun y : ℝ^3 ↦ ‖y‖⁻¹) f (ContinuousLinearMap.mul ℝ ℝ) volume z := by
    have h := integral_sub_left_eq_self (fun y : ℝ^3 ↦ ‖y‖⁻¹ * f (z - y)) volume z
    simpa only [sub_sub_cancel, convolution_mul] using h
  have hgc : ContDiff ℝ 1 (fun z : ℝ^3 ↦ ∫ y, ‖z - y‖⁻¹ * f y) := by
    simp_rw [hg]
    exact hfc.contDiff_convolution_right (L := ContinuousLinearMap.mul ℝ ℝ) hk hf
  have hderiv := hasDerivAt_integral_mul_unitSphereAverage_inv_norm
    (hf.continuous.integrable_of_hasCompactSupport hfc) x ht
  have heq (s : ℝ) : s * unitSphereAverage 3 (fun z ↦ ∫ y, ‖z - y‖⁻¹ * f y) x s =
      ∫ y, (s * unitSphereAverage 3 (fun z : ℝ^3 ↦ ‖z‖⁻¹) y s) * f (x - y) := by
    rw [unitSphereAverage_integral_convolution hk measurable_norm.inv hf.continuous hfc,
      ← integral_const_mul]
    have h := integral_sub_left_eq_self
      (fun y ↦ (s * unitSphereAverage 3 (fun z : ℝ^3 ↦ ‖z‖⁻¹) y s) * f (x - y)) volume x
    simpa only [sub_sub_cancel, mul_assoc] using h
  have hd : HasDerivAt (fun s ↦ s * unitSphereAverage 3 (fun z ↦ ∫ y, ‖z - y‖⁻¹ * f y) x s)
      (∫ y, exteriorNewtonKernel t (x - y) * f y) t :=
    hderiv.congr_of_eventuallyEq (Filter.Eventually.of_forall heq)
  rw [kirchhoffFormula_eq_sphericalMean hgc continuous_const, hd.deriv]
  simp only [unitSphereAverage, integral_zero, zero_div, mul_zero, add_zero]

/-- The convolution identity at every nonzero signed time. -/
theorem kirchhoffFormula_integral_inv_norm {f : ℝ^3 → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (x : ℝ^3) {t : ℝ} (ht : t ≠ 0) :
    kirchhoffFormula (fun z ↦ ∫ y, ‖z - y‖⁻¹ * f y) (fun _ ↦ 0) x t =
      ∫ y, exteriorNewtonKernel |t| (x - y) * f y := by
  have heven : kirchhoffFormula (fun z ↦ ∫ y, ‖z - y‖⁻¹ * f y) (fun _ ↦ 0) x t =
      kirchhoffFormula (fun z ↦ ∫ y, ‖z - y‖⁻¹ * f y) (fun _ ↦ 0) x |t| := by
    simp only [kirchhoffFormula, abs_abs, mul_zero]
  rw [heven]
  exact kirchhoffFormula_integral_inv_norm_of_pos hf hfc x (abs_pos.mpr ht)

/-- The Poisson-normalized inverse Laplacian gives the exact free-wave kernel at signed time. -/
theorem kirchhoffFormula_convolution_fundamentalSolution {f : ℝ^3 → ℝ}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (x : ℝ^3) {t : ℝ} (ht : t ≠ 0) :
    kirchhoffFormula (convolution (PotentialTheory.fundamentalSolution 3) f
      (ContinuousLinearMap.mul ℝ ℝ)) (fun _ ↦ 0) x t = (4 * Real.pi)⁻¹ * ∫ y,
      exteriorNewtonKernel |t| (x - y) * f y := by
  let c := (4 * Real.pi)⁻¹
  have hkernel (y : ℝ^3) : PotentialTheory.fundamentalSolution 3 y = c * ‖y‖⁻¹ := by
    rw [PotentialTheory.fundamentalSolution_of_three_le (by norm_num), unitBallVolume_three]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
    have hc : (3 : ℝ) * (4 * Real.pi / 3) = 4 * Real.pi := by cas
    rw [hc, one_div, mul_inv]
  have heq : convolution (PotentialTheory.fundamentalSolution 3) f
      (ContinuousLinearMap.mul ℝ ℝ) = fun z : ℝ^3 ↦ ∫ y, ‖z - y‖⁻¹ * (c * f y) := by
    funext z
    rw [convolution_mul]
    simp_rw [hkernel]
    have h := integral_sub_left_eq_self (fun y : ℝ^3 ↦ ‖y‖⁻¹ * (c * f (z - y))) volume z
    simpa only [sub_sub_cancel, mul_assoc, mul_left_comm, mul_comm] using h.symm
  rw [heq, kirchhoffFormula_integral_inv_norm (contDiff_const.mul hf) hfc.mul_left x ht]
  simp_rw [mul_left_comm _ c]
  exact integral_const_mul c _

end WaveEquation.Strichartz
