/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.ScaleDerivative.Profiles
import PDE.Spaces.Sobolev.Approximation.Mollification.KernelMoment
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Derivatives of the scaled mollifier

At positive height, both spatial and scale derivatives are dilates of the signed
profiles, with one additional inverse scale. The scale statement is local to
positive height; the totalized value at height zero plays no role.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace SobolevSpace.Approximation.Mollifier

variable {n : ℕ}

/-- A spatial derivative of the scaled kernel is the corresponding dilated profile. -/
theorem partialDeriv_scaled (μ : Mollifier n) {t : ℝ} (ht : 0 < t)
    (i : Fin n) (x : ℝ^n) :
    (∂[i] (scaled μ t)) x =
      (t⁻¹)^n * t⁻¹ * μ.spatialDerivativeProfile i (t⁻¹ • x) := by
  change fderiv ℝ (scaled μ t) x (EuclideanSpace.single i 1) = _
  rw [fderiv_scaled_apply μ ht]
  exact (mul_assoc _ _ _).symm

/-- Differentiating the positive scale gives the dilated normal derivative profile. -/
theorem hasDerivAt_scaled (μ : Mollifier n) {t : ℝ} (ht : 0 < t) (x : ℝ^n) :
    HasDerivAt (fun r : ℝ ↦ scaled μ r x)
      ((t⁻¹)^n * t⁻¹ * μ.normalDerivativeProfile (t⁻¹ • x)) t := by
  have hpow : HasDerivAt (fun r : ℝ ↦ (r⁻¹)^n)
      (-(n : ℝ) * (t⁻¹)^n * t⁻¹) t := by
    convert (hasDerivAt_inv ht.ne').pow n using 1
    cases n with
    | zero => simp
    | succ k =>
      simp only [Nat.cast_succ, Nat.add_sub_cancel, pow_succ, inv_pow]
      ring
  have hρ := (μ.smooth.differentiable (by simp) (t⁻¹ • x)).hasFDerivAt
  have hcomp := hρ.comp_hasDerivAt t ((hasDerivAt_inv ht.ne').smul_const x)
  have hraw := hpow.mul hcomp
  dsimp only [Function.comp_def] at hraw
  have hfactor :
      -(n : ℝ) * (t⁻¹)^n * t⁻¹ * μ.ρ (t⁻¹ • x) +
          (t⁻¹)^n * fderiv ℝ μ.ρ (t⁻¹ • x) (-(t^2)⁻¹ • x) =
        (t⁻¹)^n * t⁻¹ * μ.normalDerivativeProfile (t⁻¹ • x) := by
    simp only [normalDerivativeProfile, map_smul, smul_eq_mul, inv_pow]
    ring
  rw [hfactor] at hraw
  apply hraw.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with r hr
  exact congrFun (scaled_of_pos μ hr) x

/-- Pointwise scale derivative formula at positive height. -/
theorem deriv_scaled (μ : Mollifier n) {t : ℝ} (ht : 0 < t) (x : ℝ^n) :
    deriv (fun r : ℝ ↦ scaled μ r x) t =
      (t⁻¹)^n * t⁻¹ * μ.normalDerivativeProfile (t⁻¹ • x) :=
  (μ.hasDerivAt_scaled ht x).deriv

end SobolevSpace.Approximation.Mollifier
