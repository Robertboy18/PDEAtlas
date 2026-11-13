/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MeanValue.PDEToMeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

/-!
# Newtonian spherical means and their time derivative

Harmonic mean value gives the exterior inverse-norm spherical average.
Inverting the center gives the interior value. The derivative of time times
this spherical mean is the exterior Newtonian kernel, away from the
characteristic sphere.
-/

@[expose] public section

open MeasureTheory Set Metric Filter PDE.Analysis
open scoped ENNReal Topology RealInnerProductSpace

namespace WaveEquation.Strichartz

/-- The exterior Newtonian shell identity follows directly from harmonic mean value. -/
theorem unitSphereAverage_inv_norm_of_lt {x : ℝ^3} {t : ℝ} (ht : 0 < t) (hxt : t < ‖x‖) :
    unitSphereAverage 3 (fun y : ℝ^3 ↦ ‖y‖⁻¹) x t = ‖x‖⁻¹ := by
  have hh : LaplacianEquation.IsHarmonicPDE 3 (fun y : ℝ^3 ↦ ‖y‖⁻¹) {y | y ≠ 0} := by
    constructor
    · intro y hy
      exact ((contDiffAt_norm (𝕜 := ℝ) hy).inv (norm_ne_zero_iff.mpr hy)).contDiffWithinAt
    · intro y hy
      have h := EuclideanLaplacian.laplacian_inv_dist_pow (n := 3) (k := 1) (x := y) (y := 0) hy
      simpa [dist_zero_right] using h
  have hx : x ≠ 0 := norm_pos_iff.mp (ht.trans hxt)
  have hball : Metric.closedBall x t ⊆ {y : ℝ^3 | y ≠ 0} := by
    intro y hy hy₀
    subst y
    have hy' : ‖x‖ ≤ t := by simpa only [Metric.mem_closedBall, dist_zero_left] using hy
    exact (not_le.mpr hxt) hy'
  have hmean := hh.hasSphereMeanValueProperty.apply hx ht hball
  rw [sphereAverage_eq_unitSphereAverage _ _ _ ht] at hmean
  exact hmean.symm

/-- Inversion moves the center of an interior Newtonian shell to its exterior. -/
theorem norm_kelvin_shell {x : ℝ^3} (hx : x ≠ 0) {t : ℝ} (ht : 0 < t)
    (ω : Metric.sphere (0 : ℝ^3) 1) :
    ‖(t ^ 2 / ‖x‖ ^ 2) • x + t • (ω : ℝ^3)‖ = (t / ‖x‖) * ‖x + t • (ω : ℝ^3)‖ := by
  have hω : ‖(ω : ℝ^3)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  have hx₀ : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [norm_add_sq_real, mul_pow, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hω, mul_one,
    real_inner_smul_left, real_inner_smul_right]
  field_simp
  ring

/-- The interior Newtonian shell is constant, by inversion and exterior mean value. -/
theorem unitSphereAverage_inv_norm_of_norm_lt {x : ℝ^3} {t : ℝ} (ht : 0 < t) (hxt : ‖x‖ < t) :
    unitSphereAverage 3 (fun y : ℝ^3 ↦ ‖y‖⁻¹) x t = t⁻¹ := by
  have hs : unitSphereArea 3 ≠ 0 := unitSphereArea_pos.ne'
  by_cases hx : x = 0
  · subst x
    have hconst (ω : Metric.sphere (0 : ℝ^3) 1) :
        ‖(0 : ℝ^3) + t • (ω : ℝ^3)‖⁻¹ = t⁻¹ := by
      rw [zero_add, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
        mem_sphere_zero_iff_norm.mp ω.property, mul_one]
    simp only [unitSphereAverage, hconst, integral_const, smul_eq_mul]
    change unitSphereArea 3 * t⁻¹ / unitSphereArea 3 = _
    field_simp
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let x' := (t ^ 2 / ‖x‖ ^ 2) • x
  have hnorm : ‖x'‖ = t ^ 2 / ‖x‖ := by
    dsimp only [x']
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
    field_simp
  have hxt' : t < ‖x'‖ := by
    rw [hnorm]
    apply (lt_div_iff₀ hxpos).mpr
    nlinarith
  have hpoint (ω : Metric.sphere (0 : ℝ^3) 1) :
      ‖x + t • (ω : ℝ^3)‖⁻¹ = (t / ‖x‖) * ‖x' + t • (ω : ℝ^3)‖⁻¹ := by
    rw [norm_kelvin_shell hx ht ω, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (div_pos ht hxpos).ne', one_mul]
  calc
    _ = (t / ‖x‖) * unitSphereAverage 3 (fun y : ℝ^3 ↦ ‖y‖⁻¹) x' t := by
      unfold unitSphereAverage
      simp_rw [hpoint]
      rw [integral_const_mul]
      ring
    _ = (t / ‖x‖) * ‖x'‖⁻¹ := by rw [unitSphereAverage_inv_norm_of_lt ht hxt']
    _ = t⁻¹ := by rw [hnorm]; field_simp

/-- Differentiating the spherical Newtonian wave profile gives the exterior Newtonian kernel. -/
theorem hasDerivAt_mul_unitSphereAverage_inv_norm (x : ℝ^3) {t : ℝ} (ht : 0 < t) (hxt : ‖x‖ ≠ t) :
    HasDerivAt (fun s ↦ s * unitSphereAverage 3 (fun y : ℝ^3 ↦ ‖y‖⁻¹) x s)
      (if t < ‖x‖ then ‖x‖⁻¹ else 0) t := by
  by_cases h : t < ‖x‖
  · rw [ite_eq_left h]
    have heq : (fun s ↦ s * unitSphereAverage 3 (fun y : ℝ^3 ↦ ‖y‖⁻¹) x s) =ᶠ[nhds t]
        (fun s ↦ s * ‖x‖⁻¹) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show t ∈ Ioo 0 ‖x‖ from ⟨ht, h⟩)] with s hs
      rw [unitSphereAverage_inv_norm_of_lt hs.1 hs.2]
    simpa only [one_mul] using ((hasDerivAt_id t).mul_const ‖x‖⁻¹).congr_of_eventuallyEq heq
  · rw [ite_eq_right h]
    have hlt : ‖x‖ < t := lt_of_le_of_ne (le_of_not_gt h) hxt
    have heq : (fun s ↦ s * unitSphereAverage 3 (fun y : ℝ^3 ↦ ‖y‖⁻¹) x s) =ᶠ[nhds t]
        (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hlt] with s hs
      have hspos : 0 < s := (norm_nonneg x).trans_lt hs
      rw [unitSphereAverage_inv_norm_of_norm_lt hspos hs, mul_inv_cancel₀ hspos.ne']
    exact (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq heq

end WaveEquation.Strichartz
