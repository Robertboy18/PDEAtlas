/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Boundary.Continuity.Barrier.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# First derivatives of the angular barrier

After dividing the displacement by its radius, every coordinate derivative is
`r^(a-1)` times a bounded polynomial in unit-vector coordinates. This gives the
square-integrable gradient needed at a boundary vertex, even when `a < 1`.
-/

@[expose] public noncomputable section

namespace PDE.Elliptic.BoundaryContinuity

open PDE.Analysis.Radial
open scoped InnerProductSpace

variable {n : ℕ}

/-- Coordinate derivative of the barrier, in radial-angular form. -/
theorem partialDeriv_angularPowerBarrier (a : ℝ) (N : ℝ^n)
    {x : ℝ^n} (hx : x ≠ 0) (i : Fin n) :
    (∂[i] (angularPowerBarrier a N)) x =
      ‖x‖ ^ (a - 1) *
        (2 * a * (x i / ‖x‖) + N i +
          (a - 1) * (inner ℝ N x / ‖x‖) * (x i / ‖x‖) -
          (inner ℝ N x / ‖x‖) * N i / 2 -
          (a - 2) * (inner ℝ N x / ‖x‖) ^ 2 * (x i / ‖x‖) / 4) := by
  have hN : HasFDerivAt (fun y ↦ inner ℝ N y) (innerSL ℝ N) x :=
    (innerSL ℝ N).hasFDerivAt
  have h := (((hasFDerivAt_norm_rpow_of_ne_zero a hx).const_mul 2).add
    (hN.mul (hasFDerivAt_norm_rpow_of_ne_zero (a - 1) hx))).sub
      (((hN.pow 2).mul (hasFDerivAt_norm_rpow_of_ne_zero (a - 2) hx)).mul_const (4⁻¹ : ℝ))
  simp only [Pi.add_def, Pi.mul_def, Pi.sub_def] at h
  change fderiv ℝ (fun y : ℝ^n ↦
    2 * ‖y‖ ^ a + inner ℝ N y * ‖y‖ ^ (a - 1) -
      inner ℝ N y ^ 2 * ‖y‖ ^ (a - 2) / 4) x (EuclideanSpace.single i 1) = _
  simp only [div_eq_mul_inv]
  rw [h.fderiv]
  simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, nsmul_eq_mul, Nat.reduceSub, pow_one, Nat.cast_ofNat,
    starRingEnd_apply, star_trivial]
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h2 : ‖x‖ ^ (a - 2) = ‖x‖ ^ (a - 1) / ‖x‖ := by
    rw [show a - 2 = (a - 1) - 1 by ring, Real.rpow_sub hr (a - 1) 1, Real.rpow_one]
  have h3 : ‖x‖ ^ (a - 1 - 2) = ‖x‖ ^ (a - 1) / ‖x‖ ^ 2 := by
    rw [Real.rpow_sub hr (a - 1) 2, Real.rpow_two]
  have h4 : ‖x‖ ^ (a - 2 - 2) = ‖x‖ ^ (a - 1) / ‖x‖ ^ 3 := by
    rw [show a - 2 - 2 = (a - 1) - 3 by ring,
      Real.rpow_sub hr (a - 1) 3, Real.rpow_ofNat]
  rw [h3, h4, h2]
  field_simp
  ring

private theorem angular_derivative_polynomial_bound
    {a s v w : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hs : |s| ≤ 1) (hv : |v| ≤ 1) (hw : |w| ≤ 1) :
    |2 * a * v + w + (a - 1) * s * v - s * w / 2 -
      (a - 2) * s ^ 2 * v / 4| ≤ 5 := by
  have haabs : |a| ≤ 1 := by rwa [abs_of_nonneg ha]
  have ha1abs : |a - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha2abs : |a - 2| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hmul {r t : ℝ} (hr : |r| ≤ 1) (ht : |t| ≤ 1) : |r * t| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hr ht (abs_nonneg t) (by norm_num)
  have hav : |a * v| ≤ 1 := hmul haabs hv
  have hsv : |(a - 1) * s * v| ≤ 1 :=
    hmul (hmul ha1abs hs) hv
  have hsw : |s * w| ≤ 1 := hmul hs hw
  have hss : |s ^ 2| ≤ 1 := by simpa only [pow_two] using hmul hs hs
  have hlast : |(a - 2) * s ^ 2 * v| ≤ 2 := by
    rw [abs_mul, abs_mul]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul ha2abs hss (abs_nonneg _) (by norm_num)) (abs_nonneg v)).trans
        (by nlinarith)
  have hfirst : |2 * a * v| ≤ 2 := by
    rw [show 2 * a * v = 2 * (a * v) by ring, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hhalf : |s * w / 2| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hquarter : |(a - 2) * s ^ 2 * v / 4| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith
  have hsum1 := abs_add_le (2 * a * v) w
  have hsum2 := abs_add_le (2 * a * v + w) ((a - 1) * s * v)
  have hsub1 := abs_sub (2 * a * v + w + (a - 1) * s * v) (s * w / 2)
  have hsub2 := abs_sub (2 * a * v + w + (a - 1) * s * v - s * w / 2)
    ((a - 2) * s ^ 2 * v / 4)
  linarith

/-- Each weak-gradient coordinate has the integrable radial size `r^(a-1)`. -/
theorem abs_partialDeriv_angularPowerBarrier_le
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    {N x : ℝ^n} (hN : ‖N‖ = 1) (hx : x ≠ 0) (i : Fin n) :
    |(∂[i] (angularPowerBarrier a N)) x| ≤ 5 * ‖x‖ ^ (a - 1) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hs : |inner ℝ N x / ‖x‖| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]
    simpa [hN] using abs_real_inner_le_norm N x
  have hv : |x i / ‖x‖| ≤ 1 := by
    rw [abs_div, abs_of_pos hr, div_le_one hr]
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hw : |N i| ≤ 1 := by
    simpa only [Real.norm_eq_abs, hN] using PiLp.norm_apply_le N i
  rw [partialDeriv_angularPowerBarrier _ _ hx, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (angular_derivative_polynomial_bound ha ha1 hs hv hw)
    (Real.rpow_nonneg (norm_nonneg x) (a - 1))

end PDE.Elliptic.BoundaryContinuity
