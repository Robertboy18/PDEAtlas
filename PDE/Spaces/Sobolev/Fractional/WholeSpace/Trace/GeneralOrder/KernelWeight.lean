/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.GeneralOrder.FrequencyLifting
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.KernelWeight
import CAS.ExactTactic

/-!
# Exact cancellation of general-order trace weights

The normalized normal kernel times the ambient order-`s` Bessel symbol equals
the boundary order-`s-1/2` symbol divided by `sqrt (J(s))`. This fixes the
normalization for the Fourier slice formula.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Fractional.Trace.GeneralOrder

open SobolevSpace.Trace.HalfSpace

/-- Arbitrary Bessel symbols are real powers of the positive tangential scale. -/
theorem besselSymbol_eq_scale_rpow {n : ℕ} (r : ℝ) (ξ : ℝ^n) :
    besselSymbol n r ξ = (((tangentialScale ξ : ℝ) ^ r : ℝ) : ℂ) := by
  change (((1 + ‖ξ‖ ^ 2) ^ (r / 2) : ℝ) : ℂ) =
    (((Real.sqrt (1 + ‖ξ‖ ^ 2)) ^ r : ℝ) : ℂ)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 2
  cas

/-- The general normal-frequency integral scales by the reciprocal boundary weight. -/
theorem integral_bessel_normalWeight {n : ℕ} (s : ℝ) (ξ : ℝ^n) :
    ∫ t : ℝ, (1 + ‖joinTangentialNormal (ξ, t)‖ ^ 2) ^ (-s) =
      (1 + ‖ξ‖ ^ 2) ^ (1 / 2 - s) * normalMass s := by
  have ha : 0 < (tangentialScale ξ : ℝ) :=
    NNReal.coe_pos.2 (pos_iff_ne_zero.2 (tangentialScale_ne_zero ξ))
  have hbase (t : ℝ) :
      1 + ‖joinTangentialNormal (ξ, t)‖ ^ 2 = (tangentialScale ξ : ℝ) ^ 2 + t ^ 2 := by
    rw [norm_join_sq, tangentialScale_sq]
    cas
  simp_rw [hbase]
  rw [integral_normalWeight s ha]
  change Real.sqrt (1 + ‖ξ‖ ^ 2) ^ (1 - 2 * s) * normalMass s = _
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 2
  cas

/-- Absolute integrability of the reciprocal ambient weight on every normal line. -/
theorem integrable_bessel_normalWeight {n : ℕ} {s : ℝ} (hs : 1 / 2 < s) (ξ : ℝ^n) :
    MeasureTheory.Integrable (fun t : ℝ ↦
      (1 + ‖joinTangentialNormal (ξ, t)‖ ^ 2) ^ (-s)) := by
  have ha : 0 < (tangentialScale ξ : ℝ) :=
    NNReal.coe_pos.2 (pos_iff_ne_zero.2 (tangentialScale_ne_zero ξ))
  convert integrable_normalWeight hs ha using 1
  funext t
  rw [norm_join_sq, tangentialScale_sq]
  congr 1
  cas

/-- Exact kernel cancellation acting on a complex Fourier value. -/
theorem frequencyKernel_smul_besselSymbol {n : ℕ} {s : ℝ} (hs : 1 / 2 < s)
    (ξ : ℝ^n) (t : ℝ) (z : ℂ) :
    traceConstant s • (frequencyKernel s ξ t •
      (besselSymbol (n + 1) s (joinTangentialNormal (ξ, t)) * z)) =
        besselSymbol n (s - 1 / 2) ξ * z := by
  rw [besselSymbol_eq_scale_rpow (s - 1 / 2)]
  have hbase : 1 + ‖joinTangentialNormal (ξ, t)‖ ^ 2 =
      (tangentialScale ξ : ℝ) ^ 2 + t ^ 2 := by
    rw [norm_join_sq, tangentialScale_sq]
    cas
  simp only [besselSymbol, hbase, Complex.real_smul]
  rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  change ((traceConstant s * normalKernel s (tangentialScale ξ) t *
    ((tangentialScale ξ : ℝ) ^ 2 + t ^ 2) ^ (s / 2) : ℝ) : ℂ) * z = _
  rw [normalKernel_mul_weight hs _ (tangentialScale_ne_zero ξ)]

end SobolevSpace.Fractional.Trace.GeneralOrder
