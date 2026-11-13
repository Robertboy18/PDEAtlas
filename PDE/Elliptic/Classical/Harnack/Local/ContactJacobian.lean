/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Contact.WeightedHessian
public import PDE.Analysis.LinearAlgebra.PositiveDeterminant
public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixOperator

/-!
# Jacobians of lower contacts for elliptic supersolutions

For the zero-potential operator with residual at least `-f`, a lower contact satisfies
`α tr J ≤ tr(A J) ≤ tr A + ‖b‖ ‖y - x‖ + f/κ`. The first inequality uses positivity
of the contact Jacobian; the second uses the differential inequality and the
contact-gradient identity. The resulting determinant bound involves coefficient
bounds and the contact-to-vertex distance, but no modulus of continuity or
derivative of a coefficient.
-/

@[expose] public section

noncomputable section

namespace EllipticHarnack

open PDE.Analysis
open scoped RealInnerProductSpace Gradient

variable {n : ℕ}

/-- At an interior lower contact, ellipticity and the supersolution inequality
bound the trace of the contact Jacobian. -/
theorem trace_fderiv_quadraticContactMap_le
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n)
    {u : ℝ^n → ℝ} {x y : ℝ^n} {κ α τ B R f : ℝ}
    (hu : ContDiffAt ℝ 2 u x) (hκ : 0 < κ) (hα : 0 < α)
    (hell : ∀ v : ℝ^n, α * ‖v‖ ^ 2 ≤ ⟪v, (a x).toEuclideanLin v⟫)
    (htrace : (a x).trace ≤ τ) (hdrift : ‖b x‖ ≤ B) (hdist : ‖y - x‖ ≤ R)
    (hsuper : -f ≤ EllipticMaximum.matrixOperator a b (fun _ ↦ 0) u x)
    (hmin : IsLocalMin (quadraticTilt u κ y) x) :
    LinearMap.trace ℝ (ℝ^n) (fderiv ℝ (quadraticContactMap u κ) x).toLinearMap ≤
      (τ + B * R + κ⁻¹ * f) / α := by
  have hres :
      LinearMap.trace ℝ (ℝ^n)
        ((a x).toEuclideanLin.comp (fderiv ℝ (∇ u) x).toLinearMap) ≤
          fderiv ℝ u x (b x) + f := by
    rw [EllipticMaximum.matrixOperator_eq_neg_trace a b (fun _ ↦ 0) hu] at hsuper
    simp only [zero_mul, add_zero] at hsuper
    linarith
  have h := mul_trace_fderiv_quadraticContactMap_le (a x).toEuclideanLin (b x) hu hκ
    hell (by simpa only [trace_toEuclideanLin] using htrace) hdrift hdist hres hmin
  exact (le_div_iff₀ hα).mpr (by simpa only [mul_comm] using h)

/-- The positive contact Jacobian has uniformly bounded absolute determinant.
No injectivity hypothesis is used. -/
theorem abs_det_fderiv_quadraticContactMap_le
    (a : ℝ^n → Matrix (Fin n) (Fin n) ℝ) (b : ℝ^n → ℝ^n)
    {u : ℝ^n → ℝ} {x y : ℝ^n} {κ α τ B R f : ℝ}
    (hu : ContDiffAt ℝ 2 u x) (hκ : 0 < κ) (hα : 0 < α)
    (hell : ∀ v : ℝ^n, α * ‖v‖ ^ 2 ≤ ⟪v, (a x).toEuclideanLin v⟫)
    (htrace : (a x).trace ≤ τ) (hdrift : ‖b x‖ ≤ B) (hdist : ‖y - x‖ ≤ R)
    (hsuper : -f ≤ EllipticMaximum.matrixOperator a b (fun _ ↦ 0) u x)
    (hmin : IsLocalMin (quadraticTilt u κ y) x) :
    |(fderiv ℝ (quadraticContactMap u κ) x).det| ≤
      ((τ + B * R + κ⁻¹ * f) / α) ^ n := by
  have hpositive := isPositive_fderiv_quadraticContactMap hu hκ hmin
  have hbound := trace_fderiv_quadraticContactMap_le a b hu hκ hα hell
    htrace hdrift hdist hsuper hmin
  rw [abs_of_nonneg (det_nonneg_of_isPositive hpositive)]
  have hdet := det_le_trace_pow_of_isPositive hpositive
  rw [finrank_euclideanSpace_fin] at hdet
  exact hdet.trans (pow_le_pow_left₀ hpositive.trace_nonneg hbound n)

end EllipticHarnack
