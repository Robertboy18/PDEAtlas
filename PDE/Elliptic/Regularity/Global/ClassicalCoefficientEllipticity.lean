/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Global.ClassicalHigherBoundaryData

/-!
# Ellipticity of classical coefficient representatives

Pointwise ellipticity passes to the canonical bounded multiplier coefficients
used in the weak variational equation and global regularity estimates.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.BoundaryRegularity

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {Ω : Set ℝ^n}

/-- Pointwise ellipticity of classical coefficient data gives integrated
ellipticity of their canonical bounded-multiplier representatives. -/
theorem integratedElliptic_toLp_of_contDiffUpToBoundary
    {k : ℕ} (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (a : ℝ^n → Fin n → Fin n → ℝ)
    (ha : ∀ i j, ContDiffUpToBoundary k (fun x ↦ a x i j) Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hElliptic : ∀ x ∈ Ω, MatrixEllipticLowerBound (a x) alpha) :
    IntegratedElliptic
      (multiplicationCoefficientOperator (fun i j ↦ (ha i j).toLp hΩ hbounded ∞))
      alpha := by
  apply integratedElliptic_multiplication_of_ae
  refine ⟨halpha, ?_⟩
  have hrep : ∀ᵐ x ∂domainMeasure n Ω, ∀ i j,
      (ha i j).toLp hΩ hbounded ∞ x = a x i j := by
    simp only [ae_all_iff]
    exact fun i j ↦ (ha i j).toLp_coeFn hΩ hbounded ∞
  filter_upwards [hrep, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
  intro ξ
  simpa only [hx, MatrixEllipticLowerBound, principalEnergy, dotProduct,
    mul_right_comm] using hElliptic x hxΩ ξ

end SobolevSpace.GraphSpace.BoundaryRegularity
