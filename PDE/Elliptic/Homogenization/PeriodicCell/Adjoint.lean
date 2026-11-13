/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Homogenization.PeriodicCell.RescaledCorrector
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Adjoint periodic cell problems

Taking the pointwise adjoint preserves boundedness and the original ellipticity
constant. The cell solver of `PeriodicCell.CellProblem` therefore constructs its correctors
as well.
Testing the primal and adjoint cell equations against each other's corrections
shows that homogenization commutes with taking the adjoint. This supplies the
adjoint correctors needed for nonsymmetric oscillating-test arguments.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter SobolevSpace
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology InnerProductSpace Sobolev

namespace PDE.Elliptic.Homogenization.PeriodicCell

variable {n : ℕ} (A : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n))

/-- The pointwise Hilbert adjoint of the periodic coefficient field. -/
def adjointCoefficient : Lp ((ℝ^n) →L[ℝ] (ℝ^n)) ∞ (cellMeasure n) :=
  let L := (ContinuousLinearMap.adjoint :
    ((ℝ^n) →L[ℝ] (ℝ^n)) ≃ₗᵢ[ℝ] ((ℝ^n) →L[ℝ] (ℝ^n))).toContinuousLinearEquiv
  L.toContinuousLinearMap.compLp A

/-- The adjoint coefficient has the expected almost-everywhere representative. -/
theorem adjointCoefficient_ae :
    adjointCoefficient A =ᵐ[cellMeasure n] fun x ↦ (A x).adjoint :=
  ContinuousLinearMap.coeFn_compLp _ A

/-- The coefficient form of the pointwise adjoint reverses its arguments. -/
theorem coefficientForm_adjoint (v w : Lp (ℝ^n) 2 (cellMeasure n)) :
    coefficientForm (adjointCoefficient A) v w = coefficientForm A w v := by
  rw [coefficientForm_eq_integral, coefficientForm_eq_integral]
  apply integral_congr_ae
  filter_upwards [adjointCoefficient_ae A] with x hx
  rw [hx, ContinuousLinearMap.adjoint_inner_left, real_inner_comm]

variable {α : ℝ} (hα : 0 < α)
    (hA : ∀ᵐ x ∂cellMeasure n, ∀ ξ : ℝ^n, α * ‖ξ‖ ^ 2 ≤ ⟪A x ξ, ξ⟫_ℝ)

include hA in
/-- The adjoint coefficient preserves the same pointwise ellipticity lower bound. -/
theorem adjointCoefficient_elliptic :
    ∀ᵐ x ∂cellMeasure n, ∀ ξ : ℝ^n,
      α * ‖ξ‖ ^ 2 ≤ ⟪adjointCoefficient A x ξ, ξ⟫_ℝ := by
  filter_upwards [hA, adjointCoefficient_ae A] with x hx hAdj
  intro ξ
  rw [hAdj, ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  exact hx ξ

/-- Primal and adjoint cell equations identify the transposed effective pairing. -/
theorem effectiveForm_adjoint (ξ η : ℝ^n) :
    effectiveForm (adjointCoefficient A) hα (adjointCoefficient_elliptic A hA) ξ η =
      effectiveForm A hα hA η ξ := by
  let A' := adjointCoefficient A
  let hA' := adjointCoefficient_elliptic A hA
  have hzero (g : gradientSpace n) :
      coefficientForm A (correctedField A hα hA η)
        (g : Lp (ℝ^n) 2 (cellMeasure n)) = 0 := by
    rw [coefficientForm_eq_integral]
    exact correctorGradient_equation A hα hA η g
  have hzero' (g : gradientSpace n) :
      coefficientForm A' (correctedField A' hα hA' ξ)
        (g : Lp (ℝ^n) 2 (cellMeasure n)) = 0 := by
    rw [coefficientForm_eq_integral]
    exact correctorGradient_equation A' hα hA' ξ g
  change coefficientForm A' (correctedField A' hα hA' ξ) (constantField n η) =
    coefficientForm A (correctedField A hα hA η) (constantField n ξ)
  calc
    _ = coefficientForm A' (correctedField A' hα hA' ξ)
        (correctedField A hα hA η) := by
      change _ = coefficientForm A' (correctedField A' hα hA' ξ)
        (constantField n η + (correctorGradient A hα hA η :
          Lp (ℝ^n) 2 (cellMeasure n)))
      rw [map_add, hzero', add_zero]
    _ = coefficientForm A (correctedField A hα hA η)
        (correctedField A' hα hA' ξ) := coefficientForm_adjoint A _ _
    _ = _ := by
      change coefficientForm A (correctedField A hα hA η)
        (constantField n ξ + (correctorGradient A' hα hA' ξ :
          Lp (ℝ^n) 2 (cellMeasure n))) = _
      rw [map_add, hzero, add_zero]

/-- The effective operator of the adjoint medium is the adjoint effective operator. -/
theorem effectiveOperator_adjoint :
    effectiveOperator (adjointCoefficient A) hα (adjointCoefficient_elliptic A hA) =
      (effectiveOperator A hα hA).adjoint := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_right ℝ
  intro η
  rw [effectiveOperator_inner, effectiveForm_adjoint,
    ContinuousLinearMap.adjoint_inner_left, real_inner_comm, effectiveOperator_inner]

/-- The effective matrix of the adjoint medium is the transpose of the effective matrix. -/
theorem effectiveMatrix_adjoint :
    effectiveMatrix (adjointCoefficient A) hα (adjointCoefficient_elliptic A hA) =
      (effectiveMatrix A hα hA).transpose := by
  ext i j
  simp only [Matrix.transpose_apply, effectiveMatrix_entry]
  exact effectiveForm_adjoint A hα hA _ _

end PDE.Elliptic.Homogenization.PeriodicCell
