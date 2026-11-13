/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.DivergenceForm
public import PDE.Spaces.Sobolev.Calculus.Composition.DomainCore

/-!
# Affine normalization of homogeneous weak solutions

Subtracting a constant and multiplying by a scalar preserve the homogeneous
interior divergence equation. The representative formula is recorded for the
level-set and oscillation arguments.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Sobolev ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set ℝ^n} [IsFiniteMeasure (domainMeasure n Ω)]

/-- The affine normalization has its expected representative almost everywhere. -/
theorem wkpBaseCoordinateCLM_smul_sub_constant_ae (u : H¹(Ω)) (c k : ℝ) :
    (wkpBaseCoordinateCLM (c • (u - wkpConstant k)) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω] fun x ↦ c * (wkpBaseCoordinateCLM u x - k) := by
  rw [map_smul, map_sub]
  filter_upwards [Lp.coeFn_smul c (wkpBaseCoordinateCLM u -
    wkpBaseCoordinateCLM (wkpConstant k)),
    Lp.coeFn_sub (wkpBaseCoordinateCLM u)
      (wkpBaseCoordinateCLM (wkpConstant k)),
    wkpConstant_base_ae (n := n) (p := 2) (Ω := Ω) k]
      with x hs hd hk
  exact hs.trans (congrArg (c * ·) (hd.trans (congrArg (wkpBaseCoordinateCLM u x - ·) hk)))

/-- Affine changes of the dependent variable preserve the homogeneous
weak equation, without any regularity of the coefficient representatives. -/
theorem IsInteriorWeakDivergenceSolution.smul_sub_constant
    {a : Fin n → Fin n → DerivLp n ∞ Ω} {u : H¹(Ω)}
    (hu : IsInteriorWeakDivergenceSolution a 0 u) (c k : ℝ) :
    IsInteriorWeakDivergenceSolution a 0 (c • (u - wkpConstant k)) := by
  have hD (j : Fin n) :
      wkpCoordinateCLM (singleDerivIndex n j) (u - wkpConstant k) =
        wkpCoordinateCLM (singleDerivIndex n j) u := by
    have hc : wkpCoordinateCLM (singleDerivIndex n j)
        (wkpConstant (n := n) (p := 2) (Ω := Ω) k) = 0 :=
      Lp.ext ((wkpConstant_deriv_ae k j).trans
        (Lp.coeFn_zero ℝ 2 (domainMeasure n Ω)).symm)
    simp only [map_sub, hc, sub_zero]
  refine ⟨hu.1, fun φ ↦ ?_⟩
  change interiorVariableCoeffForm (multiplicationCoefficientOperator a)
    (c • (u - wkpConstant k)) φ = loadFunctional 0 φ
  rw [map_smul, smul_apply]
  have hform : interiorVariableCoeffForm (multiplicationCoefficientOperator a)
      (u - wkpConstant k) φ =
      interiorVariableCoeffForm (multiplicationCoefficientOperator a) u φ := by
    simp only [interiorVariableCoeffForm_apply, hD]
  rw [hform, hu.equation φ]
  simp only [loadFunctional_apply, inner_zero_left, smul_zero]

end SobolevSpace.GraphSpace
