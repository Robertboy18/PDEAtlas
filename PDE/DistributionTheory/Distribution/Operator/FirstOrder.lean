/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.DistributionTheory.Distribution.Operator.Polynomial
public import PDE.DistributionTheory.Distribution.Regular.Directional
public import PDE.Analysis.Operator.ConstantCoefficient.FirstOrder

/-!
# Determinant equations for classical constant-coefficient systems

A classical first-order equation for jointly `C¹` functions gives the
distributional system by integration by parts. The adjugate identity
then gives a scalar determinant equation for each component. No growth
condition is imposed.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions

namespace Distribution

variable {E F ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [Fintype ι] [Fintype κ] [DecidableEq κ]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

/-- Every component of a classical `C¹` constant-coefficient first-order system
satisfies its scalar determinant equation as an ordinary distribution. -/
theorem firstOrder_determinant_of_contDiff_one
    (v : ι → E) (A : ι → Matrix κ κ ℝ) (u : κ → E → F)
    (hu : ∀ j, ContDiff ℝ 1 (u j))
    (heq : ∀ x i, ∑ j, ∑ k, A k i j • fderiv ℝ (u j) x (v k) = 0) :
    ∀ i, polynomialLineDeriv v (PDE.Analysis.firstOrderPolynomialMatrix A).det
      (ofFun ⊤ (u i) μ ⊤) = 0 := by
  apply PDE.Analysis.firstOrderPolynomialMatrix_determinant_annihilates
    (fun k ↦ (lineDerivCLM (v k)).toLinearMap)
    (fun k l ↦ lineDerivEnd_commute (v k) (v l))
  intro i
  have hder (j : κ) (k : ι) :
      LocallyIntegrableOn (fun x ↦ fderiv ℝ (u j) x (v k)) (⊤ : Opens E) μ :=
    ((((hu j).continuous_fderiv one_ne_zero).clm_apply
      (continuous_const (y := v k))).locallyIntegrable (μ := μ)).locallyIntegrableOn _
  simp only [ContinuousLinearMap.coe_coe, lineDerivCLM_ofFun_contDiff_one (hu _)]
  ext φ
  simp only [sum_apply, smul_apply, zero_apply]
  simp only [ofFun_apply (hder _ _), ← integral_smul]
  have hint (j : κ) (k : ι) :
      Integrable (fun x ↦ A k i j • (φ x • fderiv ℝ (u j) x (v k))) μ :=
    (φ.integrable_smul (hder j k)).smul _
  have hsum (j : κ) :
      (∑ k, ∫ x, A k i j • (φ x • fderiv ℝ (u j) x (v k)) ∂μ) =
        ∫ x, ∑ k, A k i j • (φ x • fderiv ℝ (u j) x (v k)) ∂μ :=
    (integral_finsetSum _ (fun k _ ↦ hint j k)).symm
  simp_rw [hsum]
  rw [← integral_finsetSum _ (fun j _ ↦ integrable_finsetSum _ (fun k _ ↦ hint j k))]
  have hzero (x : E) :
      (∑ j, ∑ k, A k i j • (φ x • fderiv ℝ (u j) x (v k))) = 0 := by
    simp_rw [smul_comm (A _ _ _) (φ x), ← Finset.smul_sum]
    rw [heq x i, smul_zero]
  simp only [hzero, integral_zero]

end Distribution
