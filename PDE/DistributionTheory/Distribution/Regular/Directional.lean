/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Distribution
public import PDE.DistributionTheory.TestFunction.Derivative.Commutation
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Directional derivatives of regular distributions

The Fréchet derivative of a locally integrable differentiable function
represents its distributional directional derivative. The domain is any finite
dimensional real normed space with Haar measure, including a product space of
time and space. Neither the function nor its derivative needs global growth
or global integrability.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions

namespace Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

/-- Differentiation of a regular distribution in an arbitrary constant
direction agrees with its classical derivative. Local integrability
is sufficient on the whole domain. -/
theorem lineDerivCLM_ofFun_fderiv
    {f : E → F} (v : E) (hf : Differentiable ℝ f)
    (hfInt : LocallyIntegrableOn f (⊤ : Opens E) μ)
    (hdInt : LocallyIntegrableOn (fun x ↦ fderiv ℝ f x v) (⊤ : Opens E) μ) :
    lineDerivCLM v (ofFun ⊤ f μ ⊤) =
      ofFun ⊤ (fun x ↦ fderiv ℝ f x v) μ ⊤ := by
  ext φ
  rw [lineDerivCLM_apply, ofFun_apply hfInt, ofFun_apply hdInt]
  have htest :
      (TestFunction.lineDerivCLM ℝ v φ : 𝓓((⊤ : Opens E), ℝ)) =
        fun x ↦ fderiv ℝ φ x v := by
    funext x
    exact TestFunction.lineDerivCLM_apply_eq_fderiv v φ x
  have hparts := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := μ) (v := v) (f := fun x ↦ φ x) (g := f)
    (by simpa only [TestFunction.lineDerivCLM_apply_eq_fderiv] using
      (TestFunction.lineDerivCLM ℝ v φ : 𝓓((⊤ : Opens E), ℝ)).integrable_smul hfInt)
    (φ.integrable_smul hdInt) (φ.integrable_smul hfInt)
    (fun x _ ↦ (φ.contDiff.differentiable (by simp)) x) (fun x _ ↦ hf x)
  rw [htest]
  exact hparts.symm

/-- Every jointly `C¹` function has the expected ordinary distributional
directional derivative, with no global bound on either function. -/
theorem lineDerivCLM_ofFun_contDiff_one
    {f : E → F} (hf : ContDiff ℝ 1 f) (v : E) :
    lineDerivCLM v (ofFun ⊤ f μ ⊤) =
      ofFun ⊤ (fun x ↦ fderiv ℝ f x v) μ ⊤ := by
  apply lineDerivCLM_ofFun_fderiv v (hf.differentiable one_ne_zero)
  · exact (hf.continuous.locallyIntegrable (μ := μ)).locallyIntegrableOn _
  · exact (((hf.continuous_fderiv one_ne_zero).clm_apply
      (continuous_const (y := v))).locallyIntegrable (μ := μ)).locallyIntegrableOn _

end Distribution
