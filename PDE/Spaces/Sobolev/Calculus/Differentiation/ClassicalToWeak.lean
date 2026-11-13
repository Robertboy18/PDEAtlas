/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import PDE.FDeriv.Calculus

/-!
# Classical derivatives as weak derivatives on open domains

Local `C¹` regularity identifies each classical coordinate derivative with a weak
derivative. Compact support of test functions localizes integration by parts, so no
global regularity or global integrability is needed.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open TopologicalSpace
open scoped Distributions

namespace SobolevSpace

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

private theorem integrable_mul_of_continuousOn_of_tsupport_subset
    {f ψ : ℝ^n → ℝ} (hf : ContinuousOn f Ω) (hψ : Continuous ψ)
    (hcompact : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ Ω) :
    Integrable (fun x ↦ f x * ψ x) volume := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right (f := f) (g := ψ)).trans
      (subset_tsupport ψ))).mp
  exact ContinuousOn.integrableOn_compact hcompact ((hf.mono hsupp).mul hψ.continuousOn)

/-- For `tsupport ψ ⊆ Ω`, integrating `f ψ` against Lebesgue measure on `Ω` or on the whole
space gives the same value. -/
theorem integral_mul_eq_global_of_tsupport_subset
    (f ψ : ℝ^n → ℝ) (hsupp : tsupport ψ ⊆ Ω) :
    (∫ x, f x * ψ x ∂domainMeasure n Ω) = ∫ x, f x * ψ x ∂volume := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hzero : ψ x = 0 := by
    by_contra hne
    exact hx (hsupp (subset_tsupport ψ hne))
  rw [hzero, mul_zero]

/-- Local `C¹` regularity on an open domain suffices to identify each classical
partial derivative as a weak derivative. Compact support of the test function localizes
integration by parts, so no global regularity or integrability is required. -/
theorem hasWeakDerivativeOn_of_contDiffAt_one (hΩ : IsOpen Ω)
    {f : ℝ^n → ℝ} (hf : ∀ x ∈ Ω, ContDiffAt ℝ 1 f x) (i : Fin n) :
    HasWeakDerivativeOn (n := n) Ω [i] f (∂[i] f) := by
  have hcont : ContinuousOn f Ω :=
    fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have hdcont : ContinuousOn (∂[i] f) Ω :=
    fun x hx ↦ (PDE.contDiffAt_partialDeriv 0 (hf x hx) i).continuousAt.continuousWithinAt
  refine ⟨hcont.locallyIntegrableOn hΩ.measurableSet,
    hdcont.locallyIntegrableOn hΩ.measurableSet, ?_⟩
  intro φ hφ
  have hdφ : Continuous (∂[i] φ.toFun) :=
    (PDE.contDiff_top_partialDeriv φ.contDiff).continuous
  have hdφcompact : HasCompactSupport (∂[i] φ.toFun) :=
    φ.hasCompactSupport.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))
  have hdφsupp : tsupport (∂[i] φ.toFun) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ (f := φ.toFun)
      (EuclideanSpace.single i (1 : ℝ))).trans hφ
  have hparts := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (ℝ^n))) (f := f) (g := φ.toFun)
    (v := EuclideanSpace.single i (1 : ℝ))
    (integrable_mul_of_continuousOn_of_tsupport_subset hdcont φ.contDiff.continuous
      φ.hasCompactSupport hφ)
    (integrable_mul_of_continuousOn_of_tsupport_subset hcont hdφ hdφcompact hdφsupp)
    (integrable_mul_of_continuousOn_of_tsupport_subset hcont φ.contDiff.continuous
      φ.hasCompactSupport hφ)
    (fun x hx ↦ (hf x (hφ hx)).differentiableAt (by norm_num))
    (fun x _ ↦ (φ.contDiff.differentiable (by simp)).differentiableAt)
  simpa only [iteratedPartialDeriv, List.length_cons, List.length_nil,
    Nat.zero_add, pow_one, neg_one_mul] using
    (integral_mul_eq_global_of_tsupport_subset f (∂[i] φ.toFun) hdφsupp).trans
      (hparts.trans (congrArg (fun r : ℝ ↦ -r)
        (integral_mul_eq_global_of_tsupport_subset (∂[i] f) φ.toFun hφ).symm))

end SobolevSpace
