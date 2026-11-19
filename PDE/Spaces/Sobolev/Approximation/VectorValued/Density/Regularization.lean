/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.Mollification.Operator
public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.Extension

/-!
# Bounded linear regularization on Sobolev extension domains

Extend to the whole space, convolve, and restrict back to the domain. The resulting
operators have a common bound given by the norm of the extension. At finite exponents
they converge strongly to the identity, and every output is the restriction of one
globally smooth function together with all its classical derivative coordinates.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued

open Approximation GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {Ω : Opens ℝ^n} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Extend, mollify at a positive scale, and restrict back to the original domain. -/
def regularizationCLM (E : W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(ℝ^n; F))
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (hp : p ≠ ∞) :
    W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(Ω; F) :=
  (restrictCLM (le_top : Ω ≤ ⊤)).comp ((mollifyCLM μ hε hp).comp E)

/-- Regularization has the extension's norm bound, uniformly in the positive scale. -/
theorem norm_regularizationCLM_le (E : W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(ℝ^n; F))
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (hp : p ≠ ∞) :
    ‖regularizationCLM E μ hε hp‖ ≤ ‖E‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg E)
  intro U
  exact (norm_restrictCLM_apply_le (le_top : Ω ≤ ⊤) _).trans
    ((norm_mollify_le μ hε hp (E U)).trans (E.le_opNorm U))

/-- Every regularized coordinate is the convolution of that coordinate of the extension. -/
theorem regularizationCLM_apply_ae (E : W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(ℝ^n; F))
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (hp : p ≠ ∞)
    (U : W^{k,p}(Ω; F)) (a : DerivIndex n k) :
    ((regularizationCLM E μ hε hp U).val a : ℝ^n → F) =ᵐ[domainMeasure n Ω]
      mollifyVector μ ε ((E U).val a) := by
  exact (restrictCLM_apply_ae (le_top : Ω ≤ ⊤) (mollifyCLM μ hε hp (E U)) a).trans
    (ae_mono Measure.restrict_le_self (mollify_apply_ae μ hε hp (E U) a))

/-- Every regularized jet is represented on the domain by one globally smooth function. -/
theorem regularizationCLM_has_smooth_representative
    (E : W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(ℝ^n; F))
    (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (hp : p ≠ ∞) (U : W^{k,p}(Ω; F)) :
    ∃ f : ℝ^n → F, ContDiff ℝ (⊤ : ℕ∞) f ∧
      ∀ a : DerivIndex n k,
        ((regularizationCLM E μ hε hp U).val a : ℝ^n → F) =ᵐ[domainMeasure n Ω]
          iteratedPartialDeriv a.toList f := by
  obtain ⟨f, hf, hrow⟩ := mollifyCLM_has_smooth_representative μ hε hp (E U)
  refine ⟨f, hf, fun a ↦ ?_⟩
  exact (restrictCLM_apply_ae (le_top : Ω ≤ ⊤) (mollifyCLM μ hε hp (E U)) a).trans
    (ae_mono Measure.restrict_le_self (hrow a))

/-- A right inverse to restriction produces strong regularization at every finite exponent.
The conclusion is pointwise convergence in the Sobolev norm for each input. -/
theorem tendsto_regularizationCLM
    (E : W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(ℝ^n; F))
    (hE : ∀ U, restrictCLM (le_top : Ω ≤ ⊤) (E U) = U)
    (μ : Mollifier n) (hp : p ≠ ∞) (U : W^{k,p}(Ω; F))
    (ε : ℕ → ℝ) (hε : ∀ m, 0 < ε m) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun m ↦ regularizationCLM E μ (hε m) hp U) atTop (𝓝 U) := by
  simpa only [regularizationCLM, ContinuousLinearMap.comp_apply, mollifyCLM_apply,
    Function.comp_def, hE] using
    ((restrictCLM (le_top : Ω ≤ ⊤)).continuous.tendsto (E U)).comp
      (mollify_tendsto μ hp (E U) ε hε hε0)

/-- Bounded open graph domains admit a uniformly bounded linear regularization family.
The operators converge strongly for each input, and their full jets have ambient smooth
representatives. The extension is supplied by the geometric boundary hypothesis. -/
theorem exists_regularization_of_hasContDiffGraphBoundary
    (μ : Mollifier n) (hp : p ≠ ∞)
    (hbounded : Bornology.IsBounded (Ω : Set ℝ^n))
    (hgraph : Boundary.HasContDiffGraphBoundary k (Ω : Set ℝ^n)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∃ R : {ε : ℝ // 0 < ε} → (W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(Ω; F)),
        (∀ ε, ‖R ε‖ ≤ C) ∧
        (∀ ε U, ∃ f : ℝ^n → F, ContDiff ℝ (⊤ : ℕ∞) f ∧
          ∀ a : DerivIndex n k, ((R ε U).val a : ℝ^n → F) =ᵐ[domainMeasure n Ω]
            iteratedPartialDeriv a.toList f) ∧
        (∀ (U : W^{k,p}(Ω; F)) (ε : ℕ → {ε : ℝ // 0 < ε}),
          Tendsto (fun m ↦ (ε m).val) atTop (𝓝 0) →
            Tendsto (fun m ↦ R (ε m) U) atTop (𝓝 U)) := by
  obtain ⟨E, _, _, _, hE⟩ :=
    GeometricExtension.exists_extension_with_Lp_base (p := p) (F := F) hbounded hgraph
  refine ⟨‖E‖, norm_nonneg E, fun ε ↦ regularizationCLM E μ ε.property hp,
    fun ε ↦ norm_regularizationCLM_le E μ ε.property hp, ?_, ?_⟩
  · exact fun ε U ↦ regularizationCLM_has_smooth_representative E μ ε.property hp U
  · intro U ε hε
    exact tendsto_regularizationCLM E hE μ hp U (fun m ↦ (ε m).val)
      (fun m ↦ (ε m).property) hε

end SobolevSpace.VectorValued
