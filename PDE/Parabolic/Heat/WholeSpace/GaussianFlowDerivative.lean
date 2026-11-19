/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.GaussianFlow
public import PDE.FDeriv.Operators
public import PDE.Parabolic.Heat.Kernel.Integrability
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Spatial derivatives of the heat flow of smooth data

At a positive time the heat flow commutes with translations, so for data that are bounded with
bounded derivative the partial derivatives of the flow are the flow of the partial derivatives
(`partialDeriv_gaussianFlow`), by differentiation under the integral; for data with two bounded
derivatives the same holds for the Laplacian (`laplacian_gaussianFlow`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology

namespace HeatEquation.WholeSpace

set_option linter.missingDocs true

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The heat flow commutes with partial derivatives.** For smooth data with bounded values and
bounded derivative, `∂ᵢ (e^{tΔ} f) = e^{tΔ} (∂ᵢ f)` at positive times. -/
theorem partialDeriv_gaussianFlow {t : ℝ} (ht : 0 < t) {f : ℝ^n → E} (hf : ContDiff ℝ 1 f)
    {M M' : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (hM' : ∀ x, ‖fderiv ℝ f x‖ ≤ M') (i : Fin n)
    (x : ℝ^n) :
    PDE.partialDeriv i (gaussianFlow t f) x = gaussianFlow t (PDE.partialDeriv i f) x := by
  set e : ℝ^n := EuclideanSpace.single i (1 : ℝ)
  set Γ : ℝ^n → ℝ := fun y ↦ fundamentalSolutionHeat (x - y) t
  have hΓi : Integrable Γ := (fundamentalSolutionHeat_integrable t ht).comp_sub_left x
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfc : Continuous f := hf.continuous
  have hdfc : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  set F : ℝ → ℝ^n → E := fun h y ↦ Γ y • f (y + h • e)
  set F' : ℝ → ℝ^n → E := fun h y ↦ Γ y • fderiv ℝ f (y + h • e) e
  have hl (y : ℝ^n) (h : ℝ) : HasDerivAt (fun h : ℝ ↦ y + h • e) e h := by
    simpa using ((hasDerivAt_id h).smul_const e).const_add y
  have hmeas : ∀ h, AEStronglyMeasurable (F h) volume := fun h ↦
    hΓi.aestronglyMeasurable.smul
      (hfc.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (F' 0) volume :=
    hΓi.aestronglyMeasurable.smul
      ((hdfc.comp (continuous_id.add continuous_const)).clm_apply
        continuous_const).aestronglyMeasurable
  have hFint : Integrable (F 0) volume :=
    hΓi.smul_of_top_left (memLp_top_of_bound
      (hfc.comp (continuous_id.add continuous_const)).aestronglyMeasurable M
      (Eventually.of_forall fun y ↦ hM _))
  have hbound : ∀ᵐ y ∂volume, ∀ h ∈ (univ : Set ℝ), ‖F' h y‖ ≤ ‖Γ y‖ * (M' * ‖e‖) :=
    Eventually.of_forall fun y h _ ↦ by
      simp only [F', norm_smul]
      gcongr
      exact ((fderiv ℝ f (y + h • e)).le_opNorm e).trans (by gcongr; exact hM' _)
  have hdiff : ∀ᵐ y ∂volume, ∀ h ∈ (univ : Set ℝ), HasDerivAt (F · y) (F' h y) h :=
    Eventually.of_forall fun y h _ ↦
      ((hfd (y + h • e)).hasFDerivAt.comp_hasDerivAt h (hl y h)).const_smul (Γ y)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := (0 : ℝ))
    (F := F) (F' := F') univ_mem (Eventually.of_forall hmeas) hFint hmeas' hbound
    (hΓi.norm.mul_const _) hdiff
  have htrans : (fun h : ℝ ↦ ∫ y, F h y) = fun h ↦ gaussianFlow t f (x + h • e) := by
    funext h
    rw [gaussianFlow_apply ht]
    rw [← integral_add_right_eq_self (μ := volume)
      (fun y ↦ fundamentalSolutionHeat (x + h • e - y) t • f y) (h • e)]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp only [F, Γ]
    congr 2
    abel
  rw [htrans] at hmain
  have hG : DifferentiableAt ℝ (gaussianFlow t f) x :=
    ((contDiff_gaussianFlow ht (p := ⊤) le_top (memLp_top_of_bound hfc.aestronglyMeasurable M
      (Eventually.of_forall hM))).differentiable (by simp)) x
  unfold PDE.partialDeriv
  rw [← hmain.2.unique (hG.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) (hl x 0) (by simp)),
    gaussianFlow_apply ht]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  simp [F', Γ, e]

/-- The heat flow is additive on bounded continuous data at positive times. -/
theorem gaussianFlow_finsetSum {t : ℝ} (ht : 0 < t) {ι : Type*} (s : Finset ι)
    {f : ι → ℝ^n → E} (hf : ∀ i, Continuous (f i)) (hM : ∀ i, ∃ M, ∀ x, ‖f i x‖ ≤ M)
    (x : ℝ^n) :
    gaussianFlow t (fun y ↦ ∑ i ∈ s, f i y) x = ∑ i ∈ s, gaussianFlow t (f i) x := by
  have hΓi : Integrable (fun y ↦ fundamentalSolutionHeat (x - y) t) :=
    (fundamentalSolutionHeat_integrable t ht).comp_sub_left x
  simp only [gaussianFlow_apply ht, Finset.smul_sum]
  refine integral_finsetSum s fun i _ ↦ ?_
  obtain ⟨M, hM⟩ := hM i
  exact hΓi.smul_of_top_left (memLp_top_of_bound (hf i).aestronglyMeasurable M
    (Eventually.of_forall fun y ↦ hM y))

/-- The partial derivatives of a smooth function with bounded derivatives have bounded
derivatives. -/
theorem norm_iteratedFDeriv_partialDeriv_le {f : ℝ^n → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin n) (m : ℕ) (x : ℝ^n) :
    ‖iteratedFDeriv ℝ m (PDE.partialDeriv i f) x‖ ≤ ‖iteratedFDeriv ℝ (m + 1) f x‖ := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  have heq : PDE.partialDeriv i f =
      ⇑(ContinuousLinearMap.apply ℝ E (EuclideanSpace.single i (1 : ℝ))) ∘ fderiv ℝ f := rfl
  rw [heq, (ContinuousLinearMap.apply ℝ E _).iteratedFDeriv_comp_left hd.contDiffAt
    (i := m) (by exact_mod_cast le_top), ← norm_iteratedFDeriv_fderiv]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L ↦ ?_
  rw [ContinuousLinearMap.apply_apply, one_mul]
  exact (L.le_opNorm _).trans (by simp)

/-- **The heat flow commutes with partial derivatives**, for smooth data with all derivatives
bounded, as functions. -/
theorem partialDeriv_gaussianFlow_eq {t : ℝ} (ht : 0 < t) {f : ℝ^n → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hb : ∀ m : ℕ, ∃ M, ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ M)
    (i : Fin n) :
    (fun y ↦ PDE.partialDeriv i (gaussianFlow t f) y) = gaussianFlow t (PDE.partialDeriv i f) := by
  obtain ⟨M₀, h₀⟩ := hb 0
  obtain ⟨M₁, h₁⟩ := hb 1
  funext y
  exact partialDeriv_gaussianFlow ht (hf.of_le (by exact_mod_cast le_top))
    (fun x ↦ by simpa [norm_iteratedFDeriv_zero] using h₀ x)
    (fun x ↦ by simpa [norm_iteratedFDeriv_one] using h₁ x) i y

/-- **The heat flow commutes with the Laplacian**, for smooth data with all derivatives
bounded: `Δ (e^{tΔ} f) = e^{tΔ} (Δ f)` at positive times. -/
theorem laplacian_gaussianFlow {t : ℝ} (ht : 0 < t) {f : ℝ^n → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hb : ∀ m : ℕ, ∃ M, ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ M) (x : ℝ^n) :
    PDE.laplacian (gaussianFlow t f) x = gaussianFlow t (PDE.laplacian f) x := by
  have hdi (i : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (PDE.partialDeriv i f) :=
    PDE.contDiff_top_partialDeriv hf
  have hbi (i : Fin n) : ∀ m : ℕ, ∃ M, ∀ x, ‖iteratedFDeriv ℝ m (PDE.partialDeriv i f) x‖ ≤ M :=
    fun m ↦ by
      obtain ⟨M, hM⟩ := hb (m + 1)
      exact ⟨M, fun x ↦ (norm_iteratedFDeriv_partialDeriv_le hf i m x).trans (hM x)⟩
  unfold PDE.laplacian
  simp_rw [partialDeriv_gaussianFlow_eq ht hf hb]
  rw [gaussianFlow_finsetSum ht Finset.univ (fun i ↦
    (PDE.contDiff_top_partialDeriv (hdi i)).continuous) (fun i ↦ by
      obtain ⟨M, hM⟩ := hbi i 1
      exact ⟨M, fun y ↦ by
        refine ((fderiv ℝ (PDE.partialDeriv i f) y).le_opNorm _).trans ?_
        simpa [norm_iteratedFDeriv_one] using hM y⟩) x]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h := congrFun (partialDeriv_gaussianFlow_eq ht (hdi i) (hbi i) i) x
  exact h

end HeatEquation.WholeSpace
