/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.RealDistributionalDivergence
public import PDE.DistributionTheory.Distribution.Operator.Laplacian
import PDE.DistributionTheory.TestFunction.IntegrationByParts
import PDE.Analysis.MeasureTheory.Lp.IndicatorExtension

/-!
# Local first derivatives from an ordinary distributional equation

The first-order interior estimate applies to L² data given only on the open
testing domain. Zero extension is used to feed the whole-space Fourier
estimate, while every differential identity remains on the original domain.
No derivative of the zero extension across the boundary is asserted.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Distributions Laplacian Sobolev

namespace PDE.Elliptic.Interior

variable {n : ℕ} {ι : Type*} [Fintype ι] {Ω : Opens (ℝ^n)}

/-- Ordinary distributional `Δu = div f` for domain L² data gives an
H¹ representative on every relatively compact open subset. -/
theorem exists_wkpSpaceOn_one_ae_eq_of_distributional_laplacian_eq
    (u : Lp ℝ 2 (domainMeasure n Ω))
    (f : ι → Lp ℝ 2 (domainMeasure n Ω)) (v : ι → ℝ^n)
    (heq : Δ (Distribution.ofFun Ω u volume ⊤) =
      ∑ i, Distribution.lineDerivCLM (v i)
        (Distribution.ofFun Ω (f i) volume ⊤))
    {V : Set (ℝ^n)} (hV : IsOpen V) (hcompact : IsCompact (closure V))
    (hVΩ : closure V ⊆ Ω) :
    ∃ U : W^{1,2}(V),
      baseRepresentative U =ᵐ[volume.restrict V] u := by
  change LineDeriv.laplacianCLM ℝ (ℝ^n) 𝓓'(Ω, ℝ) _ = _ at heq
  let E : Lp ℝ 2 (domainMeasure n Ω) →ₗᵢ[ℝ] Lp ℝ 2 volume :=
    Lp.extendByZeroₗᵢ Ω.isOpen.measurableSet
  have hagree (a : Lp ℝ 2 (domainMeasure n Ω)) :
      (E a : ℝ^n → ℝ) =ᵐ[volume.restrict Ω] a := by
    filter_upwards [ae_restrict_of_ae
      (Lp.extendByZeroₗᵢ_apply_ae (𝕜 := ℝ) Ω.isOpen.measurableSet a),
      ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
    exact hx.trans (indicator_of_mem hxΩ _)
  have hof (a : Lp ℝ 2 (domainMeasure n Ω)) :
      Distribution.ofFun Ω (E a) volume ⊤ = Distribution.ofFun Ω a volume ⊤ :=
    Distribution.ofFun_congr_ae (hagree a)
  have hweak (φ : 𝓓(Ω, ℝ)) :
      (∫ x, E u x * laplacian (φ : ℝ^n → ℝ) x) =
        -∑ i, ∫ x, E (f i) x * fderiv ℝ (φ : ℝ^n → ℝ) x (v i) := by
    have h := congrArg (fun T : 𝓓'(Ω, ℝ) ↦ T φ) heq
    rw [← hof u, Distribution.laplacianCLM_apply_apply] at h
    have hint (a : Lp ℝ 2 (domainMeasure n Ω)) :
        LocallyIntegrableOn (E a : ℝ^n → ℝ) (Ω : Set (ℝ^n)) volume :=
      ((Lp.memLp (E a)).locallyIntegrable (by norm_num)).locallyIntegrableOn Ω
    simp only [_root_.sum_apply, Distribution.lineDerivCLM_apply] at h
    simp_rw [← hof, Distribution.ofFun_apply (hint _)] at h
    have hD (x v : ℝ^n) :
        lineDeriv ℝ (φ : ℝ^n → ℝ) x v = fderiv ℝ (φ : ℝ^n → ℝ) x v :=
      (φ.contDiff.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv
    simpa [testFunction_lineDerivCLM_apply, Finset.sum_neg_distrib, hD, mul_comm] using h
  obtain ⟨U, hU⟩ := exists_wkpSpaceOn_one_ae_eq_of_integral_laplacian_divergence_eq
    (E u) (fun i ↦ E (f i)) v hweak hV hcompact hVΩ
  exact ⟨U, hU.trans (ae_restrict_of_ae_restrict_of_subset
    (subset_closure.trans hVΩ) (hagree u))⟩

end PDE.Elliptic.Interior
