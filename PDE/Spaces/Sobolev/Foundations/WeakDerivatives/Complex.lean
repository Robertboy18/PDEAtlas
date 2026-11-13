/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.WeakDerivatives.Definitions
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Complex weak derivatives

A complex weak derivative is a weak derivative in both real coordinates. The complex
integration-by-parts identity below shows that this is a distributional condition on the
function itself. Real smooth tests suffice: complex tests split into two such tests.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)
open MeasureTheory TopologicalSpace
open scoped Distributions

namespace SobolevSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {α : List (Fin n)} {f g : ℝ^n → ℂ}

/-- The complex weak derivative, expressed in the real basis `1, I` of `ℂ`. -/
def HasComplexWeakDerivativeOn (Ω : Set (ℝ^n)) (α : List (Fin n))
    (f g : ℝ^n → ℂ) : Prop :=
  HasWeakDerivativeOn Ω α (fun x ↦ (f x).re) (fun x ↦ (g x).re) ∧
    HasWeakDerivativeOn Ω α (fun x ↦ (f x).im) (fun x ↦ (g x).im)

/-- The representative-level condition is unchanged by almost-everywhere equality. -/
theorem HasComplexWeakDerivativeOn.congr_ae
    (h : HasComplexWeakDerivativeOn Ω α f g) {f' g' : ℝ^n → ℂ}
    (hf : f =ᵐ[domainMeasure n Ω] f') (hg : g =ᵐ[domainMeasure n Ω] g') :
    HasComplexWeakDerivativeOn Ω α f' g' :=
  ⟨h.1.congr_ae (hf.fun_comp Complex.re) (hg.fun_comp Complex.re),
    h.2.congr_ae (hf.fun_comp Complex.im) (hg.fun_comp Complex.im)⟩

/-- Complex integration by parts for a real smooth compactly supported test. -/
theorem HasComplexWeakDerivativeOn.integral_identity
    (h : HasComplexWeakDerivativeOn Ω α f g)
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hφ : tsupport φ.toFun ⊆ Ω) :
    ∫ x, f x * ((iteratedPartialDeriv α φ.toFun x : ℝ) : ℂ) ∂domainMeasure n Ω =
      (-1 : ℂ) ^ α.length * ∫ x, g x * (φ x : ℂ) ∂domainMeasure n Ω := by
  have expand (v : ℝ^n → ℂ) (ψ : ℝ^n → ℝ) :
      (fun x ↦ v x * (ψ x : ℂ)) =
        fun x ↦ ((v x).re * ψ x : ℝ) + ((v x).im * ψ x : ℝ) * Complex.I := by
    funext x
    apply Complex.ext <;> simp
  have hfr : Integrable (fun x ↦ (((f x).re * iteratedPartialDeriv α φ.toFun x : ℝ) : ℂ))
      (domainMeasure n Ω) := (h.1.integrable_mul_iteratedPartialDeriv φ hφ).ofReal
  have hfi : Integrable (fun x ↦ (((f x).im * iteratedPartialDeriv α φ.toFun x : ℝ) : ℂ))
      (domainMeasure n Ω) := (h.2.integrable_mul_iteratedPartialDeriv φ hφ).ofReal
  have hgr : Integrable (fun x ↦ (((g x).re * φ x : ℝ) : ℂ))
      (domainMeasure n Ω) := (h.1.integrable_mul_testFunction φ hφ).ofReal
  have hgi : Integrable (fun x ↦ (((g x).im * φ x : ℝ) : ℂ))
      (domainMeasure n Ω) := (h.2.integrable_mul_testFunction φ hφ).ofReal
  rw [expand f, expand g, integral_add hfr (hfi.mul_const Complex.I),
    integral_add hgr (hgi.mul_const Complex.I)]
  simp only [integral_mul_const, integral_complex_ofReal]
  rw [h.1.integral_identity φ hφ, h.2.integral_identity φ hφ]
  simp only [TestFunction.toFun_eq_coe]
  push_cast
  ring

/-- Permuting the coordinate directions leaves the complex weak derivative unchanged. -/
theorem HasComplexWeakDerivativeOn.perm (h : HasComplexWeakDerivativeOn Ω α f g)
    {β : List (Fin n)} (hαβ : α.Perm β) : HasComplexWeakDerivativeOn Ω β f g :=
  ⟨h.1.perm hαβ, h.2.perm hαβ⟩

/-- For square-integrable functions, the coordinate definition is exactly complex
integration by parts. Local integrability and both test-pairing integrability statements
follow from `L²` and compact support. -/
theorem hasComplexWeakDerivativeOn_iff_integral_identity
    (hf : MemLp f 2 (domainMeasure n Ω)) (hg : MemLp g 2 (domainMeasure n Ω)) :
    HasComplexWeakDerivativeOn Ω α f g ↔
      ∀ φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ), tsupport φ.toFun ⊆ Ω →
        ∫ x, f x * ((iteratedPartialDeriv α φ.toFun x : ℝ) : ℂ) ∂domainMeasure n Ω =
          (-1 : ℂ) ^ α.length * ∫ x, g x * (φ x : ℂ) ∂domainMeasure n Ω := by
  refine ⟨fun h ↦ h.integral_identity, fun h ↦ ?_⟩
  have hp (φ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (hφ : tsupport φ.toFun ⊆ Ω) :
      (∫ x, (f x).re * iteratedPartialDeriv α φ.toFun x ∂domainMeasure n Ω =
        (-1 : ℝ) ^ α.length * ∫ x, (g x).re * φ.toFun x ∂domainMeasure n Ω) ∧
      (∫ x, (f x).im * iteratedPartialDeriv α φ.toFun x ∂domainMeasure n Ω =
        (-1 : ℝ) ^ α.length * ∫ x, (g x).im * φ.toFun x ∂domainMeasure n Ω) := by
    have hd : MemLp (iteratedPartialDeriv α φ.toFun) 2 (domainMeasure n Ω) :=
      (PDE.contDiff_top_iteratedPartialDeriv φ.contDiff α).continuous.memLp_of_hasCompactSupport
        (iteratedPartialDeriv_hasCompactSupport φ α)
    have ht : MemLp φ.toFun 2 (domainMeasure n Ω) :=
      φ.contDiff.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
    have hleft : Integrable
        (fun x ↦ f x * ((iteratedPartialDeriv α φ.toFun x : ℝ) : ℂ))
        (domainMeasure n Ω) := hf.integrable_mul hd.ofReal
    have hright : Integrable (fun x ↦ g x * (φ x : ℂ)) (domainMeasure n Ω) :=
      hg.integrable_mul ht.ofReal
    have heq := h φ hφ
    rw [show (-1 : ℂ) ^ α.length = (((-1 : ℝ) ^ α.length : ℝ) : ℂ) by norm_cast] at heq
    have hr := congrArg Complex.reCLM heq
    have hi := congrArg Complex.imCLM heq
    rw [← Complex.real_smul, map_smul, ← Complex.reCLM.integral_comp_comm hleft,
      ← Complex.reCLM.integral_comp_comm hright] at hr
    rw [← Complex.real_smul, map_smul, ← Complex.imCLM.integral_comp_comm hleft,
      ← Complex.imCLM.integral_comp_comm hright] at hi
    exact ⟨by simpa [Complex.mul_re, TestFunction.toFun_eq_coe] using hr,
      by simpa [Complex.mul_im, TestFunction.toFun_eq_coe] using hi⟩
  exact ⟨⟨memLp_locallyIntegrableOn_domain hf.re (by norm_num),
      memLp_locallyIntegrableOn_domain hg.re (by norm_num), fun φ hφ ↦ (hp φ hφ).1⟩,
    ⟨memLp_locallyIntegrableOn_domain hf.im (by norm_num),
      memLp_locallyIntegrableOn_domain hg.im (by norm_num), fun φ hφ ↦ (hp φ hφ).2⟩⟩

private theorem iteratedPartialDeriv_postcomp (L : ℂ →L[ℝ] ℝ) {φ : ℝ^n → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (α : List (Fin n)) :
    iteratedPartialDeriv α (L ∘ φ) = fun x ↦ L (iteratedPartialDeriv α φ x) := by
  induction α with
  | nil => rfl
  | cons i rest ih =>
    simp only [iteratedPartialDeriv, ih]
    funext x
    have hd := ((PDE.contDiff_top_iteratedPartialDeriv hφ rest).differentiable (by simp) x)
    exact congrArg (fun A : ℝ^n →L[ℝ] ℝ ↦ A (EuclideanSpace.single i 1))
      (L.hasFDerivAt.comp x hd.hasFDerivAt).fderiv

/-- Complex weak derivatives satisfy integration by parts against every complex smooth test. -/
theorem HasComplexWeakDerivativeOn.integral_identity_complex
    (h : HasComplexWeakDerivativeOn Ω α f g)
    (hf : MemLp f 2 (domainMeasure n Ω)) (hg : MemLp g 2 (domainMeasure n Ω))
    (φ : 𝓓((⊤ : Opens (ℝ^n)), ℂ)) (hφ : tsupport φ.toFun ⊆ Ω) :
    ∫ x, f x * iteratedPartialDeriv α φ.toFun x ∂domainMeasure n Ω =
      (-1 : ℂ) ^ α.length * ∫ x, g x * φ x ∂domainMeasure n Ω := by
  let φr := TestFunction.postcompCLM Complex.reCLM φ
  let φi := TestFunction.postcompCLM Complex.imCLM φ
  have hr := h.integral_identity φr
    ((tsupport_comp_subset Complex.reCLM.map_zero φ.toFun).trans hφ)
  have hi := h.integral_identity φi
    ((tsupport_comp_subset Complex.imCLM.map_zero φ.toFun).trans hφ)
  have hdr := iteratedPartialDeriv_postcomp Complex.reCLM φ.contDiff α
  have hdi := iteratedPartialDeriv_postcomp Complex.imCLM φ.contDiff α
  change iteratedPartialDeriv α φr.toFun =
    (fun x ↦ (iteratedPartialDeriv α φ.toFun x).re) at hdr
  change iteratedPartialDeriv α φi.toFun =
    (fun x ↦ (iteratedPartialDeriv α φ.toFun x).im) at hdi
  have expand (v : ℝ^n → ℂ) (q : ℝ^n → ℂ)
      (hr : Integrable (fun x ↦ v x * ((q x).re : ℂ)) (domainMeasure n Ω))
      (hi : Integrable (fun x ↦ v x * ((q x).im : ℂ)) (domainMeasure n Ω)) :
      ∫ x, v x * q x ∂domainMeasure n Ω =
        (∫ x, v x * ((q x).re : ℂ) ∂domainMeasure n Ω) +
          Complex.I * ∫ x, v x * ((q x).im : ℂ) ∂domainMeasure n Ω := by
    rw [← integral_const_mul, ← integral_add hr (hi.const_mul Complex.I)]
    apply integral_congr_ae
    filter_upwards [] with x
    conv_lhs => rw [← Complex.re_add_im (q x)]
    ring
  have hderiv (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
      MemLp (iteratedPartialDeriv α ψ.toFun) 2 (domainMeasure n Ω) :=
    (PDE.contDiff_top_iteratedPartialDeriv ψ.contDiff α).continuous.memLp_of_hasCompactSupport
      (iteratedPartialDeriv_hasCompactSupport ψ α)
  have htest (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
      MemLp ψ.toFun 2 (domainMeasure n Ω) :=
    ψ.contDiff.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport
  have hfr := hf.integrable_mul (hderiv φr).ofReal
  have hfi := hf.integrable_mul (hderiv φi).ofReal
  rw [hdr] at hfr hr
  rw [hdi] at hfi hi
  have hright := expand g φ.toFun (hg.integrable_mul (htest φr).ofReal)
    (hg.integrable_mul (htest φi).ofReal)
  simp only [TestFunction.toFun_eq_coe] at hright
  rw [expand f (iteratedPartialDeriv α φ.toFun) hfr hfi, hright, hr, hi]
  change _ = (-1 : ℂ) ^ α.length *
    ((∫ x, g x * (φr x : ℂ) ∂domainMeasure n Ω) +
      Complex.I * ∫ x, g x * (φi x : ℂ) ∂domainMeasure n Ω)
  ring

end SobolevSpace
