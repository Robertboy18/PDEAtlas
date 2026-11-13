/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.Sobolev
public import PDE.Analysis.Evolution.Time.WeakDerivative.Basic

/-!
# Real-line weak derivative witnesses for Hilbert transforms

Distributional differentiation of complex `L²` classes gives
`Evolution.HasWeakTimeDerivativeOn`, including local integrability and testing against
real smooth compactly supported functions. Taking real parts yields the same
identity for real representatives.
-/

@[expose] public section

namespace PDE.Analysis

open Evolution MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv ContDiff

noncomputable section

/-- An equality of `L²` tempered distributions gives the weak derivative
identity on the real line, with its local integrability requirements. -/
theorem hasWeakTimeDerivativeOn_of_lineDeriv {f g : ComplexL2}
    (hg : ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ))) :
    HasWeakTimeDerivativeOn Set.univ (f : ℝ → ℂ) (g : ℝ → ℂ) := by
  refine ⟨((Lp.memLp f).locallyIntegrable (by norm_num)).locallyIntegrableOn _,
    ((Lp.memLp g).locallyIntegrable (by norm_num)).locallyIntegrableOn _, ?_⟩
  intro ell φ hφ hsupp _
  let ψ : 𝓢(ℝ, ℂ) :=
    (hsupp.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hφ)
  have hdψ (x : ℝ) : (∂_{(1 : ℝ)} ψ) x = ((deriv φ x : ℝ) : ℂ) := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    change deriv (fun x ↦ (φ x : ℂ)) x = ((deriv φ x : ℝ) : ℂ)
    exact ((hφ.differentiable (by simp) x).hasDerivAt.ofReal_comp).deriv
  have hpair := congrArg (fun T : 𝓢'(ℝ, ℂ) ↦ T ψ) hg
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
    Lp.toTemperedDistribution_apply] at hpair
  have hψ (x : ℝ) : ψ x = (φ x : ℂ) := rfl
  have hscalar : (∫ x, φ x • g x) = -(∫ x, deriv φ x • f x) := by
    simpa only [hdψ, hψ, Complex.coe_smul] using hpair.symm
  have hintg : Integrable (fun x ↦ φ x • g x) :=
    ((Lp.memLp g).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      hφ.continuous hsupp
  have hintf : Integrable (fun x ↦ deriv φ x • f x) :=
    ((Lp.memLp f).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      (hφ.continuous_deriv (by simp)) hsupp.deriv
  have hreal := congrArg ell hscalar
  rw [map_neg, ← ell.integral_comp_comm hintg, ← ell.integral_comp_comm hintf] at hreal
  simpa only [map_smul, smul_eq_mul, mul_comm] using hreal

/-- The real parts of `L²` distributional derivative representatives form a
real weak-derivative pair. -/
theorem hasWeakTimeDerivativeOn_re_of_lineDeriv {f g : ComplexL2}
    (hg : ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ))) :
    HasWeakTimeDerivativeOn Set.univ (fun x ↦ (f x).re) (fun x ↦ (g x).re) :=
  (hasWeakTimeDerivativeOn_of_lineDeriv hg).map Complex.reCLM

/-- Weak differentiation commutes with the concrete Hilbert transform, expressed
through `HasWeakTimeDerivativeOn` for real parts. -/
theorem hasWeakTimeDerivativeOn_re_hilbertTransform {f g : ComplexL2}
    (hg : ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ))) :
    HasWeakTimeDerivativeOn Set.univ
      (fun x ↦ (hilbertTransform f x).re) (fun x ↦ (hilbertTransform g x).re) :=
  hasWeakTimeDerivativeOn_re_of_lineDeriv (lineDeriv_hilbertTransform hg)

/-- A real weak derivative of the zero almost-everywhere class is zero almost
everywhere. The test integrals have locally integrable factors. -/
theorem Evolution.HasWeakTimeDerivativeOn.ae_eq_zero_of_ae_eq_zero
    {f g : ℝ → ℝ} (hw : HasWeakTimeDerivativeOn Set.univ f g)
    (hf : f =ᵐ[volume] 0) : g =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (locallyIntegrableOn_univ.mp hw.locallyIntegrable_g)
  intro φ hφ hc
  have h := hw.integral_eq (ContinuousLinearMap.id ℝ ℝ) φ hφ hc (Set.subset_univ _)
  simp only [ContinuousLinearMap.id_apply] at h
  have hz : (∫ x, f x * deriv φ x) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hf] with x hx
    simp [hx]
  simpa only [hz, neg_zero, smul_eq_mul, mul_comm] using h

/-- A distributional derivative in `L²` of a real almost-everywhere class is
also real almost everywhere. -/
theorem ae_im_lineDeriv_eq_zero {f g : ComplexL2}
    (hg : ∂_{(1 : ℝ)} (f : 𝓢'(ℝ, ℂ)) = (g : 𝓢'(ℝ, ℂ)))
    (hf : (fun x ↦ (f x).im) =ᵐ[volume] 0) :
    (fun x ↦ (g x).im) =ᵐ[volume] 0 :=
  ((hasWeakTimeDerivativeOn_of_lineDeriv hg).map Complex.imCLM).ae_eq_zero_of_ae_eq_zero hf

end

end PDE.Analysis
