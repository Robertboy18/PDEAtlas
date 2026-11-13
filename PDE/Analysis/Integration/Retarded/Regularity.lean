/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.Retarded.ContinuousDerivative
public import PDE.Analysis.Calculus.ContinuousFamily.IteratedDerivative
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Second regularity of retarded integrals

An age-zero vanishing kernel yields a `C²` retarded integral from a continuous
family of `C²` spatial and age jets. Its derivative-valued kernel has
a possibly nonzero endpoint; continuity suffices to retain that term.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Vanishing at age zero removes the endpoint from the first derivative. -/
theorem fderiv_retardedIntegral_of_zero
    {F : ℝ → E × ℝ → V}
    (hF : ∀ s, Differentiable ℝ (F s))
    (hc : Continuous (fun p : ℝ × (E × ℝ) ↦ F p.1 p.2))
    (hD : Continuous (fun p : ℝ × (E × ℝ) ↦ fderiv ℝ (F p.1) p.2))
    (hzero : ∀ s x, F s (x, 0) = 0) :
    fderiv ℝ (retardedIntegral F) = retardedIntegral (fun s ↦ fderiv ℝ (F s)) := by
  funext p
  simpa only [hzero, ContinuousLinearMap.smulRight_zero, zero_add] using
    (hasFDerivAt_retardedIntegral hF hc hD p).fderiv

/-- The second derivative retains the derivative-valued age-zero endpoint. -/
theorem fderiv_fderiv_retardedIntegral
    {F : ℝ → E × ℝ → V}
    (hF : ∀ s, Differentiable ℝ (F s))
    (hDF : ∀ s, Differentiable ℝ (fderiv ℝ (F s)))
    (hc : Continuous (fun p : ℝ × (E × ℝ) ↦ F p.1 p.2))
    (hD : Continuous (fun p : ℝ × (E × ℝ) ↦ fderiv ℝ (F p.1) p.2))
    (hDD : Continuous (fun p : ℝ × (E × ℝ) ↦ fderiv ℝ (fderiv ℝ (F p.1)) p.2))
    (hzero : ∀ s x, F s (x, 0) = 0) (p : E × ℝ) :
    fderiv ℝ (fderiv ℝ (retardedIntegral F)) p =
      (ContinuousLinearMap.snd ℝ E ℝ).smulRight (fderiv ℝ (F p.2) (p.1, 0)) +
        retardedIntegral (fun s ↦ fderiv ℝ (fderiv ℝ (F s))) p := by
  rw [fderiv_retardedIntegral_of_zero hF hc hD hzero]
  exact (hasFDerivAt_retardedIntegral hDF hD hDD p).fderiv

/-- Evaluating the second derivative in two directions commutes with the
finite retarded integral, including its age-zero endpoint. -/
theorem fderiv_fderiv_retardedIntegral_apply
    {F : ℝ → E × ℝ → V}
    (hF : ∀ s, Differentiable ℝ (F s))
    (hDF : ∀ s, Differentiable ℝ (fderiv ℝ (F s)))
    (hc : Continuous (fun p : ℝ × (E × ℝ) ↦ F p.1 p.2))
    (hD : Continuous (fun p : ℝ × (E × ℝ) ↦ fderiv ℝ (F p.1) p.2))
    (hDD : Continuous (fun p : ℝ × (E × ℝ) ↦ fderiv ℝ (fderiv ℝ (F p.1)) p.2))
    (hzero : ∀ s x, F s (x, 0) = 0) (p v w : E × ℝ) :
    fderiv ℝ (fderiv ℝ (retardedIntegral F)) p v w =
      v.2 • fderiv ℝ (F p.2) (p.1, 0) w +
        ∫ s in (0 : ℝ)..p.2, fderiv ℝ (fderiv ℝ (F s)) (p.1, p.2 - s) v w := by
  let L := (ContinuousLinearMap.apply ℝ V w).comp
      (ContinuousLinearMap.apply ℝ ((E × ℝ) →L[ℝ] V) v)
  rw [fderiv_fderiv_retardedIntegral hF hDF hc hD hDD hzero]
  simp only [add_apply, ContinuousLinearMap.smulRight_apply, smul_apply]
  congr 1
  refine (ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ) (F := V) L
    (f := fun s ↦ fderiv ℝ (fderiv ℝ (F s)) (p.1, p.2 - s)) ?_).symm
  exact (hDD.comp (continuous_id.prodMk
    (continuous_const.prodMk (continuous_const.sub continuous_id)))).intervalIntegrable 0 p.2

/-- A continuously indexed `C²` kernel vanishing at age zero has a `C²` retarded integral.
No differentiability with respect to the integration index is required. -/
theorem contDiff_two_retardedIntegral
    {F : ℝ → E × ℝ → V}
    (hF : ∀ s, ContDiff ℝ 2 (F s))
    (hjet : ∀ j ≤ 2, Continuous
      (fun p : ℝ × (E × ℝ) ↦ iteratedFDeriv ℝ j (F p.1) p.2))
    (hzero : ∀ s x, F s (x, 0) = 0) :
    ContDiff ℝ 2 (retardedIntegral F) := by
  have hc : Continuous (fun p : ℝ × (E × ℝ) ↦ F p.1 p.2) :=
    continuous_of_continuous_iteratedFDeriv_zero_family (hjet 0 (by omega))
  have hD : Continuous (fun p : ℝ × (E × ℝ) ↦ fderiv ℝ (F p.1) p.2) :=
    continuous_of_continuous_iteratedFDeriv_zero_family (f := fun s ↦ fderiv ℝ (F s))
      (continuous_iteratedFDeriv_fderiv_family (f := F) (j := 0) (hjet 1 (by omega)))
  have hDD : Continuous
      (fun p : ℝ × (E × ℝ) ↦ fderiv ℝ (fderiv ℝ (F p.1)) p.2) :=
    continuous_of_continuous_iteratedFDeriv_zero_family
      (f := fun s ↦ fderiv ℝ (fderiv ℝ (F s)))
      (continuous_iteratedFDeriv_fderiv_family (f := fun s ↦ fderiv ℝ (F s)) (j := 0)
        (continuous_iteratedFDeriv_fderiv_family (f := F) (j := 1) (hjet 2 (by omega))))
  have hd (p : E × ℝ) :
      HasFDerivAt (retardedIntegral F)
        (retardedIntegral (fun s ↦ fderiv ℝ (F s)) p) p := by
    simpa only [hzero, ContinuousLinearMap.smulRight_zero, zero_add] using
      hasFDerivAt_retardedIntegral
        (fun s ↦ (hF s).differentiable (by norm_num)) hc hD p
  apply contDiff_succ_iff_hasFDerivAt.mpr
  refine ⟨retardedIntegral (fun s ↦ fderiv ℝ (F s)), ?_, hd⟩
  exact contDiff_one_retardedIntegral
    (F := fun s ↦ fderiv ℝ (F s))
    (fun s ↦ ((hF s).fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero)
    hD hDD

end PDE.Analysis
