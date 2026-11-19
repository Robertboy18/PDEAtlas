/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime
public import PDE.FDeriv.Calculus
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import CAS.ExactTactic

/-!
# Exponential extension in one extra coordinate

The extension `exp(s) * u(x)` follows the convention of `PDE.FDeriv.SpaceTime`:
the extra coordinate is zero and spatial coordinates are successors.
All derivative identities require regularity only near the evaluation point.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open PDE.Common
open scoped Topology ContDiff

variable {n : ℕ}

/-- Extend a scalar function by multiplication by the exponential of the extra coordinate. -/
def exponentialExtension (u : ℝ^n → ℝ) (p : ℝ^(n + 1)) : ℝ :=
  Real.exp (time p) * u (spatialPart p)

@[simp]
theorem exponentialExtension_timeSpaceCons (u : ℝ^n → ℝ) (s : ℝ) (x : ℝ^n) :
    exponentialExtension u (timeSpaceCons s x) = Real.exp s * u x := by
  simp [exponentialExtension]

/-- Local regularity of the exponential extension. -/
theorem contDiffAt_exponentialExtension {u : ℝ^n → ℝ} {p : ℝ^(n + 1)}
    {m : ℕ∞ω} (hu : ContDiffAt ℝ m u (spatialPart p)) :
    ContDiffAt ℝ m (exponentialExtension u) p := by
  have hspace : ContDiffAt ℝ m (fun q ↦ u (spatialPart q)) p := by
    simpa only [spatialPartCLM_eq_spatialPart, Function.comp_def] using
      hu.comp p (spatialPartCLM n).contDiff.contDiffAt
  exact ((timeCLM n).contDiff.contDiffAt.exp).mul hspace

/-- Exponential extension in a spatial coordinate preserves joint regularity
with an additional real parameter, such as physical time. -/
theorem contDiffAt_exponentialExtension_uncurry {u : ℝ^n → ℝ → ℝ}
    {p : ℝ^(n + 1) × ℝ} {m : ℕ∞ω}
    (hu : ContDiffAt ℝ m (Function.uncurry u) (spatialPart p.1, p.2)) :
    ContDiffAt ℝ m
      (fun q : ℝ^(n + 1) × ℝ ↦ exponentialExtension (fun x ↦ u x q.2) q.1) p := by
  have hspace : ContDiffAt ℝ m
      (fun q : ℝ^(n + 1) × ℝ ↦ (spatialPart q.1, q.2)) p := by
    simpa only [Function.comp_def, spatialPartCLM_eq_spatialPart] using!
      (((spatialPartCLM n).contDiff.contDiffAt.comp p contDiffAt_fst).prodMk contDiffAt_snd)
  have hu' : ContDiffAt ℝ m (fun q : ℝ^(n + 1) × ℝ ↦ u (spatialPart q.1) q.2) p :=
    hu.comp p (f := fun q ↦ (spatialPart q.1, q.2)) hspace
  simpa only [exponentialExtension, Function.comp_def, timeCLM_apply] using!
    (((timeCLM n).contDiff.contDiffAt.comp p contDiffAt_fst).exp).mul hu'

/-- First-order regularity, without imposing a second derivative. -/
theorem differentiableAt_exponentialExtension {u : ℝ^n → ℝ} {p : ℝ^(n + 1)}
    (hu : DifferentiableAt ℝ u (spatialPart p)) :
    DifferentiableAt ℝ (exponentialExtension u) p := by
  have hspace : DifferentiableAt ℝ (fun q ↦ u (spatialPart q)) p := by
    simpa only [spatialPartCLM_eq_spatialPart, Function.comp_def] using!
      hu.comp p (spatialPartCLM n).differentiableAt
  exact ((timeCLM n).differentiableAt.exp).mul hspace

/-- Differentiation in the added coordinate leaves the extension unchanged. -/
theorem partialDeriv_zero_exponentialExtension {u : ℝ^n → ℝ} {p : ℝ^(n + 1)}
    (hu : DifferentiableAt ℝ u (spatialPart p)) :
    (∂[0] (exponentialExtension u)) p = exponentialExtension u p := by
  have hd : DifferentiableAt ℝ (exponentialExtension u)
      (timeSpaceCons (p 0) (spatialPart p)) := by
    simpa only [timeSpaceCons_spatialPart] using differentiableAt_exponentialExtension hu
  have h := partialDeriv_timeSpaceCons_eq_deriv (exponentialExtension u)
    (spatialPart p) (p 0) hd
  simp only [timeSpaceCons_spatialPart, exponentialExtension_timeSpaceCons] at h
  rw [h]
  change deriv (fun s ↦ Real.exp s * u (spatialPart p)) (p 0) =
    Real.exp (p 0) * u (spatialPart p)
  cas

/-- Spatial differentiation commutes with exponential extension. Without differentiability of
`u` both sides vanish: the extension is then not differentiable either. -/
theorem partialDeriv_succ_exponentialExtension {u : ℝ^n → ℝ} {p : ℝ^(n + 1)} (i : Fin n) :
    (∂[i.succ] (exponentialExtension u)) p =
      exponentialExtension (∂[i] u) p := by
  by_cases hu : DifferentiableAt ℝ u (spatialPart p)
  · have hd : DifferentiableAt ℝ (exponentialExtension u)
        (timeSpaceCons (p 0) (spatialPart p)) := by
      simpa only [timeSpaceCons_spatialPart] using differentiableAt_exponentialExtension hu
    have h := partialDeriv_timeSpaceCons_spatial i (exponentialExtension u)
      (p 0) (spatialPart p) hd
    simp only [timeSpaceCons_spatialPart, exponentialExtension_timeSpaceCons] at h
    rw [← h]
    exact partialDeriv_const_smul _
  · have hE : ¬ DifferentiableAt ℝ (exponentialExtension u) p := by
      intro hE
      rw [← timeSpaceCons_spatialPart p] at hE
      refine hu (((hE.comp _ (hasFDerivAt_timeSpaceCons_spatial n (p 0) _).differentiableAt
        ).const_mul (Real.exp (-(p 0)))).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun y ↦ ?_))
      simp only [Function.comp_apply, exponentialExtension_timeSpaceCons, ← mul_assoc,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    simp only [PDE.partialDeriv, fderiv_zero_of_not_differentiableAt hE,
      fderiv_zero_of_not_differentiableAt hu, exponentialExtension, zero_apply, mul_zero]

/-- The second derivative in the extra coordinate equals the original extension. -/
theorem secondPartialDeriv_zero_exponentialExtension {u : ℝ^n → ℝ} {p : ℝ^(n + 1)}
    (hu : ContDiffAt ℝ 2 u (spatialPart p)) :
    (∂[0] (∂[0] (exponentialExtension u))) p = exponentialExtension u p := by
  have he : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 2 u (spatialPart q) := by
    have hc : ContinuousAt (spatialPart (n := n)) p := by
      change ContinuousAt (fun q ↦ spatialPart q) p
      simpa only [spatialPartCLM_eq_spatialPart] using
        (show ContinuousAt (fun q ↦ spatialPartCLM n q) p from
          (spatialPartCLM n).continuous.continuousAt)
    exact hc.eventually (hu.eventually (by norm_num))
  have hg : (∂[0] (exponentialExtension u)) =ᶠ[𝓝 p] exponentialExtension u := by
    filter_upwards [he] with q hq
    exact partialDeriv_zero_exponentialExtension (hq.differentiableAt (by norm_num))
  rw [partialDeriv_congr_nhds 0 hg]
  exact partialDeriv_zero_exponentialExtension (hu.differentiableAt (by norm_num))

/-- Two spatial derivatives commute with extension. -/
theorem secondPartialDeriv_succ_exponentialExtension {u : ℝ^n → ℝ} {p : ℝ^(n + 1)} (i j : Fin n) :
    (∂[i.succ] (∂[j.succ] (exponentialExtension u))) p =
      exponentialExtension (∂[i] (∂[j] u)) p := by
  rw [show (∂[j.succ] (exponentialExtension u)) = exponentialExtension (∂[j] u) from
    funext fun _ ↦ partialDeriv_succ_exponentialExtension j]
  exact partialDeriv_succ_exponentialExtension i

end PDE.Analysis
