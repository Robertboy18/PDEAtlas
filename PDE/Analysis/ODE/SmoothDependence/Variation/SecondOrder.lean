/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import PDE.Analysis.Calculus.Composition
import PDE.Analysis.Calculus.Prod.ParameterDerivative

/-!
# Second speed variation with affine damping

Differentiating a jointly smooth solution family twice in speed gives the Hessian
term and the first-variation forcing from affine damping. The ODE is needed only
at the displayed time for nearby speeds; the state space need not be complete or
finite dimensional.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace PDE.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A supplied jointly `C³` family with affine speed damping has its actual
second speed-variation equation. The time equation is required only on a speed
neighborhood at the displayed time. No time neighborhood of ODE identities,
completeness, or finite-dimensional hypothesis is required. -/
theorem hasDerivAt_secondSpeedVariation_sub_smul
    {F : ℝ → ℝ → E} {f : E → E} {t μ₀ : ℝ}
    (hF : ContDiff ℝ 3 F.uncurry) (hf : ContDiff ℝ 2 f)
    (hode : ∀ᶠ μ in 𝓝 μ₀,
      HasDerivAt (fun s ↦ F s μ) (f (F t μ) - μ • F t μ) t) :
    HasDerivAt (fun s ↦ deriv (deriv (F s)) μ₀)
      (fderiv ℝ f (F t μ₀) (deriv (deriv (F t)) μ₀) +
        fderiv ℝ (fderiv ℝ f) (F t μ₀) (deriv (F t) μ₀) (deriv (F t) μ₀) -
        μ₀ • deriv (deriv (F t)) μ₀ - (2 : ℝ) • deriv (F t) μ₀) t := by
  let D : ℝ → ℝ → E := fun s μ ↦ deriv (F s) μ
  let K : ℝ → E := fun μ ↦ f (F t μ) - μ • F t μ
  have hfamily : ContDiff ℝ 3
      (fun z : (ℝ × ℝ) × ℝ ↦ F z.1.1 z.2) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hDlinear : ContDiff ℝ 2
      (fun u : ℝ × ℝ ↦ fderiv ℝ (F u.1) u.2) :=
    ContDiff.fderiv
      (f := fun (u : ℝ × ℝ) (μ : ℝ) ↦ F u.1 μ)
      (g := fun u : ℝ × ℝ ↦ u.2) hfamily contDiff_snd (by norm_num)
  have hD : ContDiff ℝ 2 D.uncurry := by
    simpa only [D, Function.uncurry_def, fderiv_apply_one_eq_deriv] using
      hDlinear.clm_apply (contDiff_const (c := (1 : ℝ)))
  -- Differentiate the same ODE identity near each nearby speed.
  have hfirst : (fun μ ↦ deriv (fun s ↦ D s μ) t) =ᶠ[𝓝 μ₀] deriv K := by
    filter_upwards [hode.eventually_nhds] with μ hnear
    have heq : (fun ν ↦ deriv (fun s ↦ F s ν) t) =ᶠ[𝓝 μ] K :=
      hnear.mono (fun ν hν ↦ hν.deriv)
    have htime : deriv (fun s ↦ D s μ) t =
        deriv (fun ν ↦ deriv (fun s ↦ F s ν) t) μ := by
      simpa only [D, fderiv_apply_one_eq_deriv] using
        (PDE.Analysis.hasDerivAt_fderiv_space (U := F) (t := t) (x := μ)
          (hF.contDiffAt.of_le (by norm_num)) (1 : ℝ)).deriv
    exact htime.trans heq.deriv_eq
  -- Commute time differentiation with the second ordinary speed derivative.
  have htime : HasDerivAt (fun s ↦ deriv (D s) μ₀)
      (deriv (deriv K) μ₀) t := by
    have h : HasDerivAt (fun s ↦ deriv (D s) μ₀)
        (deriv (fun μ ↦ deriv (fun s ↦ D s μ) t) μ₀) t := by
      simpa only [fderiv_apply_one_eq_deriv] using
        PDE.Analysis.hasDerivAt_fderiv_space (U := D) (t := t) (x := μ₀)
          hD.contDiffAt (1 : ℝ)
    exact h.congr_deriv hfirst.deriv_eq
  have hslice : ContDiff ℝ 2 (F t) :=
    (hF.comp (contDiff_const.prodMk contDiff_id)).of_le (by norm_num)
  have hcomp : ContDiff ℝ 2 (fun μ ↦ f (F t μ)) := hf.comp hslice
  have hprod : ContDiff ℝ 2 (fun μ ↦ μ • F t μ) := contDiff_id.smul hslice
  have hK : deriv K = fun μ ↦ deriv (fun ν ↦ f (F t ν)) μ -
      deriv (fun ν ↦ ν • F t ν) μ := by
    funext μ
    exact deriv_fun_sub (hcomp.differentiable (by norm_num) μ)
      (hprod.differentiable (by norm_num) μ)
  have hsecond_comp : deriv (deriv (fun μ ↦ f (F t μ))) μ₀ =
      fderiv ℝ (fderiv ℝ f) (F t μ₀) (deriv (F t) μ₀) (deriv (F t) μ₀) +
        fderiv ℝ f (F t μ₀) (deriv (deriv (F t)) μ₀) := by
    simpa only [Function.comp_def, fderiv_apply_one_eq_deriv] using
      PDE.Analysis.fderiv_fderiv_comp_apply (f := f) (g := F t) (x := μ₀)
        hf.contDiffAt hslice.contDiffAt (1 : ℝ) (1 : ℝ)
  have hfirst_prod : deriv (fun μ ↦ μ • F t μ) =
      fun μ ↦ μ • deriv (F t) μ + F t μ := by
    funext μ
    simpa only [deriv_id'', one_smul] using
      deriv_fun_smul (𝕜 := ℝ) (f := F t) (c := fun ν : ℝ ↦ ν)
        differentiableAt_id (hslice.differentiable (by norm_num) μ)
  have hsecond_prod : deriv (deriv (fun μ ↦ μ • F t μ)) μ₀ =
      μ₀ • deriv (deriv (F t)) μ₀ + (2 : ℝ) • deriv (F t) μ₀ := by
    rw [hfirst_prod]
    simpa only [one_smul, two_smul, add_assoc, id_eq] using
      (((hasDerivAt_id μ₀).fun_smul
        (hslice.differentiable_deriv_two μ₀).hasDerivAt).fun_add
        (hslice.differentiable (by norm_num) μ₀).hasDerivAt).deriv
  apply htime.congr_deriv
  rw [hK, deriv_fun_sub (hcomp.differentiable_deriv_two μ₀)
    (hprod.differentiable_deriv_two μ₀), hsecond_comp, hsecond_prod]
  abel

end PDE.Analysis.ODE
