/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Differentiating a family along its parameter

For maps between real normed spaces, the derivative along a moving point splits
into parameter and spatial derivatives. Under local joint `C²` regularity,
parameter and spatial differentiation commute by symmetry of the second
Fréchet derivative. No finite-dimensional hypothesis is needed.
-/

@[expose] public noncomputable section

open scoped Topology

namespace PDE.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : ℝ → E → F}

/-- The spatial differential is the restriction of the joint differential at the point. -/
theorem fderiv_space_apply {t : ℝ} {x : E}
    (hU : DifferentiableAt ℝ (fun p : ℝ × E ↦ U p.1 p.2) (t, x)) (v : E) :
    fderiv ℝ (U t) x v =
      fderiv ℝ (fun p : ℝ × E ↦ U p.1 p.2) (t, x) (0, v) := by
  have h := hU.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
  exact congrArg (fun A ↦ A v) h.fderiv

/-- The parameter derivative is the joint differential in the parameter direction. -/
theorem deriv_parameter_eq {t : ℝ} {x : E}
    (hU : DifferentiableAt ℝ (fun p : ℝ × E ↦ U p.1 p.2) (t, x)) :
    deriv (fun s ↦ U s x) t =
      fderiv ℝ (fun p : ℝ × E ↦ U p.1 p.2) (t, x) (1, 0) := by
  exact (hU.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv

/-- Differentiation along a moving spatial point adds its transport derivative
to the derivative at fixed spatial coordinates. Only the germ at `(t, x)` is used. -/
theorem hasDerivAt_moving_point {γ : ℝ → E} {t : ℝ} {x w : E}
    (hU : DifferentiableAt ℝ (fun p : ℝ × E ↦ U p.1 p.2) (t, x))
    (hγ : HasDerivAt γ w t) (hbase : γ t = x) :
    HasDerivAt (fun s ↦ U s (γ s))
      (deriv (fun s ↦ U s x) t + fderiv ℝ (U t) x w) t := by
  rw [deriv_parameter_eq hU, fderiv_space_apply hU, ← map_add]
  have h := (hbase ▸ hU).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk hγ)
  simpa only [hbase, Prod.mk_add_mk, add_zero, zero_add, Function.comp_def, id_eq] using h

/-- The infinitesimal field of a jointly `C²` germ is `C¹` in space. -/
theorem contDiffAt_parameter_deriv {t : ℝ} {x : E}
    (hU : ContDiffAt ℝ 2 (fun p : ℝ × E ↦ U p.1 p.2) (t, x)) :
    ContDiffAt ℝ 1 (fun y ↦ deriv (fun s ↦ U s y) t) x := by
  have hnear : (fun y ↦ deriv (fun s ↦ U s y) t) =ᶠ[𝓝 x]
      (fun y ↦ fderiv ℝ (fun p : ℝ × E ↦ U p.1 p.2) (t, y) (1, 0)) := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually
      (hU.eventually (by norm_num))] with y hy
    exact deriv_parameter_eq (hy.differentiableAt (by norm_num))
  apply ContDiffAt.congr_of_eventuallyEq _ hnear
  exact ((hU.fderiv_right (m := 1) (by norm_num)).comp x
    (contDiffAt_const.prodMk contDiffAt_id)).clm_apply contDiffAt_const

/-- The parameter derivative of a spatial directional derivative is the spatial
derivative of the infinitesimal field. The mixed derivative is proved from a `C²` germ. -/
theorem hasDerivAt_fderiv_space {t : ℝ} {x : E}
    (hU : ContDiffAt ℝ 2 (fun p : ℝ × E ↦ U p.1 p.2) (t, x)) (v : E) :
    HasDerivAt (fun s ↦ fderiv ℝ (U s) x v)
      (fderiv ℝ (fun y ↦ deriv (fun s ↦ U s y) t) x v) t := by
  let F := fun p : ℝ × E ↦ U p.1 p.2
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) (t, x) :=
    (hU.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hnear : (fun y ↦ deriv (fun s ↦ U s y) t) =ᶠ[𝓝 x]
      (fun y ↦ fderiv ℝ F (t, y) (1, 0)) := by
    filter_upwards [(continuousAt_const.prodMk continuousAt_id).eventually
      (hU.eventually (by norm_num))] with y hy
    exact deriv_parameter_eq (hy.differentiableAt (by norm_num))
  have hspace :
      fderiv ℝ (fun y ↦ deriv (fun s ↦ U s y) t) x v =
        fderiv ℝ (fderiv ℝ F) (t, x) (0, v) (1, 0) := by
    rw [hnear.fderiv_eq]
    have h := (hDF.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)).clm_apply
      (hasFDerivAt_const (1, (0 : E)) x)
    simpa using congrArg (fun A ↦ A v) h.fderiv
  rw [hspace, hU.isSymmSndFDerivAt (by simp) (0, v) (1, 0)]
  have hpath : HasDerivAt (fun s ↦ fderiv ℝ F (s, x))
      (fderiv ℝ (fderiv ℝ F) (t, x) (1, 0)) t :=
    hDF.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have happ : HasDerivAt (fun s ↦ fderiv ℝ F (s, x) (0, v))
      (fderiv ℝ (fderiv ℝ F) (t, x) (1, 0) (0, v)) t := by
    simpa only [map_zero, add_zero] using hpath.clm_apply (hasDerivAt_const t (0, v))
  apply happ.congr_of_eventuallyEq
  filter_upwards [(continuousAt_id.prodMk continuousAt_const).eventually
    (hU.eventually (by norm_num))] with s hs
  exact fderiv_space_apply (hs.differentiableAt (by norm_num)) v

end PDE.Analysis
