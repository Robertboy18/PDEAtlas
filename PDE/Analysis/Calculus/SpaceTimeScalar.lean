/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Derivatives of scalar space-time fields

For a real field with a joint `C²` germ, symmetry of the second Fréchet
derivative identifies the two mixed derivatives. The hypothesis is local
at a single point; separate smoothness in the two variables would not suffice.
Spatial differentiation also lowers the joint regularity by one order, and
signed spatial reflection preserves it.
-/

@[expose] public section

open scoped Topology

namespace PDE.Analysis.Calculus

private theorem hasDerivAt_fderiv_apply
    {field : ℝ × ℝ → ℝ} {path : ℝ → ℝ × ℝ} {t : ℝ} {v : ℝ × ℝ}
    (hfield : ContDiffAt ℝ 2 field (path t))
    (hpath : HasDerivAt path v t) (w : ℝ × ℝ) :
    HasDerivAt (fun s ↦ fderiv ℝ field (path s) w)
      (fderiv ℝ (fderiv ℝ field) (path t) v w) t := by
  have hsecond : DifferentiableAt ℝ (fderiv ℝ field) (path t) :=
    (hfield.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h : HasDerivAt (fun s ↦ fderiv ℝ field (path s))
      (fderiv ℝ (fderiv ℝ field) (path t) v) t :=
    hsecond.hasFDerivAt.comp_hasDerivAt t hpath
  simpa only [map_zero, add_zero] using h.clm_apply (hasDerivAt_const t w)

/-- A joint `C²` germ permits time differentiation of the spatial derivative.
The mixed derivative is the spatial derivative of the time trace. -/
theorem hasDerivAt_spatial_deriv
    {field : ℝ → ℝ → ℝ} {x t : ℝ}
    (hfield : ContDiffAt ℝ 2 (Function.uncurry field) (x, t)) :
    HasDerivAt (fun s ↦ deriv (fun y ↦ field y s) x)
      (deriv (fun y ↦ deriv (field y) t) x) t := by
  have htime : HasDerivAt (fun s ↦ deriv (fun y ↦ field y s) x)
      (fderiv ℝ (fderiv ℝ (Function.uncurry field)) (x, t) (0, 1) (1, 0)) t := by
    have hcurve : HasDerivAt (fun s : ℝ ↦ (x, s)) (0, 1) t :=
      (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
    have hneighborhood := hcurve.continuousAt.tendsto.eventually (hfield.eventually (by simp))
    have h' := hasDerivAt_fderiv_apply (path := fun s ↦ (x, s)) hfield hcurve (1, 0)
    apply h'.congr_of_eventuallyEq
    filter_upwards [hneighborhood] with s hs
    have hspace : HasDerivAt (fun y : ℝ ↦ (y, s)) (1, 0) x :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const x s)
    exact ((hs.differentiableAt two_ne_zero).hasFDerivAt.comp_hasDerivAt x hspace).deriv
  have hspace : HasDerivAt (fun y ↦ deriv (field y) t)
      (fderiv ℝ (fderiv ℝ (Function.uncurry field)) (x, t) (1, 0) (0, 1)) x := by
    have hcurve : HasDerivAt (fun y : ℝ ↦ (y, t)) (1, 0) x :=
      (hasDerivAt_id x).prodMk (hasDerivAt_const x t)
    have hneighborhood := hcurve.continuousAt.tendsto.eventually (hfield.eventually (by simp))
    have h' := hasDerivAt_fderiv_apply (path := fun y ↦ (y, t)) (t := x)
      hfield hcurve (0, 1)
    apply h'.congr_of_eventuallyEq
    filter_upwards [hneighborhood] with y hy
    have htime : HasDerivAt (fun s : ℝ ↦ (y, s)) (0, 1) t :=
      (hasDerivAt_const t y).prodMk (hasDerivAt_id t)
    exact ((hy.differentiableAt two_ne_zero).hasFDerivAt.comp_hasDerivAt t htime).deriv
  apply htime.congr_deriv
  rw [hspace.deriv]
  exact (hfield.isSymmSndFDerivAt (by simp)).eq (0, 1) (1, 0)

/-- Signed spatial reflection preserves joint regularity of any finite order. -/
theorem contDiff_neg_reflect {f : ℝ → ℝ → ℝ} {n : ℕ∞}
    (hf : ContDiff ℝ n (Function.uncurry f)) :
    ContDiff ℝ n (Function.uncurry (fun x t ↦ -f (-x) t)) :=
  (hf.comp (contDiff_fst.neg.prodMk contDiff_snd)).neg

/-- Taking the spatial derivative of a jointly `Cⁿ⁺¹` scalar field leaves a
jointly `Cⁿ` field. The spatial derivative is the Fréchet derivative evaluated
on the first coordinate vector. -/
theorem contDiff_spatial_deriv {w : ℝ → ℝ → ℝ} {n : ℕ}
    (hw : ContDiff ℝ (n + 1) (Function.uncurry w)) :
    ContDiff ℝ n (fun p : ℝ × ℝ ↦ deriv (fun x ↦ w x p.2) p.1) := by
  have hD := (hw.fderiv_right (m := n) (by simp)).clm_apply
    (contDiff_const (c := ((1, 0) : ℝ × ℝ)))
  convert hD using 1
  funext p
  have hpath : HasDerivAt (fun x : ℝ ↦ (x, p.2)) (1, 0) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  exact ((hw.differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt p.1 hpath).deriv

end PDE.Analysis.Calculus
