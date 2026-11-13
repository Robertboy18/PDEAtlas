/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import PDE.FDeriv.Calculus.Symmetric

/-!
# Derivatives of product slices

Differentiation of a slice agrees with the joint derivative in the corresponding
factor direction. These identities require no finite-dimensional hypothesis.
The scalar second factor is useful for time and radius parameters.
-/

@[expose] public noncomputable section

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace PDE

/-- A scalar-parameter slice has the joint derivative in direction `(0, 1)`. -/
theorem deriv_prod_timeSlice
    (f : D × ℝ → E) (x : D) (t : ℝ)
    (hf : DifferentiableAt ℝ f (x, t)) :
    deriv (fun s ↦ f (x, s)) t = fderiv ℝ f (x, t) (0, 1) := by
  exact (hf.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const (x := t) (c := x)).prodMk (hasDerivAt_id t))).deriv

/-- A derivative in the first factor is the joint derivative with zero
second component. -/
theorem fderiv_prod_firstSlice
    (f : D × ℝ → E) (x v : D) (t : ℝ)
    (hf : DifferentiableAt ℝ f (x, t)) :
    fderiv ℝ (fun y ↦ f (y, t)) x v = fderiv ℝ f (x, t) (v, 0) := by
  have h := hf.hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const (x := x) (c := t)))
  simpa [Function.comp_def] using congrArg (fun L : D →L[ℝ] E ↦ L v) h.fderiv

/-- Differentiating in the scalar parameter loses one joint derivative. -/
theorem contDiff_deriv_prod_snd
    {m : ℕ} {f : D × ℝ → E} (hf : ContDiff ℝ (m + 1) f) :
    ContDiff ℝ m (fun p : D × ℝ ↦ deriv (fun s ↦ f (p.1, s)) p.2) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  simp_rw [deriv_prod_timeSlice f _ _ (hd _)]
  exact (hf.fderiv_right (m := m) (by norm_num)).clm_apply contDiff_const

/-- The parameter derivative, evaluated at a fixed parameter, has one fewer
derivative in the first factor. -/
theorem contDiff_deriv_prod_timeSlice
    {m : ℕ} (f : D × ℝ → E) (t : ℝ) (hf : ContDiff ℝ (m + 1) f) :
    ContDiff ℝ m (fun x ↦ deriv (fun s ↦ f (x, s)) t) :=
  (contDiff_deriv_prod_snd hf).comp (contDiff_id.prodMk contDiff_const)

/-- A fixed first-factor directional derivative loses one joint derivative. -/
theorem contDiff_fderiv_prod_firstSlice
    {m : ℕ} {f : D × ℝ → E} (hf : ContDiff ℝ (m + 1) f) (v : D) :
    ContDiff ℝ m (fun p : D × ℝ ↦ fderiv ℝ (fun y ↦ f (y, p.2)) p.1 v) := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  simp_rw [fderiv_prod_firstSlice f _ _ _ (hd _)]
  exact (hf.fderiv_right (m := m) (by norm_num)).clm_apply contDiff_const

/-- First-factor and scalar-parameter differentiation commute for a jointly
`C²` map, by symmetry of its second Fréchet derivative. -/
theorem fderiv_deriv_prod_comm
    {f : D × ℝ → E} (hf : ContDiff ℝ 2 f) (x v : D) (t : ℝ) :
    fderiv ℝ (fun y ↦ deriv (fun s ↦ f (y, s)) t) x v =
      deriv (fun s ↦ fderiv ℝ (fun y ↦ f (y, s)) x v) t := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have ht : Differentiable ℝ (fun p : D × ℝ ↦ fderiv ℝ f p (0, 1)) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const).differentiable one_ne_zero
  have hx : Differentiable ℝ (fun p : D × ℝ ↦ fderiv ℝ f p (v, 0)) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const).differentiable one_ne_zero
  simp_rw [deriv_prod_timeSlice f _ _ (hd _),
    fderiv_prod_firstSlice f _ _ _ (hd _)]
  rw [fderiv_prod_firstSlice _ _ _ _ (ht _), deriv_prod_timeSlice _ _ _ (hx _)]
  exact fderiv_fderiv_apply_comm f (x, t) (0, 1) (v, 0) hf.contDiffAt

end PDE
