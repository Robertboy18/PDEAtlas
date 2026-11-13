/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import PDE.Analysis.Calculus.LocalExtrema
import CAS.ExactTactic

/-!
# Hessian bounds from spatial second differences

For a twice continuously differentiable function, a second-difference upper bound gives
the same upper bound on its Hessian quadratic form. Restriction to a line and the
second-derivative test suffice; the ambient norm need not be differentiable.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The second-difference constant is the upper bound on the Hessian, without a loss
in the constant. The second-difference hypothesis is needed only at the base point. -/
theorem hessian_le_of_second_difference
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {x : E} {C : ℝ}
    (hsemi : ∀ z, f (x + z) - 2 * f x + f (x - z) ≤ C * ‖z‖ ^ 2)
    (v : E) :
    fderiv ℝ (fderiv ℝ f) x v v ≤ C * ‖v‖ ^ 2 := by
  let c := C * ‖v‖ ^ 2
  let F : ℝ → ℝ := fun s ↦ f (x + s • v) + f (x + s • (-v)) - c * s ^ 2
  let F' : ℝ → ℝ := fun s ↦
    fderiv ℝ f (x + s • v) v + fderiv ℝ f (x + s • (-v)) (-v) - 2 * c * s
  have hline (w : E) (s : ℝ) : HasDerivAt (fun r : ℝ ↦ x + r • w) w s := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id s).smul_const w).const_add x
  have hF (s : ℝ) : HasDerivAt F (F' s) s := by
    have hquad : HasDerivAt (fun r : ℝ ↦ c * r ^ 2) (2 * c * s) s := by
      cas
    exact (((hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt
      s (hline v s)).add
      ((hf.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt
        s (hline (-v) s))).sub hquad
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hD (w : E) :
      HasDerivAt (fun s : ℝ ↦ fderiv ℝ f (x + s • w) w)
        (fderiv ℝ (fderiv ℝ f) x w w) 0 := by
    have hcomp :
        HasDerivAt (fun s : ℝ ↦ fderiv ℝ f (x + s • w))
          (fderiv ℝ (fderiv ℝ f) (x + (0 : ℝ) • w) w) 0 :=
      (hdf _).hasFDerivAt.comp_hasDerivAt 0 (hline w 0)
    have happ := hcomp.clm_apply (hasDerivAt_const (0 : ℝ) w)
    simpa only [zero_smul, add_zero, ContinuousLinearMap.map_zero,
      Function.comp_apply] using happ
  have hlinear : HasDerivAt (fun s : ℝ ↦ 2 * c * s) (2 * c) 0 := by
    cas
  have hF' : HasDerivAt F' (2 * fderiv ℝ (fderiv ℝ f) x v v - 2 * c) 0 := by
    convert ((hD v).add (hD (-v))).sub hlinear using 1
    simp [two_mul]
  have hmax : IsLocalMax F 0 := by
    apply Filter.Eventually.of_forall
    intro s
    have h := hsemi (s • v)
    have hnorm : ‖s • v‖ ^ 2 = s ^ 2 * ‖v‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [hnorm] at h
    simpa only [F, zero_smul, add_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, sub_zero, smul_neg, ← sub_eq_add_neg] using
      (show f (x + s • v) + f (x - s • v) - c * s ^ 2 ≤ f x + f x by
        dsimp only [c]
        nlinarith [h])
  have hcurv := hmax.deriv_deriv_nonpos (hF 0).continuousAt
  have heq : deriv F = F' := funext fun s ↦ (hF s).deriv
  rw [heq, hF'.deriv] at hcurv
  dsimp only [c] at hcurv
  linarith

end PDE.Analysis
