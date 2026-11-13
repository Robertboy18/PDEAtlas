/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

/-!
# The remainder after subtracting a linearization

Translate a map to the origin and subtract its value and derivative at the
base point. The resulting remainder has zero value and zero derivative at the
origin. Regularity is inherited without a derivative loss.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The nonlinear remainder in the linearization of `f` at `a`, written in
displacement coordinates. -/
def linearRemainder (f : E → F) (a x : E) : F :=
  f (a + x) - f a - fderiv ℝ f a x

/-- The translated linear remainder vanishes at the origin. -/
@[simp] theorem linearRemainder_zero (f : E → F) (a : E) :
    linearRemainder f a 0 = 0 := by
  simp [linearRemainder]

/-- Its derivative is the difference between the two actual derivatives. -/
theorem hasFDerivAt_linearRemainder {f : E → F} (a x : E)
    (hf : DifferentiableAt ℝ f (a + x)) :
    HasFDerivAt (linearRemainder f a) (fderiv ℝ f (a + x) - fderiv ℝ f a) x := by
  have hd := ((hf.hasFDerivAt.comp x ((hasFDerivAt_id x).const_add a)).sub_const
    (f a)).sub (fderiv ℝ f a).hasFDerivAt
  simpa only [ContinuousLinearMap.comp_id, linearRemainder, Function.comp_def,
    Pi.sub_apply] using! hd

/-- Subtracting the actual linearization removes the first derivative at zero. -/
theorem hasFDerivAt_linearRemainder_zero {f : E → F} (a : E)
    (hf : DifferentiableAt ℝ f a) :
    HasFDerivAt (linearRemainder f a) (0 : E →L[ℝ] F) 0 := by
  have hd := hasFDerivAt_linearRemainder a 0 (by simpa only [add_zero] using hf)
  have he : fderiv ℝ f (a + 0) - fderiv ℝ f a = (0 : E →L[ℝ] F) := by
    rw [add_zero, sub_self]
  rwa [he] at hd

/-- Subtracting a fixed affine map preserves every finite or infinite
regularity order. -/
theorem contDiff_linearRemainder {f : E → F} {n : WithTop ℕ∞}
    (hf : ContDiff ℝ n f) (a : E) :
    ContDiff ℝ n (linearRemainder f a) :=
  ((hf.comp (contDiff_const.add contDiff_id)).sub contDiff_const).sub
    (fderiv ℝ f a).contDiff

/-- The Hessian is unchanged by subtracting the linearization. Its base point
is translated along with the remainder. -/
theorem fderiv_fderiv_linearRemainder {f : E → F}
    (hf : ContDiff ℝ 2 f) (a x : E) :
    fderiv ℝ (fderiv ℝ (linearRemainder f a)) x =
      fderiv ℝ (fderiv ℝ f) (a + x) := by
  have hd : fderiv ℝ (linearRemainder f a) =
      fun y ↦ fderiv ℝ f (a + y) - fderiv ℝ f a := by
    funext y
    exact (hasFDerivAt_linearRemainder a y
      (hf.differentiable (by norm_num) (a + y))).fderiv
  rw [hd]
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h := (((hDf.differentiable one_ne_zero (a + x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_add a)).sub_const (fderiv ℝ f a)).fderiv
  simpa only [ContinuousLinearMap.comp_id, Function.comp_def] using! h

/-- Along a C² curve through the origin, the second derivative of the
remainder depends only on the curve's tangent. The curve's acceleration
disappears because the remainder has zero first derivative. -/
theorem iteratedDeriv_two_linearRemainder_comp {f : E → F}
    (hf : ContDiff ℝ 2 f) (a : E) {γ : ℝ → E} {t : ℝ}
    (hγ : ContDiffAt ℝ 2 γ t) (hγ0 : γ t = 0) :
    iteratedDeriv 2 (fun s ↦ linearRemainder f a (γ s)) t =
      fderiv ℝ (fderiv ℝ f) a (deriv γ t) (deriv γ t) := by
  have hR0 := (hasFDerivAt_linearRemainder_zero a
    (hf.differentiable (by norm_num) a)).fderiv
  have h := iteratedDeriv_vcomp_two (contDiff_linearRemainder hf a).contDiffAt hγ
  simpa only [Function.comp_def, hγ0, iteratedFDeriv_two_apply,
    fderiv_fderiv_linearRemainder hf, add_zero, hR0, zero_apply] using h

end PDE.Analysis
