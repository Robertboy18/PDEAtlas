/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import PDE.Analysis.Calculus.LocalExtrema

/-!
# Second derivatives along affine lines

The curvature fact needed by maximum principles is the same for elliptic and parabolic
equations: a function has nonpositive second derivative in every direction at a local maximum.
We prove that fact and the linearity rules for the affine-line derivative.

The definition uses ordinary derivatives along a line, so it makes sense in any real normed
space. As with Mathlib's derivative, it is a total expression; the addition and curvature
theorems carry the regularity needed to interpret it classically.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The second derivative at zero of `s ↦ f (x + s • v)`. -/
def secondDirectionalDerivative (f : E → ℝ) (x v : E) : ℝ :=
  deriv (deriv (fun s : ℝ ↦ f (x + s • v))) 0

/-- At a local maximum where the function is continuous, every totalized directional
second derivative is nonpositive.

Restricting to an affine line reduces this to the one-dimensional test
`IsLocalMax.deriv_deriv_nonpos`, which rests on Mathlib's second-derivative test. -/
theorem secondDirectionalDerivative_nonpos_at_localMax
    {f : E → ℝ} {x : E}
    (hmax : IsLocalMax f x) (hf : ContinuousAt f x) (v : E) :
    secondDirectionalDerivative f x v ≤ 0 := by
  let line : ℝ → E := fun s ↦ x + s • v
  have hline0 : line 0 = x := by simp [line]
  have hlineMax : IsLocalMax (f ∘ line) 0 := by
    have hmax' : IsLocalMax f (line 0) := by simpa [hline0] using hmax
    exact hmax'.comp_continuous (show ContinuousAt line 0 by fun_prop)
  have hlineReg : ContinuousAt (f ∘ line) 0 := by
    have hf' : ContinuousAt f (line 0) := by simpa [hline0] using hf
    exact hf'.comp (show ContinuousAt line 0 by fun_prop)
  simpa [secondDirectionalDerivative, line, Function.comp_def] using
    IsLocalMax.deriv_deriv_nonpos hlineMax hlineReg

/-- Directional second differentiation commutes with addition at a common `C²` point. -/
theorem secondDirectionalDerivative_add
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (v : E) :
    secondDirectionalDerivative (fun y ↦ f y + g y) x v =
      secondDirectionalDerivative f x v + secondDirectionalDerivative g x v := by
  have hline : ContDiffAt ℝ 2 (fun s : ℝ ↦ x + s • v) 0 := by fun_prop
  have hfline : ContDiffAt ℝ 2 (fun s : ℝ ↦ f (x + s • v)) 0 := by
    exact (show ContDiffAt ℝ 2 f (x + (0 : ℝ) • v) by simpa using hf).comp 0 hline
  have hgline : ContDiffAt ℝ 2 (fun s : ℝ ↦ g (x + s • v)) 0 := by
    exact (show ContDiffAt ℝ 2 g (x + (0 : ℝ) • v) by simpa using hg).comp 0 hline
  simpa [secondDirectionalDerivative, iteratedDeriv_eq_iterate,
    Function.iterate_succ_apply] using iteratedDeriv_fun_add hfline hgline

/-- Constant scalar multiplication commutes with directional second differentiation,
including its totalized values at nonsmooth functions. -/
theorem secondDirectionalDerivative_const_mul (c : ℝ) (f : E → ℝ) (x v : E) :
    secondDirectionalDerivative (fun y ↦ c * f y) x v =
      c * secondDirectionalDerivative f x v := by
  simp only [secondDirectionalDerivative, deriv_const_mul_field', deriv_const_mul_field]

/-- Directional second differentiation commutes with negation. -/
theorem secondDirectionalDerivative_neg (f : E → ℝ) (x v : E) :
    secondDirectionalDerivative (fun y ↦ -f y) x v =
      -secondDirectionalDerivative f x v := by
  let g : ℝ → ℝ := fun s ↦ f (x + s • v)
  change deriv (deriv (-g)) 0 = -deriv (deriv g) 0
  rw [deriv.neg']
  exact deriv.neg

/-- At a `C²` point, the affine-line definition is the Hessian evaluated twice in
the direction. This connects the one-dimensional maximum test with Fréchet calculus. -/
theorem secondDirectionalDerivative_eq_fderiv
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (v : E) :
    secondDirectionalDerivative f x v = fderiv ℝ (fderiv ℝ f) x v v := by
  have hline (t : ℝ) : HasDerivAt (fun s : ℝ ↦ x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ContDiffAt ℝ 2 f (x + t • v) := by
    have hcont : ContinuousAt (fun t : ℝ ↦ x + t • v) 0 := by fun_prop
    have h := hcont.eventually (show ∀ᶠ y in 𝓝 (x + (0 : ℝ) • v),
        ContDiffAt ℝ 2 f y by simpa using hf.eventually (by simp))
    exact h
  have hfirst :
      deriv (fun s : ℝ ↦ f (x + s • v)) =ᶠ[𝓝 0]
        fun s ↦ fderiv ℝ f (x + s • v) v := by
    filter_upwards [hnear] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
      t (hline t)).deriv
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hg : DifferentiableAt ℝ (fun y ↦ fderiv ℝ f y v) x :=
    hd.clm_apply (differentiableAt_const v)
  rw [secondDirectionalDerivative, hfirst.deriv_eq]
  change lineDeriv ℝ (fun y ↦ fderiv ℝ f y v) x v = _
  rw [hg.lineDeriv_eq_fderiv, fderiv_clm_apply hd (differentiableAt_const v)]
  simp

/-- Reversing a direction does not change the second directional derivative at a `C²` point. -/
theorem secondDirectionalDerivative_neg_direction
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (v : E) :
    secondDirectionalDerivative f x (-v) = secondDirectionalDerivative f x v := by
  rw [secondDirectionalDerivative_eq_fderiv hf, secondDirectionalDerivative_eq_fderiv hf]
  simp

end PDE.Analysis
