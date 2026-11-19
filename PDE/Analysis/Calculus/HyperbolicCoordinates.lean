/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.SecondDerivativeComposition
public import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Local inverse hyperbolic coordinate formulas

First and second derivatives under `arsinh`, and the third derivative at the
origin, need only local regularity. These formulas apply to finite spline
patches without a global smoothness assumption.
-/

@[expose] public section
open Filter
namespace PDE.Calculus

/-- The first physical derivative of a locally differentiable computational profile. -/
theorem deriv_comp_arsinh_at_sinh {f : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) :
    deriv (f ∘ Real.arsinh) (Real.sinh x) = deriv f x / Real.cosh x := by
  have hf' : HasDerivAt f (deriv f x) (Real.arsinh (Real.sinh x)) := by
    simpa using hf.hasDerivAt
  have h := hf'.comp (Real.sinh x) (Real.hasDerivAt_arsinh (Real.sinh x))
  have hs : √(1 + Real.sinh x ^ 2) = Real.cosh x := by
    simpa using (Real.cosh_arsinh (Real.sinh x)).symm
  simpa [hs, div_eq_mul_inv] using h.deriv

/-- The second physical derivative of a locally twice smooth computational profile. -/
theorem second_deriv_comp_arsinh_at_sinh {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) :
    deriv (deriv (f ∘ Real.arsinh)) (Real.sinh x) =
      (deriv (deriv f) x - deriv f x * (Real.sinh x / Real.cosh x)) /
        Real.cosh x ^ 2 := by
  let g := f ∘ Real.arsinh
  have hg : ContDiffAt ℝ 2 g (Real.sinh x) := by
    apply ContDiffAt.comp
    · simpa using hf
    · exact Real.contDiff_arsinh.contDiffAt
  have hgLocal : ∀ᶠ y in nhds (Real.sinh x), DifferentiableAt ℝ g y :=
    (hg.eventually (by norm_num)).mono fun _ hy ↦ hy.differentiableAt (by norm_num)
  have hg' : DifferentiableAt ℝ (deriv g) (Real.sinh x) :=
    (hg.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : g ∘ Real.sinh = f := by
    funext t
    simp [g, Function.comp_def]
  have h := (PDE.Calculus.hasDerivAt_deriv_comp hgLocal hg' Real.contDiff_sinh).deriv
  rw [heq, Real.deriv_sinh, Real.deriv_cosh] at h
  have hd := deriv_comp_arsinh_at_sinh (hf.differentiableAt (by norm_num))
  change deriv g (Real.sinh x) = _ at hd
  rw [hd] at h
  have hc := ne_of_gt (Real.cosh_pos x)
  change deriv (deriv g) (Real.sinh x) = _
  field_simp [hc] at h ⊢
  nlinarith [h]

/-- At the origin, the third derivative under `arsinh` subtracts the first
computational derivative. Only local `C³` regularity is needed. -/
theorem third_deriv_comp_arsinh_zero {f : ℝ → ℝ}
    (hf : ContDiffAt ℝ 3 f 0) :
    deriv (deriv (deriv (f ∘ Real.arsinh))) 0 =
      deriv (deriv (deriv f)) 0 - deriv f 0 := by
  let g := f ∘ Real.arsinh
  have hg : ContDiffAt ℝ 3 g 0 := by
    apply ContDiffAt.comp
    · simpa using hf
    · exact Real.contDiff_arsinh.contDiffAt
  have hf1 : ContDiffAt ℝ 2 (deriv f) 0 := hf.derivWithin (m := 2) (by norm_num)
  have hf2 : ContDiffAt ℝ 1 (deriv (deriv f)) 0 :=
    hf1.derivWithin (m := 1) (by norm_num)
  have hg1 : ContDiffAt ℝ 2 (deriv g) 0 := hg.derivWithin (m := 2) (by norm_num)
  have hg2 : ContDiffAt ℝ 1 (deriv (deriv g)) 0 :=
    hg1.derivWithin (m := 1) (by norm_num)
  have hlocal : ∀ᶠ x in nhds (0 : ℝ), ContDiffAt ℝ 2 f x :=
    (hf.of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)).eventually (by norm_num)
  have heq : (fun x ↦ deriv (deriv g) (Real.sinh x)) =ᶠ[nhds 0]
      (fun x ↦ (deriv (deriv f) x - deriv f x *
        (Real.sinh x / Real.cosh x)) / Real.cosh x ^ 2) := by
    filter_upwards [hlocal] with x hx
    exact second_deriv_comp_arsinh_at_sinh hx
  have hleft : HasDerivAt (fun x ↦ deriv (deriv g) (Real.sinh x))
      (deriv (deriv (deriv g)) 0) 0 := by
    have hdg : HasDerivAt (deriv (deriv g))
        (deriv (deriv (deriv g)) 0) (Real.sinh 0) := by
      simpa using (hg2.differentiableAt (by norm_num)).hasDerivAt
    convert! hdg.comp 0 (Real.hasDerivAt_sinh 0) using 1
    simp
  have hratio : HasDerivAt (fun x : ℝ ↦ Real.sinh x / Real.cosh x) 1 0 := by
    convert! (Real.hasDerivAt_sinh 0).div (Real.hasDerivAt_cosh 0) (by norm_num) using 1
    simp
  have hden : HasDerivAt (fun x : ℝ ↦ Real.cosh x ^ 2) 0 0 := by
    convert! (Real.hasDerivAt_cosh 0).pow 2 using 1
    simp
  have hright : HasDerivAt
      (fun x ↦ (deriv (deriv f) x - deriv f x *
        (Real.sinh x / Real.cosh x)) / Real.cosh x ^ 2)
      (deriv (deriv (deriv f)) 0 - deriv f 0) 0 := by
    convert! ((hf2.differentiableAt (by norm_num)).hasDerivAt.sub
      ((hf1.differentiableAt (by norm_num)).hasDerivAt.mul hratio)).div hden
        (by norm_num) using 1
    simp
  exact hleft.unique (hright.congr_of_eventuallyEq heq)

end PDE.Calculus
