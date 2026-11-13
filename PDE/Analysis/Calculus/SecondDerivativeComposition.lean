/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivatives under smooth changes of coordinates

Local differentiability hypotheses suffice for first-derivative continuity and
the second-order chain rule.
The statements apply to smooth coordinate changes without assumptions on
the outer function away from the base point. Along a curve in a normed space, a map that is
`C²` at one point of the curve has the second derivative `D²F (c', c') + DF c''` there.
-/

@[expose] public section

namespace PDE.Calculus

open Filter

/-- Continuity of the first derivative is preserved by a continuously
differentiable coordinate map when the outer function is differentiable locally. -/
theorem continuousAt_deriv_comp {f g : ℝ → ℝ} {x : ℝ}
    (hf : ∀ᶠ y in nhds (g x), DifferentiableAt ℝ f y)
    (hc : ContinuousAt (deriv f) (g x))
    (hg : ContDiff ℝ 1 g) :
    ContinuousAt (deriv (f ∘ g)) x := by
  have hcontinuous : ContinuousAt (fun y ↦ deriv f (g y) * deriv g y) x :=
    (hc.comp hg.continuous.continuousAt).mul hg.continuous_deriv_one.continuousAt
  apply hcontinuous.congr_of_eventuallyEq
  filter_upwards [hg.continuous.continuousAt.tendsto.eventually hf] with y hy
  exact deriv_comp y hy (hg.differentiable (by norm_num) y)

/-- The second-order chain rule with only local hypotheses on the outer function. -/
theorem hasDerivAt_deriv_comp {f g : ℝ → ℝ} {x : ℝ}
    (hf : ∀ᶠ y in nhds (g x), DifferentiableAt ℝ f y)
    (hf' : DifferentiableAt ℝ (deriv f) (g x))
    (hg : ContDiff ℝ 2 g) :
    HasDerivAt (deriv (f ∘ g))
      ((deriv (deriv f) (g x) * deriv g x) * deriv g x +
        deriv f (g x) * deriv (deriv g) x) x := by
  have hgdiff := hg.differentiable (by norm_num)
  have hformula := (hf'.hasDerivAt.comp x (hgdiff x).hasDerivAt).mul
    (hg.differentiable_deriv_two x).hasDerivAt
  apply hformula.congr_of_eventuallyEq
  filter_upwards [hg.continuous.continuousAt.tendsto.eventually hf] with y hy
  exact deriv_comp y hy (hgdiff y)

/-- Continuous first and second derivatives remain continuous to second order
under a globally twice continuously differentiable coordinate map. -/
theorem continuousAt_second_deriv_comp {f g : ℝ → ℝ} {x : ℝ}
    (hf : ∀ᶠ y in nhds (g x), DifferentiableAt ℝ f y)
    (hf' : ∀ᶠ y in nhds (g x), DifferentiableAt ℝ (deriv f) y)
    (hc : ContinuousAt (deriv f) (g x))
    (hc' : ContinuousAt (deriv (deriv f)) (g x))
    (hg : ContDiff ℝ 2 g) :
    ContinuousAt (deriv (deriv (f ∘ g))) x := by
  have hg' : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have hcontinuous : ContinuousAt (fun y ↦
      (deriv (deriv f) (g y) * deriv g y) * deriv g y +
        deriv f (g y) * deriv (deriv g) y) x :=
    (((hc'.comp hg.continuous.continuousAt).mul
      (hg.continuous_deriv (by norm_num)).continuousAt).mul
      (hg.continuous_deriv (by norm_num)).continuousAt).add
      ((hc.comp hg.continuous.continuousAt).mul hg'.continuous_deriv_one.continuousAt)
  apply hcontinuous.congr_of_eventuallyEq
  filter_upwards [hg.continuous.continuousAt.tendsto.eventually hf.eventually_nhds,
    hg.continuous.continuousAt.tendsto.eventually hf'] with y hy hy'
  exact (hasDerivAt_deriv_comp hy hy' hg).deriv

/-- The second derivative along a curve: if `f` is `C²` at `c t₀`, the curve `c` has derivative
`c' t` near `t₀` and `c'` has derivative `v` at `t₀`, then `t ↦ (f ∘ c)'(t)` has derivative
`D²f (c t₀) (c' t₀, c' t₀) + Df (c t₀) v` at `t₀`. -/
theorem hasDerivAt_deriv_comp_of_contDiffAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {c c' : ℝ → E}
    {t₀ : ℝ} {v : E} (hf : ContDiffAt ℝ 2 f (c t₀))
    (hc : ∀ᶠ t in nhds t₀, HasDerivAt c (c' t) t) (hc' : HasDerivAt c' v t₀) :
    HasDerivAt (deriv fun t ↦ f (c t))
      (fderiv ℝ (fderiv ℝ f) (c t₀) (c' t₀) (c' t₀) + fderiv ℝ f (c t₀) v) t₀ := by
  have hcont : ContinuousAt c t₀ := hc.self_of_nhds.continuousAt
  have hnear : ∀ᶠ t in nhds t₀, ContDiffAt ℝ 2 f (c t) :=
    hcont.eventually (hf.eventually (by simp))
  have heq : (deriv fun t ↦ f (c t)) =ᶠ[nhds t₀] fun t ↦ fderiv ℝ f (c t) (c' t) := by
    filter_upwards [hnear, hc] with t hft hct
    exact ((hft.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t hct).deriv
  have hD : DifferentiableAt ℝ (fderiv ℝ f) (c t₀) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact ((hD.hasFDerivAt.comp_hasDerivAt t₀ hc.self_of_nhds).clm_apply hc').congr_of_eventuallyEq
    heq

end PDE.Calculus
