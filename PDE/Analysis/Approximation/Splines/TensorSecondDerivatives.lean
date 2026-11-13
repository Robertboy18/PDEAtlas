/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Approximation.Splines.SecondDerivatives

/-!
# Partial second derivatives of finite tensor sums

Differentiation in one coordinate preserves the finite dependence on the other
coordinate. Continuity of a transverse second derivative therefore only needs
continuity of the undifferentiated factors.
-/

@[expose] public section

namespace CAS.Splines

open Filter

/-- A partial second derivative of a separable finite sum is continuous in the
undifferentiated variable whenever its corresponding factors are continuous. -/
theorem continuousAt_partial_second_deriv_sum {ι : Type*} (u : Finset ι)
    (f g : ι → ℝ → ℝ) (x z : ℝ)
    (hc : ∀ i ∈ u, ContinuousAt (f i) x)
    (hfirst : ∀ᶠ y in nhds z, ∀ i ∈ u, DifferentiableAt ℝ (g i) y)
    (hsecond : ∀ i ∈ u, DifferentiableAt ℝ (deriv (g i)) z) :
    ContinuousAt (fun r ↦ deriv (deriv (fun y ↦ ∑ i ∈ u, f i r * g i y)) z) x := by
  have hid (r : ℝ) : deriv (deriv (fun y ↦ ∑ i ∈ u, f i r * g i y)) z =
      ∑ i ∈ u, f i r * deriv (deriv (g i)) z :=
    (hasDerivAt_deriv_weighted_sum u g (fun i ↦ f i r)
      (fun i ↦ deriv (deriv (g i)) z) z hfirst
      (fun i hi ↦ (hsecond i hi).hasDerivAt)).deriv
  simp_rw [hid]
  exact tendsto_finsetSum u (fun i hi ↦ (hc i hi).mul continuousAt_const)

/-- The transverse second derivative of a tensor spline is continuous in its
radial parameter; the axial factors need second differentiability only at the
fixed axial evaluation point. -/
theorem continuousAt_partial_second_deriv_tensor {ι κ : Type*}
    (u : Finset ι) (v : Finset κ) (f : ι → ℝ → ℝ) (g : κ → ℝ → ℝ)
    (c : ι → κ → ℝ) (x z : ℝ)
    (hc : ∀ i ∈ u, ContinuousAt (f i) x)
    (hfirst : ∀ᶠ y in nhds z, ∀ j ∈ v, DifferentiableAt ℝ (g j) y)
    (hsecond : ∀ j ∈ v, DifferentiableAt ℝ (deriv (g j)) z) :
    ContinuousAt (fun r ↦ deriv (deriv (fun y ↦
      ∑ i ∈ u, f i r * ∑ j ∈ v, c i j * g j y)) z) x := by
  apply continuousAt_partial_second_deriv_sum u f
    (fun i y ↦ ∑ j ∈ v, c i j * g j y) x z hc
  · filter_upwards [hfirst] with y hy
    intro i _
    exact (HasDerivAt.fun_sum (fun j hj ↦
      (hy j hj).hasDerivAt.const_mul (c i j))).differentiableAt
  · intro i _
    exact (hasDerivAt_deriv_weighted_sum v g (c i)
      (fun j ↦ deriv (deriv (g j)) z) z hfirst
      (fun j hj ↦ (hsecond j hj).hasDerivAt)).differentiableAt

end CAS.Splines
