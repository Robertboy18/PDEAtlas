/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.CanonicalForm2D

/-!
# Transformation of a full two-variable linear operator

The second-order chain rule transforms both the principal part and the lower-order
terms. In particular, second derivatives of the coordinate functions contribute to
the transformed drift. These formulas apply to C² coordinate germs and C² functions.
-/

@[expose] public noncomputable section

namespace Hyperbolic.CanonicalForm2D

/-- The full nondivergence-form linear operator with a symmetric principal part. -/
def linearOperator (A : ℝ^2 → PrincipalPart) (b : ℝ^2 → ℝ^2) (c : ℝ^2 → ℝ)
    (u : ℝ^2 → ℝ) (x : ℝ^2) : ℝ :=
  principalExpression (A x).a11 (A x).a12 (A x).a22
      ((∂[0] (∂[0] u)) x) ((∂[0] (∂[1] u)) x) ((∂[1] (∂[1] u)) x) +
    b x 0 * (∂[0] u) x + b x 1 * (∂[1] u) x + c x * u x

/-- The principal part transformed by the coordinate covectors. Its argument
is the original spatial point; the transformed function is evaluated at `Φ x`. -/
def transformedPrincipal (A : ℝ^2 → PrincipalPart) (Φ : ℝ^2 → ℝ^2)
    (x : ℝ^2) : PrincipalPart where
  a11 := (A x).quadratic ((∂[0] (fun y ↦ Φ y 0)) x) ((∂[1] (fun y ↦ Φ y 0)) x)
  a12 := (A x).mixed ((∂[0] (fun y ↦ Φ y 0)) x) ((∂[1] (fun y ↦ Φ y 0)) x)
    ((∂[0] (fun y ↦ Φ y 1)) x) ((∂[1] (fun y ↦ Φ y 1)) x)
  a22 := (A x).quadratic ((∂[0] (fun y ↦ Φ y 1)) x) ((∂[1] (fun y ↦ Φ y 1)) x)

/-- The transformed drift includes the principal operator applied to each
coordinate function, in addition to the transported original drift. -/
def transformedDrift (A : ℝ^2 → PrincipalPart) (b : ℝ^2 → ℝ^2)
    (Φ : ℝ^2 → ℝ^2) (x : ℝ^2) (j : Fin 2) : ℝ :=
  linearOperator A b (fun _ ↦ 0) (fun y ↦ Φ y j) x

/-- The differential operator depends only on the germ of its argument. -/
theorem linearOperator_congr_of_eventuallyEq (A : ℝ^2 → PrincipalPart) (b : ℝ^2 → ℝ^2) (c : ℝ^2 → ℝ)
    {u v : ℝ^2 → ℝ} {x : ℝ^2} (h : u =ᶠ[nhds x] v) :
    linearOperator A b c u x = linearOperator A b c v x := by
  unfold linearOperator
  rw [((h.partialDeriv 0).partialDeriv 0).eq_of_nhds,
    ((h.partialDeriv 1).partialDeriv 0).eq_of_nhds, ((h.partialDeriv 1).partialDeriv 1).eq_of_nhds,
    (h.partialDeriv 0).eq_of_nhds, (h.partialDeriv 1).eq_of_nhds, h.eq_of_nhds]

/-- The second-order chain rule for the complete linear equation. -/
theorem linearOperator_comp (A : ℝ^2 → PrincipalPart) (b : ℝ^2 → ℝ^2) (c : ℝ^2 → ℝ) (w : ℝ^2 → ℝ)
    (Φ : ℝ^2 → ℝ^2) (x : ℝ^2) (hw : ContDiffAt ℝ 2 w (Φ x)) (hΦ : ContDiffAt ℝ 2 Φ x) :
    linearOperator A b c (w ∘ Φ) x =
      principalExpression (transformedPrincipal A Φ x).a11
        (transformedPrincipal A Φ x).a12 (transformedPrincipal A Φ x).a22
        ((∂[0] (∂[0] w)) (Φ x)) ((∂[0] (∂[1] w)) (Φ x))
        ((∂[1] (∂[1] w)) (Φ x)) +
      transformedDrift A b Φ x 0 * (∂[0] w) (Φ x) +
      transformedDrift A b Φ x 1 * (∂[1] w) (Φ x) + c x * w (Φ x) := by
  have hsecond (i j : Fin 2) := PDE.partialDeriv_partialDeriv_comp_at i j w Φ x hw hΦ
  have hfirst (i : Fin 2) := PDE.partialDeriv_comp i w Φ x
    (hw.differentiableAt (by norm_num)) (hΦ.differentiableAt (by norm_num))
  have hcomm := PDE.partialDeriv_partialDeriv_comm_at 0 1 hw
  unfold transformedDrift linearOperator transformedPrincipal
  simp only [principalExpression, PrincipalPart.quadratic, PrincipalPart.mixed,
    Function.comp_def, hsecond, hfirst, Fin.sum_univ_two, zero_mul, add_zero]
  rw [← hcomm]
  ring

/-- Characteristic coordinates eliminate both pure derivatives from the complete
equation; their second derivatives remain in the transformed drift. -/
theorem linearOperator_comp_characteristic (A : ℝ^2 → PrincipalPart) (b : ℝ^2 → ℝ^2) (c : ℝ^2 → ℝ)
    (w : ℝ^2 → ℝ) (Φ : ℝ^2 → ℝ^2) (x : ℝ^2) (hw : ContDiffAt ℝ 2 w (Φ x)) (hΦ : ContDiffAt ℝ 2 Φ x)
    (h₀ : (transformedPrincipal A Φ x).a11 = 0) (h₁ : (transformedPrincipal A Φ x).a22 = 0) :
    linearOperator A b c (w ∘ Φ) x = 2 * (transformedPrincipal A Φ x).a12 * (∂[0] (∂[1] w)) (Φ x) +
      transformedDrift A b Φ x 0 * (∂[0] w) (Φ x) + transformedDrift A b Φ x 1 * (∂[1] w) (Φ x) +
      c x * w (Φ x) := by
  rw [linearOperator_comp A b c w Φ x hw hΦ, h₀, h₁, principalExpression_zero_pure]

end Hyperbolic.CanonicalForm2D
