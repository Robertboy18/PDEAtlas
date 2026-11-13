/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.CanonicalForm2D.Chart

/-!
# Canonical form of the full linear equation

For locally C² principal coefficients, strict hyperbolicity constructs a C² chart
in which the principal part is a nonzero mixed derivative. Dividing by that
coefficient gives `wξη + β₁ wξ + β₂ wη + γ w`. Here `w = u ∘ e.symm`, and the
drift includes the original principal operator applied to the coordinate functions.
The identity is proved for every original C² function; the equation equivalence
then follows for arbitrary forcing.

`exists_canonical_equation` is the first canonical form (95) of Evans, §7.2.5: in the chart
the equation (82) becomes `w_{y₁y₂} + β₁ w_{y₁} + β₂ w_{y₂} + γ w = 0` after division by the
mixed coefficient of (94), and the same holds with a right-hand side.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.2.5, equations (82)-(87), (94) and (95).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace Hyperbolic.CanonicalForm2D

/-- The normalized mixed canonical operator in the new variables. The coefficients
are evaluated at the inverse chart, and include all first- and zeroth-order terms. -/
def canonicalMixedOperator
    (A : ℝ^2 → PrincipalPart) (b : ℝ^2 → ℝ^2) (c : ℝ^2 → ℝ)
    (e : OpenPartialHomeomorph ℝ^2 ℝ^2) (w : ℝ^2 → ℝ) (z : ℝ^2) : ℝ :=
  (∂[0] (∂[1] w)) z +
    transformedDrift A b e (e.symm z) 0 /
        (2 * (transformedPrincipal A e (e.symm z)).a12) * (∂[0] w) z +
    transformedDrift A b e (e.symm z) 1 /
        (2 * (transformedPrincipal A e (e.symm z)).a12) * (∂[1] w) z +
    c (e.symm z) / (2 * (transformedPrincipal A e (e.symm z)).a12) * w z

/-- The change of an arbitrary original C² function to characteristic
variables transforms the complete differential operator. -/
theorem linearOperator_in_characteristic_chart (A : ℝ^2 → PrincipalPart) (b : ℝ^2 → ℝ^2)
    (c : ℝ^2 → ℝ) (e : OpenPartialHomeomorph ℝ^2 ℝ^2) {y : ℝ^2} (hy : y ∈ e.source)
    (he : ContDiffAt ℝ 2 e y) (hinv : ContDiffAt ℝ 2 e.symm (e y))
    (h₀ : (transformedPrincipal A e y).a11 = 0) (h₁ : (transformedPrincipal A e y).a22 = 0)
    (u : ℝ^2 → ℝ) (hu : ContDiffAt ℝ 2 u y) :
    linearOperator A b c u y = 2 * (transformedPrincipal A e y).a12 *
      (∂[0] (∂[1] (u ∘ e.symm))) (e y) + transformedDrift A b e y 0 * (∂[0] (u ∘ e.symm)) (e y) +
      transformedDrift A b e y 1 * (∂[1] (u ∘ e.symm)) (e y) + c y * u y := by
  have hu' : ContDiffAt ℝ 2 u (e.symm (e y)) := by
    simpa only [e.left_inv hy] using hu
  have hw : ContDiffAt ℝ 2 (u ∘ e.symm) (e y) := hu'.comp _ hinv
  have hlocal : (u ∘ e.symm) ∘ e =ᶠ[nhds y] u := by
    filter_upwards [e.eventually_left_inverse hy] with z hz using congrArg u hz
  rw [linearOperator_congr_of_eventuallyEq A b c hlocal.symm,
    linearOperator_comp_characteristic A b c (u ∘ e.symm) e y hw he h₀ h₁]
  simp only [Function.comp_apply, e.left_inv hy]

/-- Normalization is legitimate wherever the transformed mixed coefficient is nonzero. -/
theorem canonicalMixedOperator_eq (A : ℝ^2 → PrincipalPart) (b : ℝ^2 → ℝ^2) (c : ℝ^2 → ℝ)
    (e : OpenPartialHomeomorph ℝ^2 ℝ^2) {y : ℝ^2} (hy : y ∈ e.source) (he : ContDiffAt ℝ 2 e y)
    (hinv : ContDiffAt ℝ 2 e.symm (e y)) (h₀ : (transformedPrincipal A e y).a11 = 0)
    (h₁ : (transformedPrincipal A e y).a22 = 0) (hm : (transformedPrincipal A e y).a12 ≠ 0)
    (u : ℝ^2 → ℝ) (hu : ContDiffAt ℝ 2 u y) :
    canonicalMixedOperator A b c e (u ∘ e.symm) (e y) =
      linearOperator A b c u y / (2 * (transformedPrincipal A e y).a12) := by
  rw [linearOperator_in_characteristic_chart A b c e hy he hinv h₀ h₁ u hu]
  unfold canonicalMixedOperator
  simp only [e.left_inv hy, Function.comp_apply]
  field_simp

/-- Local C² principal coefficients and strict hyperbolicity construct the full
normalized canonical form, including the transformed drift and potential. -/
theorem exists_canonical_form {A : ℝ^2 → PrincipalPart} {x : ℝ^2}
    (h₁₁ : ContDiffAt ℝ 2 (fun y ↦ (A y).a11) x) (h₁₂ : ContDiffAt ℝ 2 (fun y ↦ (A y).a12) x)
    (h₂₂ : ContDiffAt ℝ 2 (fun y ↦ (A y).a22) x) (hA : (A x).IsHyperbolic) (b : ℝ^2 → ℝ^2)
    (c : ℝ^2 → ℝ) :
    ∃ e : OpenPartialHomeomorph ℝ^2 ℝ^2, x ∈ e.source ∧
      ContDiffOn ℝ 2 e e.source ∧ ContDiffOn ℝ 2 e.symm e.target ∧
      ∀ y ∈ e.source, (transformedPrincipal A e y).a11 = 0 ∧
        (transformedPrincipal A e y).a22 = 0 ∧
        (transformedPrincipal A e y).a12 ≠ 0 ∧
        ∀ u : ℝ^2 → ℝ, ContDiffAt ℝ 2 u y →
          canonicalMixedOperator A b c e (u ∘ e.symm) (e y) =
            linearOperator A b c u y / (2 * (transformedPrincipal A e y).a12) := by
  obtain ⟨e, hx, he, hinv, hnull⟩ := exists_characteristic_chart h₁₁ h₁₂ h₂₂ hA
  refine ⟨e, hx, he, hinv, fun y hy ↦ ?_⟩
  obtain ⟨h₀, h₁, hm⟩ := hnull y hy
  refine ⟨h₀, h₁, hm, fun u hu ↦ ?_⟩
  exact canonicalMixedOperator_eq A b c e hy (he.contDiffAt (e.open_source.mem_nhds hy))
    (hinv.contDiffAt (e.open_target.mem_nhds (e.map_source hy))) h₀ h₁ hm u hu

/-- The constructed characteristic chart gives an equivalent canonical PDE for
every C² original function and arbitrary forcing. -/
theorem exists_canonical_equation {A : ℝ^2 → PrincipalPart} {x : ℝ^2}
    (h₁₁ : ContDiffAt ℝ 2 (fun y ↦ (A y).a11) x) (h₁₂ : ContDiffAt ℝ 2 (fun y ↦ (A y).a12) x)
    (h₂₂ : ContDiffAt ℝ 2 (fun y ↦ (A y).a22) x) (hA : (A x).IsHyperbolic) (b : ℝ^2 → ℝ^2)
    (c : ℝ^2 → ℝ) :
    ∃ e : OpenPartialHomeomorph ℝ^2 ℝ^2, x ∈ e.source ∧
      ContDiffOn ℝ 2 e e.source ∧ ContDiffOn ℝ 2 e.symm e.target ∧
      ∀ y ∈ e.source, (transformedPrincipal A e y).a12 ≠ 0 ∧
        ∀ (u f : ℝ^2 → ℝ), ContDiffAt ℝ 2 u y →
          (linearOperator A b c u y = f y ↔
            canonicalMixedOperator A b c e (u ∘ e.symm) (e y) =
              f y / (2 * (transformedPrincipal A e y).a12)) := by
  obtain ⟨e, hx, he, hinv, hform⟩ := exists_canonical_form h₁₁ h₁₂ h₂₂ hA b c
  refine ⟨e, hx, he, hinv, fun y hy ↦ ?_⟩
  obtain ⟨_, _, hm, hidentity⟩ := hform y hy
  refine ⟨hm, fun u f hu ↦ ?_⟩
  rw [hidentity u hu]
  exact (div_left_inj' (mul_ne_zero (by norm_num) hm)).symm

end Hyperbolic.CanonicalForm2D
