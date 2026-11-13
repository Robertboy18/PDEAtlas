/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.ClassicalDensity
public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.Systems.Functional

/-!
# Densities restricted to the determinant graph

A density on independent matrix and scalar variables defines a Sobolev
density by evaluating the scalar at the determinant. Its energy is the signed
`vectorWkpIntegral`.

A lower bound only on this graph makes the negative part finite. The exact
constant-shift identity retains positive infinite energies and arbitrary signed
lower bounds, including on empty domains.

Reading `F` as `F(P, r, z, x)`, `determinantDensity F` is the Lagrangian
`L(P, z, x) = F(P, det P, z, x)` of Evans, §8.2.4(b), (51). With the convexity (52) in `(P, r)`
it is polyconvex, the setting of Theorem 8 there.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.4(b), (51)-(52) and Theorem 8 (Lower
  semicontinuity of polyconvex functionals), p. 478.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev

namespace PDE.CalculusOfVariations

/-- Restrict an independent matrix–scalar density to the determinant graph.
The gradient argument uses row-major Euclidean coordinates. -/
def determinantDensity {n : ℕ}
    (F : (ℝ^n × ℝ^n) × (Matrix (Fin n) (Fin n) ℝ × ℝ) → ℝ) :
    ℝ^n → ℝ^n × ℝ^(n * n) → ℝ :=
  fun x z ↦ F ((x, z.1),
    (Matrix.euclideanEquiv.symm z.2, (Matrix.euclideanEquiv.symm z.2).det))

/-- Continuous graph densities evaluated on Sobolev fields are measurable. -/
theorem aestronglyMeasurable_determinantDensity
    {n : ℕ} {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω)
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : (ℝ^n × ℝ^n) × (Matrix (Fin n) (Fin n) ℝ × ℝ) → ℝ}
    (hF : ContinuousOn F ((Ω ×ˢ univ) ×ˢ univ))
    (u : Fin n → W^{1,p}(Ω)) :
    AEStronglyMeasurable (fun x ↦ determinantDensity F x
      (vectorWkpValueCLM u x, ∇ u x)) (domainMeasure n Ω) := by
  have hC := (Matrix.euclideanEquiv (m := n) (n := n)).symm.continuous
  have hF' : ContinuousOn
      (fun t : (ℝ^n × ℝ^n) × ℝ^(n * n) ↦
        F (t.1, (Matrix.euclideanEquiv.symm t.2, (Matrix.euclideanEquiv.symm t.2).det)))
      ((Ω ×ˢ univ) ×ˢ univ) :=
    hF.comp (continuous_fst.prodMk
      ((hC.comp continuous_snd).prodMk (hC.comp continuous_snd).matrix_det)).continuousOn
      (fun _ ht ↦ ⟨ht.1, mem_univ _⟩)
  exact aestronglyMeasurable_classicalDensity hΩ hF'
    (Lp.aestronglyMeasurable _).aemeasurable (Lp.aestronglyMeasurable _).aemeasurable
    (ae_restrict_mem hΩ)

/-- A graph-only lower bound makes the negative-part integral finite.
No bound is required at independent scalar arguments. -/
theorem lintegral_neg_determinantDensity_lt_top
    {n : ℕ} {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (domainMeasure n Ω)] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : (ℝ^n × ℝ^n) × (Matrix (Fin n) (Fin n) ℝ × ℝ) → ℝ}
    {β : ℝ} (hlower : ∀ x ∈ Ω, ∀ s P, -β ≤ F ((x, s), (P, P.det)))
    (u : Fin n → W^{1,p}(Ω)) :
    (∫⁻ x, ENNReal.ofReal (-determinantDensity F x
      (vectorWkpValueCLM u x, ∇ u x)) ∂domainMeasure n Ω) < ∞ := by
  apply PDE.Analysis.lintegral_neg_part_lt_top_of_ae_lower_bound (integrable_const β)
  filter_upwards [ae_restrict_mem hΩ] with x hx
  exact hlower x hx _ _

/-- The original signed energy equals its nonnegative shift minus `β |Ω|`,
including when the positive part is infinite. -/
theorem vectorWkpIntegral_determinantDensity_eq_lIntegral_sub
    {n : ℕ} {Ω : Set (ℝ^n)} (hΩ : MeasurableSet Ω)
    [IsFiniteMeasure (domainMeasure n Ω)] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : (ℝ^n × ℝ^n) × (Matrix (Fin n) (Fin n) ℝ × ℝ) → ℝ}
    (hF : ContinuousOn F ((Ω ×ˢ univ) ×ˢ univ))
    {β : ℝ} (hlower : ∀ x ∈ Ω, ∀ s P, -β ≤ F ((x, s), (P, P.det)))
    (u : Fin n → W^{1,p}(Ω)) :
    vectorWkpIntegral (determinantDensity F) u =
      (vectorWkpLIntegral (determinantDensity F) (fun _ ↦ β) u : EReal) -
        ((β * (domainMeasure n Ω).real univ : ℝ) : EReal) := by
  apply PDE.Analysis.lowerBoundedIntegral_eq_lintegral_add_const_sub
    (aestronglyMeasurable_determinantDensity hΩ hF u)
  filter_upwards [ae_restrict_mem hΩ] with x hx
  exact hlower x hx _ _

end PDE.CalculusOfVariations
