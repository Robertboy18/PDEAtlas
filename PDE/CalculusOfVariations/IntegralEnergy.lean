/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.IntegralLowerSemicontinuity
public import PDE.CalculusOfVariations.WeakLowerSemicontinuity
import PDE.Analysis.MeasureTheory.Lp.Superposition

/-!
# Convex integral energies on `Lᵖ`

For `1 ≤ p < ∞`, consider `J(u) = ∫ x, F x (u x) ∂μ`. Joint measurability,
almost-everywhere continuity in the dependent variable, an integrable
`p`-growth bound, and a common integrable lower bound give finite energies
and norm lower semicontinuity. Convexity of `F x` then gives lower
semicontinuity for the full weak `Lᵖ` topology.

This is the convex lower semicontinuity step of the direct method of
Evans, §8.2.1 and §8.2.2, for a density convex in its one field variable.
Pullback along a continuous linear map
`D : X →L[ℝ] Lp E p μ` gives weak lower semicontinuity of
`u ↦ ∫ x, F x (D u x) ∂μ`. Taking `D` to be a bounded weak-gradient map
gives the corresponding result on a Sobolev space.
The density depends on position and one field variable. Densities of `(x, u, Du)`
convex only in `Du` are treated in `MixedIntegralEnergy` and `ExtendedMixedIntegralEnergy`.

Canonical `Lp` representatives preserve affine combinations only almost
everywhere. The convexity proof uses these identities for each pair before
integrating. For a linear pullback, integrability is needed only on the
range of the map.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.2.1 and §8.2.2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.CalculusOfVariations

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞}

/-- A linear pullback of an almost-everywhere convex density has a convex
integral whenever the density is integrable on the range of the map.
The source can be any real module, and the map need not be continuous. -/
theorem convexOn_integral_Lp_comp
    {X : Type*} [AddCommMonoid X] [Module ℝ X]
    (D : X →ₗ[ℝ] Lp E p μ)
    {F : α → E → ℝ}
    (hconvex : ∀ᵐ x ∂μ, ConvexOn ℝ univ (F x))
    (hFint : ∀ u : X, Integrable (fun x ↦ F x (D u x)) μ) :
    ConvexOn ℝ univ (fun u : X ↦ ∫ x, F x (D u x) ∂μ) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  calc
    (∫ x, F x (D (a • u + b • v) x) ∂μ) ≤
        ∫ x, a • F x (D u x) + b • F x (D v x) ∂μ := by
      refine integral_mono_ae (hFint _) (((hFint u).smul a).add
        ((hFint v).smul b)) ?_
      rw [map_add, map_smul, map_smul]
      filter_upwards [hconvex, Lp.coeFn_add (a • D u) (b • D v),
        Lp.coeFn_smul a (D u), Lp.coeFn_smul b (D v)] with x hx hadd hau hbv
      rw [hadd, Pi.add_apply, hau, hbv, Pi.smul_apply, Pi.smul_apply]
      exact hx.2 (mem_univ _) (mem_univ _) ha hb hab
    _ = a • (∫ x, F x (D u x) ∂μ) + b • (∫ x, F x (D v x) ∂μ) := by
      simpa only [Pi.smul_apply, integral_smul] using
        (integral_add ((hFint u).smul a) ((hFint v).smul b))

/-- Almost-everywhere convexity of the density implies convexity of its
integral on `Lᵖ`, provided every density is integrable. No topology or
continuity of the energy is needed for this step. -/
theorem convexOn_integral_Lp
    {F : α → E → ℝ}
    (hconvex : ∀ᵐ x ∂μ, ConvexOn ℝ univ (F x))
    (hFint : ∀ u : Lp E p μ, Integrable (fun x ↦ F x (u x)) μ) :
    ConvexOn ℝ univ (fun u : Lp E p μ ↦ ∫ x, F x (u x) ∂μ) := by
  exact convexOn_integral_Lp_comp LinearMap.id hconvex hFint

/-- A continuous convex density with an integrable `p`-growth bound and a
common integrable lower bound defines a weakly lower-semicontinuous integral
on `Lᵖ`, for `1 ≤ p < ∞`. Integrability and strong lower semicontinuity are
proved from these hypotheses. Neither reflexivity nor finite measure is
required. -/
theorem lowerSemicontinuous_weakSpace_integral_Lp_of_growth
    [Fact (1 ≤ p)] [MeasurableSpace E] [BorelSpace E]
    (hp_top : p ≠ ∞) {F : α → E → ℝ} {a b : α → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F))
    (hcont : ∀ᵐ x ∂μ, Continuous (F x))
    (hconvex : ∀ᵐ x ∂μ, ConvexOn ℝ univ (F x))
    (ha : Integrable a μ) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ z, b x ≤ F x z)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, |F x z| ≤ a x + C * ‖z‖ ^ p.toReal) :
    LowerSemicontinuous
      (fun w : WeakSpace ℝ (Lp E p μ) ↦
        ∫ x, F x (((toWeakSpace ℝ (Lp E p μ)).symm w) x) ∂μ) := by
  apply lowerSemicontinuous_weakSpace_of_convex
    (fun u : Lp E p μ ↦ ∫ x, F x (u x) ∂μ) ?_
    (lowerSemicontinuous_integral_Lp_of_growth hp_top hF hcont ha hb hlower hgrowth)
  apply convexOn_integral_Lp hconvex
  intro u
  exact (Lp.memLp u).integrable_comp_of_norm_rpow_le
    (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp_top hF ha
    (by simpa only [Real.norm_eq_abs] using hgrowth)

/-- Pulling a convex integral energy back along a continuous linear map gives
a weakly lower-semicontinuous energy on the source space. In particular, when
`D` is the weak-gradient map, this proves weak lower semicontinuity of
`u ↦ ∫ x, F x (Du x) ∂μ`. The growth bound ensures integrability; neither the
source nor the range needs to be complete or a Hilbert space. -/
theorem lowerSemicontinuous_weakSpace_integral_Lp_comp_of_growth
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fact (1 ≤ p)] [MeasurableSpace E] [BorelSpace E]
    (D : X →L[ℝ] Lp E p μ)
    (hp_top : p ≠ ∞) {F : α → E → ℝ} {a b : α → ℝ} {C : ℝ}
    (hF : Measurable (Function.uncurry F))
    (hcont : ∀ᵐ x ∂μ, Continuous (F x))
    (hconvex : ∀ᵐ x ∂μ, ConvexOn ℝ univ (F x))
    (ha : Integrable a μ) (hb : Integrable b μ)
    (hlower : ∀ᵐ x ∂μ, ∀ z, b x ≤ F x z)
    (hgrowth : ∀ᵐ x ∂μ, ∀ z, |F x z| ≤ a x + C * ‖z‖ ^ p.toReal) :
    LowerSemicontinuous
      (fun w : WeakSpace ℝ X ↦
        ∫ x, F x (D ((toWeakSpace ℝ X).symm w) x) ∂μ) := by
  exact (lowerSemicontinuous_weakSpace_integral_Lp_of_growth
    hp_top hF hcont hconvex ha hb hlower hgrowth).comp (WeakSpace.map D).continuous

end PDE.CalculusOfVariations
