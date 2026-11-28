/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.GradientRegularization
public import PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.LowerSemicontinuity
import PDE.Analysis.Convex.Function.JointContinuity
import PDE.Analysis.WeakSequentialBoundedness
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Lower semicontinuity for densities convex in the gradient

## Motivation

Is `∫ F(x, u, Du)` lower semicontinuous under strong convergence of `u` and weak convergence of
`Du` when `F` is only measurable in `x`, continuous in `u` and convex in `Du`, with no
derivative in `Du` at all?

## The idea

Yes, on a finite measure space, for a gradient variable in a finite-dimensional space and a
density bounded below by a function of `x`. A density that is continuous in `u` for each `Du`
and convex in `Du` is continuous in the pair `(u, Du)`
(`PDE.Analysis.continuous_uncurry_of_convexOn`), so this is the class of Carathéodory
integrands that are convex in the gradient. Replace `F` by its Moreau regularization `F_λ` in
the gradient variable (`moreauDensity`). It is convex and differentiable in the gradient, and it
and its gradient are continuous in the value, so the theorem for differentiable densities
applies to it. Since `F_λ ≤ F`,

`∫ F_λ(x, u, Du) ≤ liminf ∫ F_λ(x, u_j, Du_j) ≤ liminf ∫ F(x, u_j, Du_j)`.

As `λ` decreases to `0`, `F_λ` increases to `F`, and the monotone convergence theorem turns the
left side into `∫ F(x, u, Du)`. The integrals are extended ones of `F - b` for the lower bound
`b`, and may be infinite; no upper growth bound is used.

## Main results

* `lintegral_le_liminf_of_tendsto_ae_weak_of_continuous_convex_gradient` (all densities that
  are jointly measurable, continuous in `u` for each `Du` and convex in `Du` for almost every
  `x`, and bounded below by a measurable function of `x`): lower semicontinuity under
  almost-everywhere convergence of the values and weak `Lᵖ` convergence of the gradients. A
  weakly convergent sequence is bounded, so no bound is assumed.

## Relations

* The theorem is proved from `lintegral_le_liminf_of_tendsto_ae_weak_of_convex_gradient`, the
  theorem for densities differentiable in the gradient, applied to `moreauDensity`. That
  theorem allows a gradient variable in any second countable inner product space and needs the
  lower bound only at the limit; it stays the tool for densities on lifted variables.
* Under strong `Lʳ` convergence of the values the same inequality holds:
  `le_liminf_of_tendsto_Lp_of_forall_subseq_ae` reduces it to subsequences that converge
  almost everywhere. There is no second statement for this case.
* The Sobolev theorems `lintegral_le_liminf_of_tendsto_weak_wkp_of_c1Domain`,
  `lintegral_le_liminf_of_tendsto_weak_vectorWkp_of_c1Domain` and the existence theorems of
  `Dirichlet` and `Systems.Dirichlet` apply the theorem in this way.

## What stays open

A lower bound of the form `⟪a(x), Du⟫ + b(x)` with `a` in the conjugate space, and a gradient
variable in an infinite-dimensional space.

## References

* The statement, with the more general lower bound just mentioned, is the theorem on
  sequential weak lower semicontinuity of integrals in
  <https://en.wikipedia.org/wiki/Direct_method_in_the_calculus_of_variations> (read 27 November
  2026), which refers to B. Dacorogna, *Direct Methods in the Calculus of Variations*, Springer,
  1989, pp. 74-79. The book was not opened; the proof here, by Moreau regularization, is ours.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace PDE.CalculusOfVariations

variable {α E H : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]

omit [BorelSpace E] in
/-- On a finite measure space, an integral energy whose density is continuous in the value for
each gradient, convex in the gradient and bounded below by a function `b` of the point is lower
semicontinuous under almost-everywhere convergence of the values and weak `Lᵖ` convergence of
the gradients, for a finite conjugate exponent `q`. The density need not be
differentiable. The gradient variable is finite-dimensional. The extended integrals of `F - b`
may be infinite.

The proof applies the theorem for differentiable densities to the Moreau regularization of the
density in the gradient variable, which lies below the density, and lets the parameter decrease
to zero by monotone convergence. -/
theorem lintegral_le_liminf_of_tendsto_ae_weak_of_continuous_convex_gradient
    (hq_top : q ≠ ∞)
    {F : α → E × H → ℝ} {b : α → ℝ}
    (hF : Measurable (Function.uncurry F)) (hb : Measurable b)
    (hFcont : ∀ᵐ x ∂μ, ∀ z : H, Continuous (fun s : E ↦ F x (s, z)))
    (hconvex : ∀ᵐ x ∂μ, ∀ s : E, ConvexOn ℝ univ (fun z : H ↦ F x (s, z)))
    (hlower : ∀ᵐ x ∂μ, ∀ z, b x ≤ F x z)
    {u : ℕ → α → E} {uLimit : α → E}
    (hu_meas : ∀ j, Measurable (u j)) (huLimit_meas : Measurable uLimit)
    (hu : ∀ᵐ x ∂μ, Tendsto (fun j ↦ u j x) atTop (𝓝 (uLimit x)))
    {g : ℕ → Lp H p μ} {gLimit : Lp H p μ}
    (hg : Tendsto (fun j ↦ toWeakSpace ℝ (Lp H p μ) (g j)) atTop
      (𝓝 (toWeakSpace ℝ (Lp H p μ) gLimit))) :
    (∫⁻ x, ENNReal.ofReal (F x (uLimit x, gLimit x) - b x) ∂μ) ≤
      liminf (fun j ↦ ∫⁻ x, ENNReal.ofReal (F x (u j x, g j x) - b x) ∂μ) atTop := by
  -- a weakly convergent sequence is bounded
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp
    (PDE.Analysis.isBounded_range_of_tendsto_weak hg)
  have hgR (j : ℕ) : ‖g j‖ ≤ R := hR _ (mem_range_self j)
  -- continuity in the value and convexity in the gradient give joint continuity
  have hFjoint : ∀ᵐ x ∂μ, Continuous (F x) := by
    filter_upwards [hFcont, hconvex] with x hc hv
    exact PDE.Analysis.continuous_uncurry_of_convexOn (G := fun s z ↦ F x (s, z)) hc hv
  set lam : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1) with hlam
  have hpos (n : ℕ) : 0 < lam n := by positivity
  have hzero : Tendsto lam atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  -- the regularized densities are below the density, so each of them gives a lower bound
  have hstep (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal (moreauDensity F (lam n) x (uLimit x, gLimit x) - b x) ∂μ) ≤
        liminf (fun j ↦ ∫⁻ x, ENNReal.ofReal (F x (u j x, g j x) - b x) ∂μ) atTop := by
    have h := lintegral_le_liminf_of_tendsto_ae_weak_of_convex_gradient hq_top
      (F := moreauDensity F (lam n)) (D := moreauDensityGradient F (lam n)) (b := b)
      (measurable_moreauDensity hF _) (measurable_moreauDensityGradient hF _) hb
      (by
        filter_upwards [hFjoint, hconvex, hlower] with x hc hv hl z
        exact continuous_moreauDensity hc hv hl (hpos n) z)
      (by
        filter_upwards [hFjoint, hconvex, hlower] with x hc hv hl z
        exact continuous_moreauDensityGradient hc hv hl (hpos n) z)
      (by
        filter_upwards [hFjoint, hconvex, hlower] with x hc hv hl s
        exact convexOn_moreauDensity hc hv hl (hpos n) s)
      (by
        filter_upwards [hFjoint, hconvex, hlower] with x hc hv hl s z
        exact hasFDerivAt_moreauDensity hc hv hl (hpos n) s z)
      hu_meas huLimit_meas hu hg
      (by
        filter_upwards [hFjoint, hconvex, hlower] with x hc hv hl
        exact le_moreauDensity hc hv hl (hpos n) _ _)
      R hgR
    refine h.trans (liminf_le_liminf (Eventually.of_forall fun j ↦ lintegral_mono_ae ?_))
    filter_upwards [hFjoint, hconvex, hlower] with x hc hv hl
    exact ENNReal.ofReal_le_ofReal
      (sub_le_sub_right (moreauDensity_le hc hv hl (hpos n) _ _) _)
  -- the regularized densities increase to the density
  have hmeas (n : ℕ) : AEMeasurable
      (fun x ↦ ENNReal.ofReal (moreauDensity F (lam n) x (uLimit x, gLimit x) - b x)) μ :=
    (ENNReal.measurable_ofReal.comp (((measurable_moreauDensity hF (lam n)).comp
      (measurable_id.prodMk (huLimit_meas.prodMk
        (Lp.stronglyMeasurable gLimit).measurable))).sub hb)).aemeasurable
  have hmono : ∀ᵐ x ∂μ, Monotone fun n ↦
      ENNReal.ofReal (moreauDensity F (lam n) x (uLimit x, gLimit x) - b x) := by
    filter_upwards [hFjoint, hconvex, hlower] with x hc hv hl
    intro n m hnm
    have hle : lam m ≤ lam n :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hnm)
    exact ENNReal.ofReal_le_ofReal
      (sub_le_sub_right (moreauDensity_antitone hc hv hl (hpos n) (hpos m) hle _ _) _)
  have htend : ∀ᵐ x ∂μ, Tendsto (fun n ↦
      ENNReal.ofReal (moreauDensity F (lam n) x (uLimit x, gLimit x) - b x)) atTop
      (𝓝 (ENNReal.ofReal (F x (uLimit x, gLimit x) - b x))) := by
    filter_upwards [hFjoint, hconvex, hlower] with x hc hv hl
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((tendsto_moreauDensity hc hv hl hpos hzero _ _).sub_const _)
  exact le_of_tendsto' (lintegral_tendsto_of_tendsto_of_monotone hmeas hmono htend) hstep

end PDE.CalculusOfVariations
