/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# A measurable gradient from difference quotients

## Motivation

A function `G(a, ξ)` is measurable in the pair and, for the parameters `a` of interest,
differentiable in `ξ`. Is there a jointly measurable function that is the gradient in `ξ`
wherever the gradient exists?

## The idea

Take the difference quotients `(k + 1) (g(ξ + e_i / (k + 1)) - g(ξ))` along an orthonormal basis
`e_i` of a finite-dimensional inner product space and put
`quotientGradient g ξ = ∑ i, (limsup over k of the i-th quotient) e_i`. A `limsup` of countably
many measurable functions is measurable, so the result is measurable in every parameter of which
`g` is a measurable function. Where `g` has the gradient `v`, the quotients along `e_i` converge
to `⟪v, e_i⟫` and the sum is `v`. Nothing is claimed at the other points.

## Main results

* `quotientGradient_eq_of_hasFDerivAt` (all functions, all points of differentiability): the
  quotient gradient is the gradient.
* `measurable_quotientGradient` (all jointly measurable families): the quotient gradient is
  jointly measurable in the parameter and the point.

## Relations

* Mathlib's `measurable_fderiv_with_param` gives the measurability of the derivative for a
  family that is jointly continuous in the parameter and the point. Here the family is only
  measurable in the parameter.
* `PDE.CalculusOfVariations.moreauDensityGradient` is the quotient gradient of a regularized
  integrand, and uses both results.

## What stays open

The construction uses an orthonormal basis, so it is for finite-dimensional spaces only.
-/

@[expose] public section

noncomputable section

open Filter
open scoped Topology

namespace PDE.Analysis

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The gradient of `g` at `ξ` read off from difference quotients along the standard
orthonormal basis: the `i`-th coordinate is the `limsup` of
`(k + 1) (g(ξ + e_i / (k + 1)) - g(ξ))` over `k`. It is the gradient wherever `g` is
differentiable. -/
def quotientGradient (g : H → ℝ) (ξ : H) : H :=
  ∑ i, limsup (fun k : ℕ ↦ ((k : ℝ) + 1) *
    (g (ξ + ((k : ℝ) + 1)⁻¹ • stdOrthonormalBasis ℝ H i) - g ξ)) atTop •
      stdOrthonormalBasis ℝ H i

/-- Where `g` has the gradient `v`, the quotient gradient is `v`: the difference quotients along
a basis vector converge to the inner product of `v` with it. -/
theorem quotientGradient_eq_of_hasFDerivAt {g : H → ℝ} {ξ v : H}
    (hg : HasFDerivAt g (innerSL ℝ v) ξ) : quotientGradient g ξ = v := by
  have key (i : Fin (Module.finrank ℝ H)) :
      limsup (fun k : ℕ ↦ ((k : ℝ) + 1) *
        (g (ξ + ((k : ℝ) + 1)⁻¹ • stdOrthonormalBasis ℝ H i) - g ξ)) atTop =
        inner ℝ (stdOrthonormalBasis ℝ H i) v := by
    set e := stdOrthonormalBasis ℝ H i
    -- the derivative of `t ↦ g (ξ + t e)` at `0`
    have h1 : HasDerivAt (fun t : ℝ ↦ ξ + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add ξ
    have h2 : HasFDerivAt g (innerSL ℝ v) (ξ + (0 : ℝ) • e) := by simpa using hg
    have hline : HasDerivAt (fun t : ℝ ↦ g (ξ + t • e)) (innerSL ℝ v e) 0 :=
      HasFDerivAt.comp_hasDerivAt (l := g) (f := fun t : ℝ ↦ ξ + t • e) 0 h2 h1
    have hseq : Tendsto (fun k : ℕ ↦ ((k : ℝ) + 1)⁻¹) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k ↦ ?_⟩
      · simpa [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      · exact inv_ne_zero (by positivity)
    have hlim := hline.tendsto_slope_zero.comp hseq
    refine Tendsto.limsup_eq ?_
    rw [real_inner_comm]
    refine hlim.congr fun k ↦ ?_
    simp
  simp only [quotientGradient, key]
  exact (stdOrthonormalBasis ℝ H).sum_repr' v

/-- The quotient gradient of a jointly measurable family is jointly measurable in the parameter
and the point. -/
theorem measurable_quotientGradient {α : Type*} [MeasurableSpace α] [MeasurableSpace H]
    [BorelSpace H] {G : α → H → ℝ} (hG : Measurable (Function.uncurry G)) :
    Measurable fun p : α × H ↦ quotientGradient (G p.1) p.2 := by
  unfold quotientGradient
  refine Finset.measurable_sum _ fun i _ ↦ Measurable.smul_const ?_ _
  refine Measurable.limsup fun k ↦ ?_
  have h1 : Measurable fun p : α × H ↦
      G p.1 (p.2 + ((k : ℝ) + 1)⁻¹ • stdOrthonormalBasis ℝ H i) :=
    hG.comp (measurable_fst.prodMk (measurable_snd.add_const _))
  have h2 : Measurable fun p : α × H ↦ G p.1 p.2 := hG
  exact (h1.sub h2).const_mul _

end PDE.Analysis
