/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Calculus.Gradient.DifferenceQuotient
public import PDE.Analysis.Convex.Proximal.MoreauEnvelope
public import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Regularizing an integrand in the gradient variable

## Motivation

The lower semicontinuity theorem for `∫ F(x, u, Du)` in
`PDE.CalculusOfVariations.ExtendedMixedIntegralEnergy.LowerSemicontinuity` needs `F`
differentiable in the gradient, with a measurable derivative. How can a density that is only
continuous in `(u, Du)` and convex in `Du` be brought into its scope?

## The idea

Replace `F(x, s, ·)` by its Moreau envelope
`F_λ(x, s, ξ) = inf_η (F(x, s, η) + ‖η - ξ‖² / (2 λ))`. For a density that is continuous in
`(s, ξ)`, convex in `ξ` and bounded below at the point `x`, the envelope is convex and
differentiable in `ξ`, continuous in `s`, lies between the lower bound and `F`, increases as `λ`
decreases and tends to `F` as `λ → 0`. Its gradient in `ξ` is continuous in `s` as well.

Joint measurability in `x` is kept by two choices. The infimum is taken over a dense sequence of
`η`, so `moreauDensity` is a countable infimum of measurable functions; for a continuous
density this is the same infimum. The gradient field `moreauDensityGradient` is the limit of
difference quotients along an orthonormal basis, which is measurable and is the gradient
wherever the gradient exists. Both definitions make sense for every `x`; the properties are
proved at the points `x` where the density is continuous, convex in the gradient and bounded
below, which is almost every point in the applications.

The gradient variable ranges over a finite-dimensional real inner product space.

## Main results

All results are for all densities `F : α → E × H → ℝ` and all `λ > 0`; the pointwise ones are
at a point `x` where `F x` is continuous, convex in the second variable and bounded below.

* `measurable_moreauDensity`, `measurable_moreauDensityGradient`: joint measurability.
* `moreauDensity_eq_moreauEnvelope`: the countable infimum is the Moreau envelope.
* `le_moreauDensity`, `moreauDensity_le`, `moreauDensity_antitone`, `tendsto_moreauDensity`:
  bounds, monotonicity in `λ` and convergence to `F`.
* `convexOn_moreauDensity`, `hasFDerivAt_moreauDensity`: convexity and differentiability in the
  gradient variable, with the gradient field as derivative.
* `continuous_moreauDensity`, `continuous_moreauDensityGradient`: continuity in the value
  variable.

## Relations

* Every pointwise result is the corresponding result of
  `PDE.Analysis.Convex.Proximal.MoreauEnvelope` for the slice `η ↦ F x (s, η)`, through
  `moreauDensity_eq_moreauEnvelope` and `moreauDensityGradient_eq`.
* `PDE.CalculusOfVariations.lintegral_le_liminf_of_tendsto_ae_weak_of_continuous_convex_gradient`
  applies the differentiable theorem to `moreauDensity` and lets `λ → 0`.

## What stays open

A gradient variable in an infinite-dimensional space.
-/

@[expose] public section

noncomputable section

open Filter Set TopologicalSpace PDE.Analysis PDE.Analysis.Convex
open scoped Topology

namespace PDE.CalculusOfVariations

variable {α E H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The Moreau regularization of a density in its second variable, as an infimum over a dense
sequence: `inf_k (F x (s, η_k) + ‖η_k - ξ‖² / (2 λ))`. -/
def moreauDensity (F : α → E × H → ℝ) (lambda : ℝ) (x : α) (z : E × H) : ℝ :=
  ⨅ k : ℕ, F x (z.1, denseSeq H k) + quadraticPenalty lambda z.2 (denseSeq H k)

/-- The field of difference-quotient limits of the regularized density in its second variable.
It is defined for every density; it is the gradient where the regularized density is
differentiable (`moreauDensityGradient_eq`, `hasFDerivAt_moreauDensity`). -/
def moreauDensityGradient (F : α → E × H → ℝ) (lambda : ℝ) (x : α) (z : E × H) : H :=
  quotientGradient (fun ξ ↦ moreauDensity F lambda x (z.1, ξ)) z.2

section Measurable

variable [MeasurableSpace α] [MeasurableSpace E] [MeasurableSpace H] [BorelSpace H]
  {F : α → E × H → ℝ}

/-- The regularized density is jointly measurable when the density is. -/
theorem measurable_moreauDensity (hF : Measurable (Function.uncurry F)) (lambda : ℝ) :
    Measurable (Function.uncurry (moreauDensity F lambda)) := by
  have hpen (k : ℕ) : Continuous fun w : H ↦ quadraticPenalty lambda w (denseSeq H k) := by
    unfold quadraticPenalty
    fun_prop
  refine Measurable.iInf fun k ↦ ?_
  exact (hF.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_const))).add
    ((hpen k).measurable.comp measurable_snd.snd)

/-- The field `moreauDensityGradient` is jointly measurable when the density is. Nothing is
claimed here about its being a gradient. -/
theorem measurable_moreauDensityGradient (hF : Measurable (Function.uncurry F)) (lambda : ℝ) :
    Measurable (Function.uncurry (moreauDensityGradient F lambda)) := by
  have hG : Measurable (Function.uncurry fun (a : α × E) (ξ : H) ↦
      moreauDensity F lambda a.1 (a.2, ξ)) :=
    (measurable_moreauDensity hF lambda).comp
      (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have h := (measurable_quotientGradient hG).comp
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd :
      Measurable fun q : α × E × H ↦ ((q.1, q.2.1), q.2.2))
  unfold Function.uncurry moreauDensityGradient
  exact h

end Measurable

section Pointwise

variable [TopologicalSpace E] {F : α → E × H → ℝ} {x : α} {b lambda : ℝ}

/-- At a point where the density is continuous and bounded below, the countable infimum is the
Moreau envelope of the slice `η ↦ F x (s, η)`. -/
theorem moreauDensity_eq_moreauEnvelope (hcont : Continuous (F x)) (hlow : ∀ z, b ≤ F x z)
    (hlambda : 0 < lambda) (s : E) (ξ : H) :
    moreauDensity F lambda x (s, ξ) = moreauEnvelope (fun η ↦ F x (s, η)) lambda ξ := by
  refine (moreauEnvelope_eq_iInf_of_denseRange (denseRange_denseSeq H)
    (hcont.comp (Continuous.prodMk_right s)) ⟨b, ?_⟩).symm
  rintro _ ⟨u, rfl⟩
  have h1 := hlow (s, u)
  have h2 : 0 ≤ quadraticPenalty lambda ξ u := by
    unfold quadraticPenalty
    positivity
  change b ≤ F x (s, u) + quadraticPenalty lambda ξ u
  linarith

variable (hcont : Continuous (F x)) (hconv : ∀ s, ConvexOn ℝ univ fun ξ ↦ F x (s, ξ))
  (hlow : ∀ z, b ≤ F x z) (hlambda : 0 < lambda)

include hcont hconv hlow hlambda

/-- The regularized density lies below the density. -/
theorem moreauDensity_le (s : E) (ξ : H) : moreauDensity F lambda x (s, ξ) ≤ F x (s, ξ) := by
  rw [moreauDensity_eq_moreauEnvelope hcont hlow hlambda]
  exact moreauEnvelope_le_self (hconv s)
    (hcont.comp (Continuous.prodMk_right s)).lowerSemicontinuous hlambda ξ

/-- A lower bound of the density is a lower bound of the regularized density. -/
theorem le_moreauDensity (s : E) (ξ : H) : b ≤ moreauDensity F lambda x (s, ξ) := by
  rw [moreauDensity_eq_moreauEnvelope hcont hlow hlambda]
  exact le_moreauEnvelope (hconv s)
    (hcont.comp (Continuous.prodMk_right s)).lowerSemicontinuous hlambda
    (fun u ↦ hlow (s, u)) ξ

/-- The regularized density decreases when the parameter grows. -/
theorem moreauDensity_antitone {mu : ℝ} (hmu : 0 < mu) (hle : mu ≤ lambda) (s : E) (ξ : H) :
    moreauDensity F lambda x (s, ξ) ≤ moreauDensity F mu x (s, ξ) := by
  rw [moreauDensity_eq_moreauEnvelope hcont hlow hlambda,
    moreauDensity_eq_moreauEnvelope hcont hlow hmu]
  exact moreauEnvelope_antitone (hconv s)
    (hcont.comp (Continuous.prodMk_right s)).lowerSemicontinuous hlambda hmu hle ξ

/-- The regularized density is convex in the gradient variable. -/
theorem convexOn_moreauDensity (s : E) :
    ConvexOn ℝ univ fun ξ ↦ moreauDensity F lambda x (s, ξ) := by
  rw [show (fun ξ ↦ moreauDensity F lambda x (s, ξ)) =
    moreauEnvelope (fun η ↦ F x (s, η)) lambda from
    funext (moreauDensity_eq_moreauEnvelope hcont hlow hlambda s)]
  exact convexOn_moreauEnvelope (hconv s)
    (hcont.comp (Continuous.prodMk_right s)).lowerSemicontinuous hlambda

/-- The gradient field of the regularized density is the gradient of the Moreau envelope of the
slice. -/
theorem moreauDensityGradient_eq (s : E) (ξ : H) :
    moreauDensityGradient F lambda x (s, ξ) =
      moreauGradient (fun η ↦ F x (s, η)) (hconv s)
        (hcont.comp (Continuous.prodMk_right s)).lowerSemicontinuous lambda hlambda ξ := by
  rw [moreauDensityGradient, show (fun ξ ↦ moreauDensity F lambda x (s, ξ)) =
    moreauEnvelope (fun η ↦ F x (s, η)) lambda from
    funext (moreauDensity_eq_moreauEnvelope hcont hlow hlambda s)]
  exact quotientGradient_eq_of_hasFDerivAt (hasFDerivAt_moreauEnvelope (hconv s)
    (hcont.comp (Continuous.prodMk_right s)).lowerSemicontinuous hlambda ξ)

/-- The regularized density is differentiable in the gradient variable, and its derivative is
the inner product with the gradient field. -/
theorem hasFDerivAt_moreauDensity (s : E) (ξ : H) :
    HasFDerivAt (fun η ↦ moreauDensity F lambda x (s, η))
      (innerSL ℝ (moreauDensityGradient F lambda x (s, ξ))) ξ := by
  rw [moreauDensityGradient_eq hcont hconv hlow hlambda,
    show (fun ξ ↦ moreauDensity F lambda x (s, ξ)) =
      moreauEnvelope (fun η ↦ F x (s, η)) lambda from
      funext (moreauDensity_eq_moreauEnvelope hcont hlow hlambda s)]
  exact hasFDerivAt_moreauEnvelope (hconv s)
    (hcont.comp (Continuous.prodMk_right s)).lowerSemicontinuous hlambda ξ

omit hlambda in
/-- The regularized density tends to the density as the parameter tends to zero. -/
theorem tendsto_moreauDensity {ι : Type*} {l : Filter ι} {lam : ι → ℝ}
    (hpos : ∀ i, 0 < lam i) (hzero : Tendsto lam l (𝓝 0)) (s : E) (ξ : H) :
    Tendsto (fun i ↦ moreauDensity F (lam i) x (s, ξ)) l (𝓝 (F x (s, ξ))) := by
  have h := tendsto_moreauEnvelope (hconv s)
    (hcont.comp (Continuous.prodMk_right s)).lowerSemicontinuous hpos hzero ξ
  exact h.congr fun i ↦ (moreauDensity_eq_moreauEnvelope hcont hlow (hpos i) s ξ).symm

variable [FirstCountableTopology E]

/-- The regularized density is continuous in the value variable. -/
theorem continuous_moreauDensity (ξ : H) :
    Continuous fun s ↦ moreauDensity F lambda x (s, ξ) := by
  have hG : Continuous (Function.uncurry fun (s : E) (η : H) ↦ F x (s, η)) := hcont
  exact (continuous_moreauEnvelope_param hG hconv (fun s u ↦ hlow (s, u)) hlambda ξ).congr
    fun s ↦ (moreauDensity_eq_moreauEnvelope hcont hlow hlambda s ξ).symm

/-- The gradient field of the regularized density is continuous in the value variable. -/
theorem continuous_moreauDensityGradient (ξ : H) :
    Continuous fun s ↦ moreauDensityGradient F lambda x (s, ξ) := by
  have hG : Continuous (Function.uncurry fun (s : E) (η : H) ↦ F x (s, η)) := hcont
  exact (continuous_moreauGradient_param hG hconv (fun s u ↦ hlow (s, u)) hlambda ξ).congr
    fun s ↦ (moreauDensityGradient_eq hcont hconv hlow hlambda s ξ).symm

end Pointwise

end PDE.CalculusOfVariations
