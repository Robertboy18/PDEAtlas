/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.FDeriv.Operators
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.FiniteExponent
public import PDE.Spaces.Sobolev.Calculus.Differentiation.Representative
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Gradient

/-!
# Classical representatives of the weak gradient

## Motivation

Is the weak gradient of a Sobolev function with a `C¹` representative the
classical gradient of that representative?

## The idea

It is, almost everywhere. The coordinates of the weak gradient are the first
weak derivatives. On an open set, a `C¹` representative has its classical partial
derivatives as weak derivatives, and weak derivatives are unique almost everywhere. For
the Sobolev class of a test function no uniqueness is needed, since its coordinates are
defined as the classical derivatives.

## Main results

* `wkpGradientCLM_ae_eq_gradient_of_contDiffOn` (all open `Ω`, all `1 ≤ p ≤ ∞`, all `U` in
  `W^{1,p}(Ω)` with a `C¹` representative `f` on `Ω`): `∇U = ∇f` almost everywhere on `Ω`.
* `wkpGradientCLM_testFunctionToWkp_ae` (all sets `Ω`, all `1 ≤ p ≤ ∞`, all test functions
  `φ` supported in `Ω`): the weak gradient of the class of `φ` is `∇φ` almost everywhere.

## Relations

* `wkpCoordinate_ae_eq_partialDeriv_of_contDiffOn` is the statement for one coordinate, and
  `wkpGradientCLM_apply_ae` assembles the coordinates.
* `ContDiffUpToBoundary.gradient_toWkpSpaceOn_ae` is the analogous identity for the Sobolev
  element built from classical data up to the boundary.
* `neg_divergence_gradientDensity_eq_zero_of_representative` and
  `PDE.CalculusOfVariations.LocalMinimizer.Convex` use the first result, and
  `PDE.CalculusOfVariations.LocalMinimizer.Dirichlet` uses the second.

## What stays open

Higher derivatives are not assembled here:
`wkpCoordinate_ae_eq_iteratedPartialDeriv_of_contDiffOn` gives them coordinate by
coordinate.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.1, for weak derivatives and their uniqueness.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Set (ℝ^n)}

/-- On an open set, the weak gradient of a Sobolev function with a `C¹` representative `f`
is the classical gradient of `f`, almost everywhere. Each coordinate is
`wkpCoordinate_ae_eq_partialDeriv_of_contDiffOn`. -/
theorem wkpGradientCLM_ae_eq_gradient_of_contDiffOn (hΩ : IsOpen Ω) (U : W^{1,p}(Ω))
    {f : ℝ^n → ℝ} (hf : ContDiffOn ℝ 1 f Ω)
    (hbase : baseRepresentative U =ᵐ[domainMeasure n Ω] f) :
    (wkpGradientCLM U : ℝ^n → ℝ^n) =ᵐ[domainMeasure n Ω] gradient f := by
  filter_upwards [wkpGradientCLM_apply_ae U,
    ae_all_iff.mpr (wkpCoordinate_ae_eq_partialDeriv_of_contDiffOn hΩ U hf hbase)] with x hx hd
  ext i
  rw [hx i, PDE.gradient_apply_eq_partialDeriv]
  exact hd i

/-- The weak gradient of the Sobolev class of a test function is its classical gradient,
almost everywhere on the domain. The domain is any set, since the coordinates of the class
are the classical derivatives by construction. -/
theorem wkpGradientCLM_testFunctionToWkp_ae (φ : TestFunctionOn n Ω) :
    (wkpGradientCLM (testFunctionToWkp (k := 1) (p := p) φ) : ℝ^n → ℝ^n)
      =ᵐ[domainMeasure n Ω] gradient φ.1.toFun := by
  filter_upwards [wkpGradientCLM_apply_ae (testFunctionToWkp (k := 1) (p := p) φ),
    ae_all_iff.mpr (fun i : Fin n ↦
      testFunctionToWkp_coordinate_ae (k := 1) (p := p) φ (singleDerivIndex n i))] with x hx hd
  ext i
  rw [hx i, PDE.gradient_apply_eq_partialDeriv]
  simpa only [singleDerivIndex_toList, iteratedPartialDeriv] using hd i

end SobolevSpace.GraphSpace
