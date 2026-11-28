/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Local.Definitions
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Gradient
public import PDE.Spaces.Sobolev.GraphSpace.Operators.Restriction

/-!
# Restriction to subdomains: local membership and the weak gradient

## Motivation

Is a function of `W^{k,p}(Ω)` in `W^{k,p}_loc(Ω)`, and is the weak gradient
of its restriction to a subdomain the restriction of its weak gradient?

## The idea

Both are immediate from the definition of the restriction, which acts on
each `Lᵖ` coordinate of the Sobolev element and leaves it unchanged almost everywhere on
the smaller set. The base coordinate gives local membership. The first-order coordinates
are the coordinates of the weak gradient, which gives the second statement.

## Main results

* `isLocallyWkpOn_baseRepresentative` (all sets `Ω`, all orders `k`, all `1 ≤ p ≤ ∞`, all
  `U` in `W^{k,p}(Ω)`): the base representative of `U` is in `W^{k,p}_loc(Ω)`.
* `wkpGradientCLM_restrictCLM_ae` (all measurable `V ⊆ Ω`, all `1 ≤ p ≤ ∞`, all `U` in
  `W^{1,p}(Ω)`): the weak gradient of the restriction of `U` to `V` is the weak gradient
  of `U`, almost everywhere on `V`.

## Relations

* `restrictCLM_apply_ae` is the statement for one coordinate, and
  `wkpGradientCLM_apply_ae` assembles the gradient from its coordinates.
* The second result is used by the interior regularity theory of the modules under
  `PDE/Elliptic/Regularity/Quasilinear/Interior/HigherOrder/` and by
  `PDE.CalculusOfVariations.LocalMinimizer.Dirichlet`.
* `gradient_restrict_between_ae` and `gradient_restrict_ae` of the nonlinear wave equation are
  the second result for the exponent `2`, the latter for a function on the whole space. Each
  is proved from it in one line.

## What stays open

Gradients of higher order and vector-valued Sobolev functions are not treated here.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.2.3, Theorem 1 (iii), for the restriction of a
  Sobolev function to an open subset.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω V : Set (ℝ^n)}

/-- A function of `W^{k,p}(Ω)` is in `W^{k,p}_loc(Ω)`: on each open subdomain with compact
closure in `Ω`, its restriction represents it. The set `Ω` is arbitrary. -/
theorem isLocallyWkpOn_baseRepresentative (U : W^{k,p}(Ω)) :
    IsLocallyWkpOn k p Ω (baseRepresentative U) := fun _ hV _ hVΩ ↦
  ⟨restrictCLM hV.measurableSet (subset_closure.trans hVΩ) U,
    restrictCLM_apply_ae hV.measurableSet (subset_closure.trans hVΩ) U (baseIndex n k)⟩

/-- Restriction to a measurable subdomain commutes with the weak gradient: the gradient of
the restriction of `U` to `V` agrees almost everywhere on `V` with the gradient of `U`. -/
theorem wkpGradientCLM_restrictCLM_ae (hV : MeasurableSet V) (hsub : V ⊆ Ω)
    (U : W^{1,p}(Ω)) :
    (wkpGradientCLM (restrictCLM hV hsub U) : ℝ^n → ℝ^n)
      =ᵐ[domainMeasure n V] wkpGradientCLM U := by
  filter_upwards [wkpGradientCLM_apply_ae (restrictCLM hV hsub U),
    ae_mono (domainMeasure_le hsub) (wkpGradientCLM_apply_ae U),
    ae_all_iff.mpr fun i ↦ restrictCLM_apply_ae hV hsub U (singleDerivIndex n i)]
    with x hsmall hbig hrow
  exact PiLp.ext fun i ↦ (hsmall i).trans ((hrow i).trans (hbig i).symm)

end SobolevSpace.GraphSpace
