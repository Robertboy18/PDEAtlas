/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.AnalyticIdentity
public import PDE.Elliptic.Classical.Harmonic.Analyticity
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Unique continuation for harmonic functions

Two classical harmonic functions on a connected open domain coincide throughout the
domain if they agree on a nonempty open subset, or if all their iterated Fréchet
derivatives agree at one interior point. The derivative condition includes order zero.

Harmonicity supplies real analyticity through
`PDE.Elliptic.Classical.Harmonic.Analyticity`. Mathlib's multivariable analytic identity
theorem propagates local equality through a preconnected set. No smoothness beyond
the original `C²` harmonicity hypothesis is assumed.
-/

@[expose] public section

open Filter Metric Set
open scoped Topology

namespace LaplacianEquation

/-- Unique continuation for classical harmonic functions: equality on a nonempty open subset
of a preconnected open domain implies equality throughout the domain. -/
theorem IsHarmonicPDE.eqOn_of_isPreconnected_of_eqOn
    {n : ℕ} [Fact (0 < n)] {u v : ℝ^n → ℝ} {U V : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (hv : IsHarmonicPDE n v U)
    (hU : IsOpen U) (hUconn : IsPreconnected U)
    (hV : IsOpen V) (hVne : V.Nonempty) (hVU : V ⊆ U) (huv : EqOn u v V) :
    EqOn u v U := by
  obtain ⟨x, hx⟩ := hVne
  apply (hu.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
    (hv.analyticOnNhd hU) hUconn (hVU hx)
  filter_upwards [hV.mem_nhds hx] with y hy
  exact huv hy

/-- A classical harmonic function on a preconnected open domain is determined by its
iterated Fréchet derivatives of all orders at any interior point. No smoothness beyond
the `C²` regularity in `IsHarmonicPDE` is assumed. -/
theorem IsHarmonicPDE.eqOn_of_isPreconnected_of_iteratedFDeriv_eq
    {n : ℕ} [Fact (0 < n)] {u v : ℝ^n → ℝ} {U : Set (ℝ^n)}
    (hu : IsHarmonicPDE n u U) (hv : IsHarmonicPDE n v U)
    (hU : IsOpen U) (hUconn : IsPreconnected U)
    {x : ℝ^n} (hx : x ∈ U)
    (hderiv : ∀ k : ℕ, iteratedFDeriv ℝ k u x = iteratedFDeriv ℝ k v x) :
    EqOn u v U := by
  have hau : AnalyticOnNhd ℝ u U := hu.analyticOnNhd hU
  have hav : AnalyticOnNhd ℝ v U := hv.analyticOnNhd hU
  exact hau.eqOn_of_preconnected_of_eventuallyEq hav hUconn hx
    ((hau x hx).eventuallyEq_of_iteratedFDeriv_eq (hav x hx) hderiv)

end LaplacianEquation
