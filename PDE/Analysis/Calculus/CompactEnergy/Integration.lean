/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime
public import PDE.Analysis.Calculus.ParametricIntegral.CompactSupport
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import PDE.FDeriv.Calculus

/-!
# Integrating compactly supported classical energy balances

Compact spatial support supplies integrability and domination for differentiation
under the integral; the vanishing integral of each spatial divergence term is
`PDE.DistributionTheory.integral_partialDeriv_eq_zero_of_hasCompactSupport`. The support is
uniform only on the open time interval where the identity is used.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Filter MeasureTheory Set PDE.Common
open scoped Topology

variable {n : ℕ}

/-- A common compact spatial support permits differentiation of a local `C¹` family. -/
theorem hasDerivAt_integral_compact_support
    {f : ℝ^(n + 1) → ℝ} {I : Set ℝ} {K : Set (ℝ^n)}
    (hI : IsOpen I) (hK : IsCompact K)
    (hf : ∀ t ∈ I, ∀ x, ContDiffAt ℝ 1 f (timeSpaceCons t x))
    (hs : ∀ t ∈ I, ∀ x ∉ K, f (timeSpaceCons t x) = 0)
    {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (fun s ↦ ∫ x, f (timeSpaceCons s x))
      (∫ x, (∂[0] f) (timeSpaceCons t x)) t := by
  let F : ℝ → ℝ^n → ℝ := fun s x ↦ f (timeSpaceCons s x)
  let D : ℝ → ℝ^n → ℝ := fun s x ↦ (∂[0] f) (timeSpaceCons s x)
  have hfc : ContinuousOn F.uncurry (I ×ˢ univ) := by
    intro p hp
    exact (ContinuousAt.comp (f := fun z : ℝ × ℝ^n ↦ timeSpaceCons z.1 z.2)
      (hf p.1 hp.1 p.2).continuousAt
      (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.continuousAt).continuousWithinAt
  have hdc : ContinuousOn (Function.uncurry D) (I ×ˢ univ) := by
    intro p hp
    have hc : ContinuousAt (∂[0] f) (timeSpaceCons p.1 p.2) :=
      (contDiffAt_partialDeriv 0 (hf p.1 hp.1 p.2) 0).continuousAt
    have hm : ContinuousAt (fun z : ℝ × ℝ^n ↦ timeSpaceCons z.1 z.2) p :=
      (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.continuousAt
    exact (ContinuousAt.comp (f := fun z : ℝ × ℝ^n ↦ timeSpaceCons z.1 z.2)
      hc hm).continuousWithinAt
  exact hasDerivAt_integral_of_locally_uniform_compact_support hI hK hfc hdc
    (fun s hsI x ↦ hasDerivAt_timeSpaceCons f s x
      ((hf s hsI x).differentiableAt one_ne_zero)) hs ht

end PDE.Analysis
