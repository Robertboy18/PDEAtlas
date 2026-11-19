/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.Constructors

/-!
# Restriction of classical Sobolev elements

Embedding a smooth compactly supported function in a Sobolev graph space commutes with
restriction to a measurable subdomain, at every derivative order and every exponent.
The identity follows coordinatewise from almost-everywhere restriction of `Lᵖ` classes.
-/

@[expose] public section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal

/-- The smooth Sobolev constructor commutes with restriction to a measurable subdomain.
No boundary regularity or support condition relative to either domain is required. -/
theorem restrictCLM_mkWkpSpaceOnOfContDiff
    {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω Ωbig : Set (ℝ^n)}
    (hΩ : MeasurableSet Ω) (hsub : Ω ⊆ Ωbig)
    (f : ℝ^n → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f) :
    restrictCLM (k := k) (p := p) hΩ hsub
        (mkWkpSpaceOnOfContDiff (Ω := Ωbig) f hf hcs) =
      mkWkpSpaceOnOfContDiff (Ω := Ω) f hf hcs := by
  apply Subtype.ext
  refine PiLp.ext fun a ↦ Lp.ext ?_
  refine (restrictCLM_apply_ae hΩ hsub _ a).trans (Filter.EventuallyEq.trans ?_
    (mkWkpSpaceOnOfContDiff_apply_ae (Ω := Ω) f hf hcs a).symm)
  exact ae_mono (domainMeasure_le hsub)
    (mkWkpSpaceOnOfContDiff_apply_ae (Ω := Ωbig) f hf hcs a)

end SobolevSpace.GraphSpace
