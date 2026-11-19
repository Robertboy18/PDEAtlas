/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.LineRepresentative.WeakDerivative

/-!
# Classical derivative of a continuous weak-derivative representative

If a continuous `f : ℝ → ℝ` has weak derivative `g` on the whole line, then `f` equals the
mean-normalized primitive `lineRepresentative f g` everywhere, and is therefore differentiable
almost everywhere with derivative `g`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace PDE.Analysis.Evolution.HasWeakTimeDerivativeOn

/-- A continuous representative has its weak derivative as its classical
derivative almost everywhere. -/
theorem ae_hasDerivAt_of_continuous {f g : ℝ → ℝ}
    (hw : HasWeakTimeDerivativeOn univ f g) (hf : Continuous f) :
    ∀ᵐ x ∂volume, HasDerivAt f (g x) x := by
  have hg := locallyIntegrableOn_univ.mp hw.locallyIntegrable_g
  have heq : f = SobolevSpace.Slices.lineRepresentative f g :=
    Measure.eq_of_ae_eq hw.ae_eq_lineRepresentative hf
      (SobolevSpace.Slices.continuous_lineRepresentative hg)
  simpa only [← heq] using
    SobolevSpace.Slices.ae_hasDerivAt_lineRepresentative_of_locallyIntegrable (f := f) hg

end PDE.Analysis.Evolution.HasWeakTimeDerivativeOn
