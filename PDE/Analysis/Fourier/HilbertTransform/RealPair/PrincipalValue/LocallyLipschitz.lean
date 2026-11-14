/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair
public import PDE.Analysis.Fourier.HilbertTransform.PrincipalValue.LocallyLipschitz
import PDE.Analysis.Fourier.HilbertTransform.RealPair.PrincipalValue
import PDE.Analysis.Calculus.Rademacher.Local

/-!
# The pointwise Hilbert relation of a Hilbert pair with a locally Lipschitz input

`IsHilbertPair f v` is an almost-everywhere statement: `f` and `v` represent an `L²` class and
its image under the Fourier multiplier `-i sgn ξ`. The classical Hilbert transform is the
principal value `(1 / π) p.v. ∫ f (y) / (x - y) dy` at a point `x`, `HasHilbertPV`. This module
passes from the first to the second: if `f` is integrable and locally Lipschitz and `v` is
continuous, then the principal value of `f` exists at every point `x` and equals `v x`. No
compact support is assumed, so the theorems apply to rational functions that decay at
infinity. The compactly supported `C¹` and Lipschitz cases are `IsHilbertPair.eq_hilbertPV` and
`IsHilbertPair.eq_hilbertPV_of_lipschitzWith_compactSupport` in
`PDE.Analysis.Fourier.HilbertTransform.RealPair.PrincipalValue`.

## Main results

* `PDE.Analysis.IsHilbertPair.eq_hilbertPV_of_integrable`: a continuous output of a Hilbert pair
  with an integrable locally Lipschitz input is the principal value of the input, at every
  point.
* `PDE.Analysis.IsHilbertPair.hasHilbertPV`: under the same hypotheses the principal value of
  the input exists at every point `x` and equals the output at `x`.

## How it works

A function in `L¹ ∩ L²` that is differentiable almost everywhere forms a Hilbert pair with its
principal value (`IsHilbertPair.of_integrable_memLp_ae_differentiableAt`), and two outputs of
one input agree almost everywhere (`IsHilbertPair.ae_eq_right`). All three requirements hold
for the input `f` here. It is integrable by hypothesis. It is in `L²` because `IsHilbertPair f v`
says so (`IsHilbertPair.memLp_left`). It is differentiable almost everywhere because it is
locally Lipschitz: this is Rademacher's theorem on an open set,
`LocallyLipschitzOn.ae_differentiableAt`, on the whole line with Lebesgue measure. Two
continuous functions that agree almost everywhere agree everywhere, and the principal value is
continuous by `continuous_hilbertPV`.

The statements are standard facts on the Hilbert transform, and the proofs follow no particular
source.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis

/-- **A continuous output of a Hilbert pair is the principal value.** If `v` represents the
Hilbert transform of `f`, `v` is continuous, and `f` is integrable and locally Lipschitz, then
`v` is the principal value of `f` at every point. The pair supplies `f ∈ L²`, and the local
Rademacher theorem `LocallyLipschitzOn.ae_differentiableAt` supplies the differentiability of `f`
almost everywhere. -/
theorem IsHilbertPair.eq_hilbertPV_of_integrable {f v : ℝ → ℝ} (h : IsHilbertPair f v)
    (hv : Continuous v) (hf : Integrable f) (hlip : LocallyLipschitz f) : v = hilbertPV f := by
  have hd : ∀ᵐ x, DifferentiableAt ℝ f x := by
    simpa only [Measure.restrict_univ] using
      hlip.locallyLipschitzOn.ae_differentiableAt (μ := volume) isOpen_univ
  exact Measure.eq_of_ae_eq
    (h.ae_eq_right (.of_integrable_memLp_ae_differentiableAt hf h.memLp_left hd))
    hv (continuous_hilbertPV hf hlip)

/-- **The pointwise Hilbert relation.** If `v` represents the Hilbert transform of `f`, `v` is
continuous, and `f` is integrable and locally Lipschitz, then at every point `x` the principal
value `(1 / π) p.v. ∫ f (y) / (x - y) dy` exists and equals `v x`. -/
theorem IsHilbertPair.hasHilbertPV {f v : ℝ → ℝ} (h : IsHilbertPair f v) (hv : Continuous v)
    (hf : Integrable f) (hlip : LocallyLipschitz f) (x : ℝ) : HasHilbertPV f x (v x) :=
  h.eq_hilbertPV_of_integrable hv hf hlip ▸ hasHilbertPV_of_locallyLipschitz hf hlip x

end PDE.Analysis
