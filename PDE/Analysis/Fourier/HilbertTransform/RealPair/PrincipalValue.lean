/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair
public import PDE.Analysis.Fourier.HilbertTransform.SpectralL2
public import PDE.Analysis.Fourier.HilbertTransform.Velocity
import Mathlib.Analysis.BoundedVariation
import PDE.Analysis.Calculus.Rademacher.Local

/-!
# Principal values as real spectral Hilbert pairs

The principal-value/spectral bridge supplies Hilbert pairs for real `L¹ ∩ L²`
inputs differentiable almost everywhere. Compact Lipschitz inputs satisfy these
hypotheses even when derivatives jump at the support endpoints.

`IsHilbertPair f v` is an almost-everywhere statement: `f` and `v` represent an `L²` class and
its image under the Fourier multiplier `-i sgn ξ`. The classical Hilbert transform is the
principal value `(1 / π) p.v. ∫ f (y) / (x - y) dy` at a point `x`, `HasHilbertPV`. This module
also passes from the first to the second: if `f` is integrable and locally Lipschitz and `v` is
continuous, then the principal value of `f` exists at every point `x` and equals `v x`. No
compact support is assumed, so the theorems apply to integrable rational functions with no real
pole, such as `1 / (1 + x²)`. The compactly supported `C¹` and Lipschitz cases are corollaries.

The normalized integral primitive has the principal value as its classical
derivative everywhere under the stated compact `C¹` or Lipschitz hypotheses.

## Main results

* `PDE.Analysis.IsHilbertPair.of_integrable_memLp_ae_differentiableAt`: an input in `L¹ ∩ L²`
  that is differentiable almost everywhere forms a Hilbert pair with its principal value.
* `PDE.Analysis.IsHilbertPair.eq_hilbertPV_of_integrable`: a continuous output of a Hilbert pair
  with an integrable locally Lipschitz input is the principal value of the input, at every
  point.
* `PDE.Analysis.IsHilbertPair.hasHilbertPV`: under the same hypotheses the principal value of
  the input exists at every point `x` and equals the output at `x`.
* `PDE.Analysis.IsHilbertPair.eq_hilbertPV` and
  `PDE.Analysis.IsHilbertPair.eq_hilbertPV_of_lipschitzWith_compactSupport`: the cases of a
  compactly supported `C¹` or Lipschitz input.

## How it works

Two outputs of one input agree almost everywhere (`IsHilbertPair.ae_eq_right`), and the
principal value is an output by `IsHilbertPair.of_integrable_memLp_ae_differentiableAt`. All
three requirements of that bridge hold for an integrable locally Lipschitz input `f` of a
Hilbert pair. It is integrable by hypothesis. It is in `L²` because `IsHilbertPair f v` says so
(`IsHilbertPair.memLp_left`). It is differentiable almost everywhere because it is locally
Lipschitz: this is Rademacher's theorem on an open set,
`LocallyLipschitzOn.ae_differentiableAt`, on the whole line with Lebesgue measure. Two
continuous functions that agree almost everywhere agree everywhere, and the principal value is
continuous by `continuous_hilbertPV`.

The statements are standard facts on the Hilbert transform, and the proofs follow no particular
source.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal NNReal

namespace PDE.Analysis

variable {omega v : ℝ → ℝ}

/-- The classical principal value supplies the spectral Hilbert relation for a
smooth compactly supported vorticity. Its spectral identification is proved by
Abel regularization in `SpectralBridge`. -/
theorem IsHilbertPair.of_contDiff_compactSupport
    (hsmooth : ContDiff ℝ ∞ omega) (hsupp : HasCompactSupport omega) :
    IsHilbertPair omega (hilbertPV omega) := by
  have hmem : MemLp (fun x ↦ (omega x : ℂ)) 2 (volume : Measure ℝ) :=
    Complex.ofRealCLM.comp_memLp' (hsmooth.continuous.memLp_of_hasCompactSupport hsupp)
  exact IsHilbertPair.of_memLp hmem
    (hilbertPV_eq_hilbertTransform_ae_of_contDiff_compactSupport hsmooth hsupp
      (hmem.toLp _) hmem.coeFn_toLp.symm)

/-- An almost-everywhere differentiable real `L¹ ∩ L²` input and its
principal value satisfy the concrete spectral Hilbert relation. -/
theorem IsHilbertPair.of_integrable_memLp_ae_differentiableAt {omega : ℝ → ℝ}
    (hint : Integrable omega) (hmem : MemLp omega 2 (volume : Measure ℝ))
    (hdiff : ∀ᵐ x, DifferentiableAt ℝ omega x) :
    IsHilbertPair omega (hilbertPV omega) := by
  have hc : MemLp (fun x ↦ (omega x : ℂ)) 2 (volume : Measure ℝ) := hmem.ofReal
  exact IsHilbertPair.of_memLp hc
    (hilbertPV_eq_hilbertTransform_ae_of_ae_differentiableAt hint hdiff
      (hc.toLp _) hc.coeFn_toLp.symm)

/-- Compact `C¹` vorticity yields a principal-value Hilbert pair. -/
theorem IsHilbertPair.of_contDiff_one_compactSupport {omega : ℝ → ℝ}
    (hsmooth : ContDiff ℝ 1 omega) (hsupp : HasCompactSupport omega) :
    IsHilbertPair omega (hilbertPV omega) := by
  apply IsHilbertPair.of_integrable_memLp_ae_differentiableAt
  · exact memLp_one_iff_integrable.mp (hsmooth.continuous.memLp_of_hasCompactSupport hsupp)
  · exact hsmooth.continuous.memLp_of_hasCompactSupport hsupp
  · exact Filter.Eventually.of_forall (hsmooth.differentiable (by norm_num))

/-- Compactly supported Lipschitz vorticity and its principal value form
a concrete spectral Hilbert pair, using real a.e. differentiability. -/
theorem IsHilbertPair.of_lipschitzWith_compactSupport {omega : ℝ → ℝ} {K : ℝ≥0}
    (hlip : LipschitzWith K omega) (hsupp : HasCompactSupport omega) :
    IsHilbertPair omega (hilbertPV omega) := by
  apply IsHilbertPair.of_integrable_memLp_ae_differentiableAt
  · exact memLp_one_iff_integrable.mp (hlip.continuous.memLp_of_hasCompactSupport hsupp)
  · exact hlip.continuous.memLp_of_hasCompactSupport hsupp
  · exact hlip.ae_differentiableAt_real

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

/-- A continuous real Hilbert representative equals the principal value
everywhere for compact `C¹` input. -/
theorem IsHilbertPair.eq_hilbertPV (h : IsHilbertPair omega v)
    (hv : Continuous v) (homega : ContDiff ℝ 1 omega)
    (hsupp : HasCompactSupport omega) : v = hilbertPV omega :=
  h.eq_hilbertPV_of_integrable hv (homega.continuous.integrable_of_hasCompactSupport hsupp)
    homega.locallyLipschitz

/-- The localized norm bound for the principal-value Hilbert transform of smooth
odd vorticity supported in `[-L,L]`. Oddness makes the stated right support bound
sufficient for both sides. -/
theorem integral_sq_hilbertPV_Ioo_le {L : ℝ}
    (hsmooth : ContDiff ℝ ∞ omega) (hsupp : HasCompactSupport omega)
    (homega : Function.Odd omega) (hsupport : ∀ x, L ≤ x → omega x = 0) :
    (∫ x in Ioo 0 L, hilbertPV omega x ^ 2) ≤ ∫ x in Ioo 0 L, omega x ^ 2 :=
  (IsHilbertPair.of_contDiff_compactSupport hsmooth hsupp).integral_sq_Ioo_le
    homega (hilbertPV_even_of_odd homega) hsupport

/-- Compact `C¹` vorticity and the derivative of its constructed normalized
velocity satisfy the spectral Hilbert relation. -/
theorem isHilbertPair_deriv_hilbertPVVelocity {omega : ℝ → ℝ}
    (hsmooth : ContDiff ℝ 1 omega) (hsupp : HasCompactSupport omega) :
    IsHilbertPair omega (deriv (hilbertPVVelocity omega)) := by
  rw [show deriv (hilbertPVVelocity omega) = hilbertPV omega from funext fun x ↦
    (hasDerivAt_hilbertPVVelocity_of_contDiff_one_compactSupport hsmooth hsupp x).deriv]
  exact IsHilbertPair.of_contDiff_one_compactSupport hsmooth hsupp

/-- The normalized principal-value velocity of compact Lipschitz vorticity
satisfies the spectral Hilbert relation with its classical derivative. -/
theorem isHilbertPair_deriv_hilbertPVVelocity_of_lipschitzWith_compactSupport
    {omega : ℝ → ℝ} {K : ℝ≥0}
    (hlip : LipschitzWith K omega) (hsupp : HasCompactSupport omega) :
    IsHilbertPair omega (deriv (hilbertPVVelocity omega)) := by
  rw [show deriv (hilbertPVVelocity omega) = hilbertPV omega from funext fun x ↦
    (hasDerivAt_hilbertPVVelocity_of_lipschitzWith_compactSupport hlip hsupp x).deriv]
  exact IsHilbertPair.of_lipschitzWith_compactSupport hlip hsupp

/-- Continuous spectral representatives agree everywhere with the
principal value for compact Lipschitz input, including boundary slope jumps. -/
theorem IsHilbertPair.eq_hilbertPV_of_lipschitzWith_compactSupport
    {f v : ℝ → ℝ} {K : ℝ≥0} (h : IsHilbertPair f v) (hv : Continuous v)
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) : v = hilbertPV f :=
  h.eq_hilbertPV_of_integrable hv (hf.continuous.integrable_of_hasCompactSupport hc)
    hf.locallyLipschitz

end PDE.Analysis
