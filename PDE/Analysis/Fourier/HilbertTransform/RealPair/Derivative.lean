/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.WeakDerivative
import PDE.Analysis.Evolution.Time.WeakDerivative.AbsolutelyContinuous
import PDE.Spaces.Sobolev.Calculus.Slicing.LineRepresentative.ContinuousDerivative

/-!
# The derivative of a Hilbert pair

The Hilbert transform commutes with differentiation. For real `L²` pairs: if `g` represents the
Hilbert transform of `f`, `f` has the square-integrable weak derivative `f'`, and `g` is
continuous, then `deriv g` represents the Hilbert transform of `f'`. No compact support is
assumed. The compactly supported `C²` case is `IsHilbertPair.deriv_of_contDiff_two` in
`PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev`, and the second derivative of the
Hilbert velocity of a compactly supported Lipschitz function,
`isHilbertPair_deriv_deriv_hilbertPVVelocity_of_lipschitzWith_compactSupport` in
`PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev.ClassicalDerivative`, is a case of the
weak form.

## Main results

* `PDE.Analysis.IsHilbertPair.deriv_of_weak`: the derivative of the output of a Hilbert pair
  represents the Hilbert transform of the weak derivative of the input, for every input with a
  square-integrable weak derivative and every continuous output.
* `PDE.Analysis.IsHilbertPair.deriv`: the derivatives of a Hilbert pair form a Hilbert pair, for
  every continuously differentiable input with square-integrable derivative and every
  continuous output.

## How it works

The Hilbert transform commutes with the weak derivative on `L²`
(`IsHilbertPair.exists_hasWeakTimeDerivativeOn`), and a continuous function with a weak
derivative has it as derivative almost everywhere
(`HasWeakTimeDerivativeOn.ae_hasDerivAt_of_continuous`). A continuously differentiable function
has its derivative as weak derivative
(`HasWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval`).

The statements are standard facts on the Hilbert transform, and the proofs follow no particular
source.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open PDE.Analysis.Evolution

namespace PDE.Analysis

/-- **The derivative of a Hilbert pair, weak form.** If `g` represents the Hilbert transform of
`f`, `f` has the square-integrable weak derivative `f'`, and `g` is continuous, then `deriv g`
represents the Hilbert transform of `f'`. The proof shows that `g` is differentiable almost
everywhere, which is all that the almost-everywhere relation `IsHilbertPair` sees of `deriv g`. -/
theorem IsHilbertPair.deriv_of_weak {f f' g : ℝ → ℝ} (h : IsHilbertPair f g)
    (hf' : MemLp f' 2 volume) (hweak : HasWeakTimeDerivativeOn univ f f') (hg : Continuous g) :
    IsHilbertPair f' (deriv g) := by
  obtain ⟨w, hw, hd⟩ := h.exists_hasWeakTimeDerivativeOn hf' hweak
  apply hw.congr_right_ae
  filter_upwards [hd.ae_hasDerivAt_of_continuous hg] with x hx
  exact hx.deriv.symm

/-- **The derivative of a Hilbert pair.** If `g` represents the Hilbert transform of `f`, `f` is
continuously differentiable with a square-integrable derivative, and `g` is continuous, then
`deriv g` represents the Hilbert transform of `deriv f`. -/
protected theorem IsHilbertPair.deriv {f g : ℝ → ℝ} (h : IsHilbertPair f g)
    (hf : ContDiff ℝ 1 f) (hf' : MemLp (deriv f) 2 volume) (hg : Continuous g) :
    IsHilbertPair (deriv f) (deriv g) :=
  h.deriv_of_weak hf'
    (.of_absolutelyContinuousOnInterval hf.continuous.locallyIntegrable
      (hf.continuous_deriv le_rfl).locallyIntegrable
      (fun _ _ ↦ hf.contDiffOn.absolutelyContinuousOnInterval)
      (.of_forall fun x ↦ (hf.differentiable one_ne_zero x).hasDerivAt)) hg

end PDE.Analysis
