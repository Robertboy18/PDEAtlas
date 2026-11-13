/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

-- Supplies `ContDiffAt.hasStrictFDerivAt'` for the joint wave-family derivative.
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Dynamics.Flow
public import PDE.Hyperbolic.ConservationLaw.System.WaveCurve
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Characteristic integral-curve wave families

A flow whose trajectories solve a characteristic ODE and whose joint
time-state map is locally `C¹` produces a `LocalWaveFamily`. The required
Fréchet derivative is derived from the ODE and flow laws rather than assumed:
the time block is the right characteristic vector, while the initial-state
block is the identity because every flow fixes states at time zero.

The trajectories are integral curves of a right characteristic field, as in (6) of Evans,
§11.2.1, which defines the rarefaction curves `Rₖ(z₀)`. Such flows supply the rarefaction
branches of the wave curves `Tₖ` of §11.2.4.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §11.2.1, equation (6) and the definition
  of rarefaction curves; §11.2.4, definition of the wave curves `Tₖ`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Hyperbolic.ConservationLaw.System

variable {m : ℕ}
variable {flux : ℝ^m → ℝ^m}
variable {fields : Fin m → CharacteristicField flux}

namespace LocalWaveFamily

/-- Characteristic flows with joint local `C¹` dependence on time and initial
state form a local wave family.

The integral-curve hypothesis supplies the time derivative; the flow laws
supply the zero-strength identity and its state derivative. -/
def ofCharacteristicFlows
    (flows : Fin m → Flow ℝ (ℝ^m))
    (hcontDiff : ∀ k state,
      ContDiffAt ℝ 1
        (fun p : ℝ × ℝ^m ↦ flows k p.1 p.2) (0, state))
    (hintegral : ∀ k state,
      IsIntegralCurveAt (fun strength ↦ flows k strength state)
        (fields k).vectorField 0) :
    LocalWaveFamily flux fields where
  curve k strength state := flows k strength state
  curve_zero k state := (flows k).map_zero_apply state
  hasStrictFDerivAt_zero k state _hstate :=
    (hcontDiff k state).hasStrictFDerivAt'
      (hasFDerivAt_waveStep_zero (flows k) state
        ((fields k).rightEigenvector state)
        (flows k).map_zero_apply
        ((hcontDiff k state).differentiableAt one_ne_zero) (by
          simpa [CharacteristicField.vectorField,
            (flows k).map_zero_apply] using
            (hintegral k state).hasDerivAt))
      one_ne_zero

variable {states : Set (ℝ^m)}

/-- At zero strength, each wave curve has derivative equal to its right
characteristic vector. -/
theorem hasDerivAt_curve_zero
    (W : LocalWaveFamily flux fields states) (k : Fin m) (state : ℝ^m) (hstate : state ∈ states) :
    HasDerivAt (fun strength ↦ W.curve k strength state) ((fields k).rightEigenvector state) 0 := by
  simpa [Function.comp_def, waveStepDerivative_apply] using
    (W.hasStrictFDerivAt_zero k state hstate).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (HasDerivAt.prodMk
        (hasDerivAt_id' (0 : ℝ)) (hasDerivAt_const (0 : ℝ) state))

/-- The tangent of each local wave curve at zero strength is its right
characteristic vector. -/
theorem curveTangent_zero
    (W : LocalWaveFamily flux fields states) (k : Fin m) (state : ℝ^m) (hstate : state ∈ states) :
    curveTangent (fun strength ↦ W.curve k strength state) 0 = (fields k).rightEigenvector state :=
  (W.hasDerivAt_curve_zero k state hstate).deriv

/-- The tangent of a local wave curve at zero strength is nonzero. -/
theorem curveTangent_zero_ne_zero
    (W : LocalWaveFamily flux fields states) (k : Fin m) (state : ℝ^m) (hstate : state ∈ states) :
    curveTangent (fun strength ↦ W.curve k strength state) 0 ≠ 0 := by
  rw [W.curveTangent_zero k state hstate]
  exact ((fields k).eigenvector state).2

end LocalWaveFamily

end PDE.Hyperbolic.ConservationLaw.System
