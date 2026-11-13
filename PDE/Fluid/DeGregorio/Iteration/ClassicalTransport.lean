/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Transport
public import PDE.Fluid.DeGregorio.Iteration.FlowRegularity
public import PDE.Fluid.DeGregorio.Iteration.AmplitudeRegularity
import PDE.Hyperbolic.Transport.Characteristics

/-!
# Frozen Eulerian transport for the complete bounded H² class

Every L²-continuous curve in the bounded weak H² class generates its
normalized Hilbert velocity and stretching coefficient. The constructed
characteristics, their Eulerian inverse, and the exponential amplitude give
a classical frozen transport solution on the full prescribed open time
cylinder, with continuous L² trace and a common compact support enclosure
on the closed interval.

The stretching coefficient is the Hilbert transform of the input curve, so the
equation is linear in the transported field.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis
open scoped Topology

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- Every input in the complete bounded H² curve class constructs a
classical Eulerian solution of its frozen Hilbert transport equation
on the prescribed interval. The common support enclosure and L²-continuous
initial trace are retained from the characteristic construction.

The coefficient is the Hilbert transform of the input curve, not of the
output. -/
theorem exists_hkCurve_classical_transport
    {A : Set (ℝ^1)} {B : NNReal} {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    {w₀ : ℝ → ℝ} (hw₀ : ContDiff ℝ 1 w₀)
    (hsupp₀ : ∀ x, S < |x| → w₀ x = 0) :
    ∃ c w : ℝ → ℝ → ℝ,
      Continuous (Function.uncurry c) ∧
      (∀ t, IsHilbertPair (oneDimensionalPushforwardL2 (f (projIcc 0 T hT t)).val)
        (fun x ↦ c x t)) ∧
      (∀ x t, HasDerivAt (fun y ↦ hkCurveHilbertVelocity hT f y t) (c x t) x) ∧
      Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ w p.1 p.2) ∧
      ContDiffOn ℝ 1 (Function.uncurry w) (univ ×ˢ Ioo (0 : ℝ) T) ∧
      (∀ x, w x 0 = w₀ x) ∧
      (∀ x t, t ∈ Ioo (0 : ℝ) T →
        deriv (w x) t + hkCurveHilbertVelocity hT f x t * deriv (fun y ↦ w y t) x =
          c x t * w x t) ∧
      (∀ x t, t ∈ Icc (0 : ℝ) T →
        S * Real.exp (2 * (B : ℝ) * T) < |x| → w x t = 0) ∧
      ∃ F : C(Icc (0 : ℝ) T, Lp ℝ 2 volume),
        ∀ t, (F t : ℝ → ℝ) =ᵐ[volume] fun x ↦ w x t := by
  obtain ⟨c, X, Y, w, h⟩ :=
    exists_hkCurve_transport_along_characteristics hT hS f hw₀.continuous hsupp₀
  have hYregular := contDiffOn_one_hkCurve_inverse hT f
    h.coefficient_continuous h.velocity_derivative h.flow_initial h.flow_derivative
    h.flow_continuous h.inverse_continuous h.inverse_flow h.flow_inverse
  have hVregular := contDiffOn_one_hkCurve_amplitude hT f h.toHkForwardCharacteristics hw₀
  obtain ⟨hwregular, hpde⟩ :=
    TransportEquation.contDiffOn_transport_of_characteristics
    hYregular hVregular h.flow_inverse h.formula h.flow_derivative h.along_flow
  exact ⟨c, w, h.coefficient_continuous, h.hilbert_pair, h.velocity_derivative,
    h.continuous, hwregular, h.initial, hpde, h.support, h.representative⟩

end DeGregorio.Iteration
