/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.InvariantBall
public import PDE.Spaces.Sobolev.GraphSpace.RealLine.SecondOrder.Representative
public import PDE.Fluid.DeGregorio.Iteration.FlowRegularity
import PDE.Hyperbolic.Transport.Characteristics

/-!
# The invariant H² output satisfies the interior frozen PDE

Classical regularity is derived for the same characteristic output whose
weak H² graph and L² trace were constructed by the invariant-ball theorem.
The input curve is L²-continuous in time.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Common
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

/-- The analytic properties of a frozen output in the supported H² base ball.
`exists_hkFrozenOutput` constructs an output with these properties from every input. -/
structure IsHkFrozenOutput {B : NNReal} {T R : ℝ} (hT : 0 ≤ T)
    (f G : C(Icc (0 : ℝ) T,
      supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B))
    (W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))) (w₀ : ℝ → ℝ) (c w : ℝ → ℝ → ℝ) : Prop where
  /-- The stretching coefficient is jointly continuous. -/
  coefficient_continuous : Continuous (Function.uncurry c)
  /-- The Hilbert pair uses the input curve. -/
  hilbert_pair : ∀ t, IsHilbertPair
    (oneDimensionalPushforwardL2 (f (projIcc 0 T hT t)).val) (fun x ↦ c x t)
  /-- The normalized velocity has this spatial derivative. -/
  velocity_derivative : ∀ x t,
    HasDerivAt (fun y ↦ hkCurveHilbertVelocity hT f y t) (c x t) x
  /-- The input H² budget bounds the coefficient. -/
  coefficient_bound : ∀ x t, ‖c x t‖ ≤ 2 * (B : ℝ)
  /-- The representative is jointly continuous up to the endpoints. -/
  continuous : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ w p.1 p.2)
  /-- The output is classical in the open cylinder. -/
  classical : ContDiffOn ℝ 1 (Function.uncurry w) (univ ×ˢ Ioo (0 : ℝ) T)
  /-- The classical representative attains the initial datum. -/
  initial : ∀ x, w x 0 = w₀ x
  /-- The frozen equation holds at every interior spacetime point. -/
  transport : ∀ x t, t ∈ Ioo (0 : ℝ) T →
    deriv (w x) t + hkCurveHilbertVelocity hT f x t * deriv (fun y ↦ w y t) x =
      c x t * w x t
  /-- The fixed support enclosure holds at both endpoints as well. -/
  support : ∀ x t, t ∈ Icc (0 : ℝ) T → R < |x| → w x t = 0
  /-- The classical output represents the L²-continuous H²-bounded curve. -/
  representative : ∀ t,
    (oneDimensionalPushforwardL2 (G t).val : ℝ → ℝ) =ᵐ[volume] fun x ↦ w x t
  /-- The L² trace equals the weak H² initial datum. -/
  initial_base : (G ⟨0, le_rfl, hT⟩).val = wkpBaseCoordinateCLM W₀

/-- Each input curve produces an output in the same complete H²-bounded class
and the frozen PDE, including its L² endpoint trace. -/
theorem exists_hkFrozenOutput
    {B : NNReal} {T S R : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hBT : (B : ℝ) * T ≤ 1) (hR : S * Real.exp 2 ≤ R)
    (f : C(Icc (0 : ℝ) T,
      supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B))
    (W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))) {w₀ : ℝ → ℝ} (hw₀ : Continuous w₀)
    (hW₀ : (oneDimensionalPushforwardL2 (wkpBaseCoordinateCLM W₀) : ℝ → ℝ)
      =ᵐ[volume] w₀)
    (hsupp₀ : ∀ x, S < |x| → w₀ x = 0)
    (hbudget : hkTransportH2Bound 1 * ‖W₀‖ ≤ B) :
    ∃ (G : C(Icc (0 : ℝ) T,
        supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B))
      (c w : ℝ → ℝ → ℝ), IsHkFrozenOutput hT f G W₀ w₀ c w := by
  obtain ⟨c, X, Y, w, G, h⟩ :=
    exists_hkCurve_transport_in_h2_ball hT hS hBT hR f W₀ hw₀ hW₀ hsupp₀ hbudget
  have hw₀reg := (contDiff_and_bounds_of_h2_representative W₀ hw₀ hW₀).1
  have hYregular := contDiffOn_one_hkCurve_inverse hT f
    h.coefficient_continuous h.velocity_derivative h.flow_initial h.flow_derivative
    h.flow_continuous h.inverse_continuous h.inverse_flow h.flow_inverse
  have hVregular := contDiffOn_one_hkCurve_amplitude hT f h.toHkForwardCharacteristics hw₀reg
  obtain ⟨hwregular, hpde⟩ :=
    TransportEquation.contDiffOn_transport_of_characteristics
    hYregular hVregular h.flow_inverse h.formula h.flow_derivative h.along_flow
  exact ⟨G, c, w, ⟨h.coefficient_continuous, h.hilbert_pair, h.velocity_derivative,
    h.coefficient_bound, h.continuous, hwregular, h.initial, hpde,
    h.support, h.representative, h.initial_base⟩⟩

end DeGregorio.Iteration
