/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Characteristics

/-!
# Characteristic data for frozen De Gregorio transport

`HkForwardCharacteristics` combines the Hilbert coefficient of an H² input curve
with its position flow. `HkCharacteristics` adds Eulerian coordinates: an inverse of
the flow with a quantitative Lipschitz bound. Lemmas that use only the forward data
take the smaller structure as hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis SobolevSpace SobolevSpace.GraphSpace
open scoped Topology

namespace DeGregorio.Iteration

/-- The coefficient and forward characteristic given by an H² input curve. -/
structure HkForwardCharacteristics {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    (c X : ℝ → ℝ → ℝ) : Prop where
  /-- Joint continuity of the stretching coefficient. -/
  coefficient_continuous : Continuous (Function.uncurry c)
  /-- The coefficient is the Hilbert transform of the clamped input. -/
  hilbert_pair : ∀ t, IsHilbertPair
    (oneDimensionalPushforwardL2 (f (projIcc 0 T hT t)).val) (fun x ↦ c x t)
  /-- The coefficient is the derivative of the normalized velocity. -/
  velocity_derivative : ∀ x t,
    HasDerivAt (fun y ↦ hkCurveHilbertVelocity hT f y t) (c x t) x
  /-- The input budget bounds the coefficient. -/
  coefficient_bound : ∀ x t, ‖c x t‖ ≤ 2 * (B : ℝ)
  /-- The initial position is its characteristic label. -/
  flow_initial : ∀ x, X x 0 = x
  /-- The flow solves the velocity equation. -/
  flow_derivative : ∀ x t, t ∈ Icc (0 : ℝ) T →
    HasDerivAt (X x) (hkCurveHilbertVelocity hT f (X x t) t) t
  /-- Joint continuity includes the closed time endpoints. -/
  flow_continuous : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ X p.1 p.2)

/-- Forward characteristics with quantitative Eulerian inverse coordinates. -/
structure HkCharacteristics {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B))
    (c X Y : ℝ → ℝ → ℝ) : Prop extends HkForwardCharacteristics hT f c X where
  /-- Joint continuity of the inverse coordinates. -/
  inverse_continuous : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ Y p.1 p.2)
  /-- Inversion recovers the characteristic label. -/
  inverse_flow : ∀ x t, t ∈ Icc (0 : ℝ) T → Y (X x t) t = x
  /-- Every Eulerian point lies on its characteristic. -/
  flow_inverse : ∀ y t, t ∈ Icc (0 : ℝ) T → X (Y y t) t = y
  /-- The inverse has the uniform bound on the prescribed interval. -/
  inverse_lipschitz : ∀ t, t ∈ Icc (0 : ℝ) T →
    LipschitzWith ⟨Real.exp (2 * (B : ℝ) * T), (Real.exp_pos _).le⟩ (fun y ↦ Y y t)

end DeGregorio.Iteration
