/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Characteristics.Data

/-!
# The constructed transport in characteristic coordinates

`HkTransportData` records the characteristic formula, the initial values, and the
closed-interval evolution of the transported field. `HkTransportResult` adds signs,
support, and the continuous L² representative.
-/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Analysis SobolevSpace SobolevSpace.GraphSpace
open scoped Topology

namespace DeGregorio.Iteration

/-- A continuous transport of the prescribed datum along the flow. -/
structure HkTransportData {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B)) (w₀ : ℝ → ℝ)
    (c X Y w : ℝ → ℝ → ℝ) : Prop extends HkCharacteristics hT f c X Y where
  /-- The Eulerian field is jointly continuous on the closed cylinder. -/
  continuous : Continuous (fun p : ℝ × Icc (0 : ℝ) T ↦ w p.1 p.2)
  /-- The transport attains the initial datum. -/
  initial : ∀ x, w x 0 = w₀ x
  /-- The characteristic formula uses the constructed coefficient and flow. -/
  formula : ∀ x t, t ∈ Icc (0 : ℝ) T →
    w (X x t) t = w₀ x * Real.exp (∫ s in 0..t, c (X x s) s)
  /-- The amplitude solves its ODE, including one-sided endpoint derivatives. -/
  along_flow : ∀ x t, t ∈ Icc (0 : ℝ) T →
    HasDerivWithinAt (fun s ↦ w (X x s) s)
      (c (X x t) t * w (X x t) t) (Icc (0 : ℝ) T) t

/-- Signs, support and the L² curve of the constructed characteristic transport. -/
structure HkTransportResult {A : Set (ℝ^1)} {B : NNReal} {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, supportedHkBaseBall 1 2 univ A B)) (S : ℝ) (w₀ : ℝ → ℝ)
    (c X Y w : ℝ → ℝ → ℝ) : Prop extends HkTransportData hT f w₀ c X Y w where
  /-- Zero values follow exactly the zero set of the initial datum. -/
  zero_iff : ∀ x t, t ∈ Icc (0 : ℝ) T → (w (X x t) t = 0 ↔ w₀ x = 0)
  /-- Positive values retain their initial sign. -/
  pos_iff : ∀ x t, t ∈ Icc (0 : ℝ) T → (0 < w (X x t) t ↔ 0 < w₀ x)
  /-- Negative values retain their initial sign. -/
  neg_iff : ∀ x t, t ∈ Icc (0 : ℝ) T → (w (X x t) t < 0 ↔ w₀ x < 0)
  /-- The amplitude is bounded by its initial value and the input budget. -/
  norm_le : ∀ y t, t ∈ Icc (0 : ℝ) T →
    ‖w y t‖ ≤ ‖w₀ (Y y t)‖ * Real.exp (2 * (B : ℝ) * t)
  /-- A common support enclosure throughout the prescribed interval. -/
  support : ∀ y t, t ∈ Icc (0 : ℝ) T →
    S * Real.exp (2 * (B : ℝ) * T) < |y| → w y t = 0
  /-- The Eulerian field represents one continuous L² curve. -/
  representative : ∃ F : C(Icc (0 : ℝ) T, Lp ℝ 2 volume),
    ∀ t, (F t : ℝ → ℝ) =ᵐ[volume] fun y ↦ w y t

end DeGregorio.Iteration
