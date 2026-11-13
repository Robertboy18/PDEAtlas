/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Density.TimeSlices

/-!
# Sobolev continuity of smooth spacetime slices

A smooth compactly supported spacetime test determines a continuous curve in W¹ᵖ(Ω),
for every spatial set Ω and `1 ≤ p ≤ ∞`. Its base Lᵖ coordinate is differentiable in
time, with derivative given by the slice of its time derivative.

The graph norm involves only the base row and the spatial first derivatives. Each row
is a slice of a smooth compactly supported spacetime function, so the Lᵖ slice theorem
applies to all rows. This argument requires neither a regular boundary nor finite
volume of Ω.
-/

@[expose] public section

noncomputable section

open PDE (iteratedPartialDeriv)
open Filter Function MeasureTheory Set TopologicalSpace
open scoped Distributions ENNReal

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}

/-- Each first-order graph coordinate is the spatial Lᵖ class of the corresponding
spacetime derivative, sliced at the same time. -/
private theorem globalTestFunctionToWkpOn_sliceRight_coordinate
    (Φ : 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ)) (t : ℝ) (d : DerivIndex n 1) :
    (globalTestFunctionToWkpOn (k := 1) (p := p) (Ω := Ω)
      (TestFunction.sliceRight t Φ) : WkpAmbientOn n 1 p Ω) d =
      toLpOfContCompact (p := p) (Ω := Ω)
        (TestFunction.sliceRight t
          (firstOrderRows Φ (fun j ↦
            TestFunction.lineDerivCLM ℝ (0, EuclideanSpace.single j (1 : ℝ)) Φ) d))
        (TestFunction.sliceRight t _).continuous
        (TestFunction.sliceRight t _).hasCompactSupport := by
  rcases d.eq_baseIndex_or_eq_singleDerivIndex with rfl | ⟨j, rfl⟩
  · simp only [firstOrderRows_baseIndex]
    apply Lp.ext
    filter_upwards [globalTestFunctionToWkpOn_coordinate_ae
      (p := p) (Ω := Ω) (TestFunction.sliceRight t Φ) (baseIndex n 1),
      toLpOfContCompact_coeFn (p := p) (Ω := Ω)
        (TestFunction.sliceRight t Φ).continuous
        (TestFunction.sliceRight t Φ).hasCompactSupport] with x hx hy
    rw [hx, hy]
    simp only [baseIndex_toList, iteratedPartialDeriv]
    rfl
  · simp only [firstOrderRows_singleDerivIndex]
    apply Lp.ext
    filter_upwards [globalTestFunctionToWkpOn_coordinate_ae
      (p := p) (Ω := Ω) (TestFunction.sliceRight t Φ) (singleDerivIndex n j),
      toLpOfContCompact_coeFn (p := p) (Ω := Ω)
        (TestFunction.sliceRight t
          (TestFunction.lineDerivCLM ℝ (0, EuclideanSpace.single j (1 : ℝ)) Φ)).continuous
        (TestFunction.sliceRight t
          (TestFunction.lineDerivCLM ℝ (0, EuclideanSpace.single j (1 : ℝ)) Φ)).hasCompactSupport]
        with x hx hy
    rw [hx, hy, singleDerivIndex_toList]
    change (∂[j] (TestFunction.sliceRight t Φ).toFun) x = _
    rw [← TestFunction.lineDerivCLM_sliceRight,
      testFunction_lineDerivCLM_apply]
    rfl

variable [Fact (1 ≤ p)]

/-- The canonical spatial slices of a smooth compactly supported spacetime test form
a continuous W¹ᵖ curve, including at `p = ∞` and on unbounded spatial sets. -/
theorem continuous_globalTestFunctionToWkpOn_sliceRight
    (Φ : 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ)) :
    Continuous (fun t ↦ globalTestFunctionToWkpOn (k := 1) (p := p) (Ω := Ω)
      (TestFunction.sliceRight t Φ)) := by
  have hcoord (d : DerivIndex n 1) : Continuous (fun t ↦
      (globalTestFunctionToWkpOn (k := 1) (p := p) (Ω := Ω)
        (TestFunction.sliceRight t Φ) : WkpAmbientOn n 1 p Ω) d) := by
    simp_rw [globalTestFunctionToWkpOn_sliceRight_coordinate]
    exact continuous_iff_continuousAt.mpr fun t ↦
      (hasDerivAt_toLpOfContCompact_sliceRight (p := p) (Ω := Ω) _ t).continuousAt
  apply continuous_induced_rng.mpr
  exact (PiLp.continuous_toLp p _).comp (continuous_pi hcoord)

/-- The derivative of the base Lᵖ row of a spatial test slice is the base row of its
time derivative. This identifies the derivative in the Sobolev graph model. -/
theorem hasDerivAt_wkpBase_sliceRight
    (Φ : 𝓓((⊤ : Opens (ℝ × ℝ^n)), ℝ)) (t : ℝ) :
    HasDerivAt
      (fun s ↦ (globalTestFunctionToWkpOn (k := 1) (p := p) (Ω := Ω)
        (TestFunction.sliceRight s Φ) : WkpAmbientOn n 1 p Ω) (baseIndex n 1))
      ((globalTestFunctionToWkpOn (k := 1) (p := p) (Ω := Ω)
        (TestFunction.sliceRight t (TestFunction.lineDerivCLM ℝ (1, 0) Φ)) :
          WkpAmbientOn n 1 p Ω) (baseIndex n 1)) t := by
  simp_rw [globalTestFunctionToWkpOn_sliceRight_coordinate, firstOrderRows_baseIndex]
  exact hasDerivAt_toLpOfContCompact_sliceRight (p := p) (Ω := Ω) Φ t

end SobolevSpace.GraphSpace
