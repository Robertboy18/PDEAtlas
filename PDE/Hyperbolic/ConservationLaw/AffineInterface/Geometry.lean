/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import PDE.Common.Euclidean
import Mathlib.Tactic.Positivity.Finset

/-!
# Geometry of affine interfaces

For a speed `s`, `leftHalfSpace s` is the open spacetime region `x < s t`, and
`interface s` parametrizes its boundary by `t ↦ (t, s t)`. We prove
the elementary topological and scaling properties used by weak conservation-law
calculations.
-/

@[expose] public section

namespace PDE.Hyperbolic.ConservationLaw.AffineInterface

noncomputable section

open PDE.Common
open TopologicalSpace

/-- The open spacetime region strictly to the left of the line `x = s t`. -/
def leftHalfSpace (s : ℝ) : Set ℝ^2 := {x : ℝ^2 | x 1 < s * x 0}

/-- The region strictly to the left of an affine interface is open. -/
theorem isOpen_leftHalfSpace (s : ℝ) : IsOpen (leftHalfSpace s) :=
  isOpen_lt (PiLp.continuous_apply _ _ 1) (continuous_const.mul (PiLp.continuous_apply _ _ 0))

/-- The region strictly to the left of an affine interface is measurable. -/
theorem measurableSet_leftHalfSpace (s : ℝ) : MeasurableSet (leftHalfSpace s) :=
  (isOpen_leftHalfSpace s).measurableSet

/-- Positive spacetime dilation preserves each affine half-space through the
origin. -/
theorem smul_mem_leftHalfSpace_iff {a s : ℝ} (ha : 0 < a) (p : ℝ^2) :
    a • p ∈ leftHalfSpace s ↔ p ∈ leftHalfSpace s := by
  change a * p 1 < s * (a * p 0) ↔ p 1 < s * p 0
  rw [mul_left_comm s a (p 0), mul_lt_mul_iff_of_pos_left ha]

/-- Parametrization of the spacetime line `x = s t`. -/
def interface (s : ℝ) (t : ℝ) : ℝ^2 := !₂[t, s * t]

/-- The time coordinate of the affine interface is its parameter. -/
@[simp]
theorem interface_time (s t : ℝ) : interface s t 0 = t := by
  simp [interface]

/-- The spatial coordinate of the affine interface is `s * t`. -/
@[simp]
theorem interface_space (s t : ℝ) : interface s t 1 = s * t := by
  simp [interface]

private theorem continuous_mkX {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun t : ℝ ↦ (!₂[f t, g t] : ℝ^2) := by
  fun_prop

/-- The affine-interface parametrization is continuous. -/
theorem continuous_interface (s : ℝ) : Continuous (interface s) :=
  continuous_mkX continuous_id (continuous_const.mul continuous_id)

/-- The affine-interface parametrization is a closed embedding. -/
theorem isClosedEmbedding_interface (s : ℝ) :
    Topology.IsClosedEmbedding (interface s) := by
  have hleft :
      Function.LeftInverse (fun x : ℝ^2 ↦ x 0) (interface s) := by
    intro t
    simp
  have hprojection : Continuous (fun x : ℝ^2 ↦ x 0) := by
    simpa using (EuclideanSpace.proj (0 : Fin 2)).continuous
  have hembedding : Topology.IsEmbedding (interface s) :=
    hleft.isEmbedding (hf := hprojection) (hg := continuous_interface s)
  have hrange :
      Set.range (interface s) = {x : ℝ^2 | x 1 = s * x 0} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      simp
    · intro hx
      refine ⟨x 0, ?_⟩
      ext i
      fin_cases i
      · simp
      · simpa using hx.symm
  have hclosed : IsClosed {x : ℝ^2 | x 1 = s * x 0} :=
    isClosed_eq (PiLp.continuous_apply _ _ 1) (continuous_const.mul (PiLp.continuous_apply _
        _ 0))
  exact ⟨hembedding, hrange ▸ hclosed⟩

end

end PDE.Hyperbolic.ConservationLaw.AffineInterface
