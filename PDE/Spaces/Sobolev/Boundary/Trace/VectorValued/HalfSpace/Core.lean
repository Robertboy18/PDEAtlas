/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.Normal
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Boundary values of normed-valued compact functions

Evaluation at normal coordinate zero gives the boundary function on `ℝ^n`.
For a continuous compactly supported function its boundary restriction belongs to
every `Lp` space, including `L∞`. These constructions require no completeness of
the codomain and include the zero-dimensional boundary.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SobolevSpace.VectorValued.Trace.HalfSpace

open SobolevSpace.Trace.HalfSpace

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F]
  {f : ℝ^(n + 1) → F}

/-- Evaluation on the boundary preserves continuity. -/
theorem boundaryValue_continuous (hf : Continuous f) :
    Continuous (fun y : ℝ^n ↦ normalSlice f y 0) :=
  (normalSlice_product_continuous hf).comp (continuous_id.prodMk continuous_const)

/-- The support of the boundary restriction lies in the tangential projection
of the ambient compact support. The ambient support may meet the boundary. -/
theorem boundaryValue_hasCompactSupport (hfc : HasCompactSupport f) :
    HasCompactSupport (fun y : ℝ^n ↦ normalSlice f y 0) := by
  let K : Set (ℝ^n) :=
    (fun x : ℝ^(n + 1) ↦ (splitTangentialNormal x).1) '' tsupport f
  have hproj : Continuous (fun x : ℝ^(n + 1) ↦ (splitTangentialNormal x).1) :=
    continuous_fst.comp (tangentialNormalContinuousLinearEquiv (n := n)).continuous
  apply HasCompactSupport.intro (hfc.image hproj : IsCompact K)
  intro y hy
  by_contra hne
  apply hy
  exact ⟨joinTangentialNormal (y, 0), subset_tsupport _ hne, by simp⟩

/-- A compact continuous boundary value belongs to every `Lp` space. -/
theorem boundaryValue_memLp (hf : Continuous f) (hfc : HasCompactSupport f)
    (p : ℝ≥0∞) :
    MemLp (fun y : ℝ^n ↦ normalSlice f y 0) p volume :=
  (boundaryValue_continuous hf).memLp_of_hasCompactSupport
    (boundaryValue_hasCompactSupport hfc)

/-- The `Lp` class of the boundary restriction of a compact continuous function. -/
def smoothBoundaryLp {p : ℝ≥0∞} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Lp F p (volume : Measure (ℝ^n)) :=
  (boundaryValue_memLp hf hfc p).toLp (fun y ↦ normalSlice f y 0)

/-- The boundary `Lp` class represents evaluation at normal coordinate zero. -/
theorem smoothBoundaryLp_coeFn_ae {p : ℝ≥0∞}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    (smoothBoundaryLp (p := p) hf hfc : ℝ^n → F) =ᵐ[volume]
      fun y ↦ normalSlice f y 0 :=
  (boundaryValue_memLp hf hfc p).coeFn_toLp

end SobolevSpace.VectorValued.Trace.HalfSpace
