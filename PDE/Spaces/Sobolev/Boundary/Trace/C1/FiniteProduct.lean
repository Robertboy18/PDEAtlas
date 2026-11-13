/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ZeroTrace

/-!
# Geometric traces of finite Sobolev systems

The scalar geometric trace and the Euclidean Lp equivalence give
the trace of a finite system. Equality of vector traces is exactly membership
of every component difference in the zero-boundary graph space.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open MeasureTheory GraphSpace Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Sobolev

variable {m n : ℕ} {Ω : Set (ℝ^(n + 1))}
  [Boundary.C1ExtensionAtlas (n + 1) Ω]
  (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

/-- The geometric vector trace, with the Euclidean target norm, obtained from
the scalar traces through the finite Lp equivalence. -/
def vectorTraceLp :
    (Fin m → W^{1,ENNReal.ofReal p}(Ω)) →L[ℝ]
      Lp (ℝ^m) (ENNReal.ofReal p) (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω) :=
  Lp.euclideanTuple.comp
    (ContinuousLinearMap.pi fun i ↦ (traceLp p).comp (ContinuousLinearMap.proj i))

/-- Equality of geometric vector traces is equivalent in both directions to
zero-boundary membership of the component differences. The target may be empty. -/
theorem vectorTraceLp_eq_iff_sub_mem_Wkp0
    (u g : Fin m → W^{1,ENNReal.ofReal p}(Ω)) :
    vectorTraceLp p u = vectorTraceLp p g ↔
      ∀ i, u i - g i ∈ wkp0SubmoduleOn
        (n := n + 1) (k := 1) (p := ENNReal.ofReal p) (Ω := Ω) := by
  have heq :
      vectorTraceLp p u = vectorTraceLp p g ↔
        (fun i ↦ traceLp p (u i)) = (fun i ↦ traceLp p (g i)) :=
    (Lp.euclideanTupleEquiv (n := m) (p := ENNReal.ofReal p)
      (μ := Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)).injective.eq_iff
  rw [heq, funext_iff]
  apply forall_congr'
  intro i
  rw [← sub_eq_zero, ← map_sub, traceLp_eq_zero_iff_mem_Wkp0]
  rfl

/-- The prescribed geometric trace class is exactly the affine
zero-boundary class through any one of its members. -/
theorem vectorTraceLp_eq_iff_sub_mem_Wkp0_of_trace
    {γ : Lp (ℝ^m) (ENNReal.ofReal p) (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)}
    (g : Fin m → W^{1,ENNReal.ofReal p}(Ω))
    (hg : vectorTraceLp p g = γ)
    (u : Fin m → W^{1,ENNReal.ofReal p}(Ω)) :
    vectorTraceLp p u = γ ↔
      ∀ i, u i - g i ∈ wkp0SubmoduleOn
        (n := n + 1) (k := 1) (p := ENNReal.ofReal p) (Ω := Ω) := by
  rw [← hg]
  exact vectorTraceLp_eq_iff_sub_mem_Wkp0 p u g

/-- A prescribed boundary function, interpreted almost everywhere for Hausdorff
surface measure, gives the same affine zero-trace class as any one of its
Sobolev realizations. No separate measurability or integrability premise on the
boundary function is needed. -/
theorem vectorTraceLp_ae_eq_iff_sub_mem_Wkp0_of_ae_eq
    {γ : ℝ^(n + 1) → ℝ^m}
    (g : Fin m → W^{1,ENNReal.ofReal p}(Ω))
    (hg : (vectorTraceLp p g : ℝ^(n + 1) → ℝ^m) =ᵐ[surfaceMeasure Ω] γ)
    (u : Fin m → W^{1,ENNReal.ofReal p}(Ω)) :
    (vectorTraceLp p u : ℝ^(n + 1) → ℝ^m) =ᵐ[surfaceMeasure Ω] γ ↔
      ∀ i, u i - g i ∈ wkp0SubmoduleOn
        (n := n + 1) (k := 1) (p := ENNReal.ofReal p) (Ω := Ω) := by
  rw [← vectorTraceLp_eq_iff_sub_mem_Wkp0 p u g]
  constructor
  · intro hu
    exact Lp.ext (hu.trans hg.symm)
  · intro hu
    rw [hu]
    exact hg

end SobolevSpace.Trace.C1
