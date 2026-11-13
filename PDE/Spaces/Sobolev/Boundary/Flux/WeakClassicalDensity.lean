/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Flux.WeakClassical
import PDE.Spaces.Sobolev.Boundary.Trace.C1.ContinuousRepresentative
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Identification of a classical weak-normal density

For second-order classical closure data, a surface density representing the
weak normal functional agrees almost everywhere with the outward completed
gradient flux.

We test against smooth compactly supported `g`. Their traces are their boundary values
(`trace_eq_ae_of_continuousOn`), `weakNormalTraceOfH2_toWkpSpaceOn_traceClass` evaluates the
functional on them, and Mathlib's `ae_eq_of_integral_contDiff_smul_eq` turns the equality of all
these integrals into equality almost everywhere for the surface measure.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open MeasureTheory Set GraphSpace Boundary.Geometry.SurfaceMeasure
open scoped Sobolev

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- Let `Ω` have a C¹ graph boundary and let `ContDiffUpToBoundary 2 f Ω`. If `q ∈ L²(∂Ω)`
satisfies `weakNormalTraceOfH2 f z = ∫_{∂Ω} q (boundaryValue z) dS` for every `z` in the trace
space, then `q` equals the normal flux `∂f/∂ν` of the completed gradient of `f` almost everywhere
for the surface measure. -/
theorem surfaceDensity_weakNormalTraceOfH2_ae_eq_normalFlux
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    {f : ℝ^(m + 1) → ℝ} (hf : ContDiffUpToBoundary 2 f Ω)
    (q : BoundaryL2 (Ω := Ω))
    (hq : ∀ z : HilbertTraceSpace (Ω := Ω),
      weakNormalTraceOfH2 (hf.toWkpSpaceOn hΩ.isOpen hΩ.bounded 2) z =
        ∫ y, q y * (boundaryValue z) y ∂surfaceMeasure Ω) :
    (q : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω]
      normalFlux (Ω := Ω) (hf.of_le (show 1 ≤ 2 by omega)).completedGradient := by
  let hf₁ := hf.of_le (show 1 ≤ 2 by omega)
  obtain ⟨P⟩ := SobolevSpace.Approximation.UpToBoundary.exists_inwardPartition
    hΩ.isOpen hΩ.bounded (Boundary.hasC1Boundary_of_local_graph hgraph)
  refine ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp q).locallyIntegrable (by norm_num))
    (integrable_normalFlux (Ω := Ω)
      hf₁.continuous_completedGradient.continuousOn).locallyIntegrable ?_
  intro g hg _
  let hg₁ : ContDiffUpToBoundary 1 g Ω :=
    ContDiffUpToBoundary.of_contDiff (hg.of_le (by simp)) hΩ.bounded
  let V : H¹(Ω) := hg₁.toWkpSpaceOn hΩ.isOpen hΩ.bounded 2
  have htrace : (boundaryValue (traceClass V) : ℝ^(m + 1) → ℝ)
      =ᵐ[surfaceMeasure Ω] g := by
    change (trace V : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω] g
    exact trace_eq_ae_of_continuousOn P V hg.continuous.continuousOn
      (hg₁.toWkpSpaceOn_base_ae hΩ.isOpen hΩ.bounded 2)
  calc
    (∫ y, g y • q y ∂surfaceMeasure Ω) =
        ∫ y, q y * (boundaryValue (traceClass V)) y ∂surfaceMeasure Ω := by
      apply integral_congr_ae
      filter_upwards [htrace] with y hy
      simp only [hy, smul_eq_mul, mul_comm]
    _ = weakNormalTraceOfH2 (hf.toWkpSpaceOn hΩ.isOpen hΩ.bounded 2)
        (traceClass V) := (hq (traceClass V)).symm
    _ = ∫ y, g y * normalFlux (Ω := Ω) hf₁.completedGradient y ∂surfaceMeasure Ω :=
      weakNormalTraceOfH2_toWkpSpaceOn_traceClass hgraph hf hg₁ hg.continuous.continuousOn
    _ = ∫ y, g y • normalFlux (Ω := Ω) hf₁.completedGradient y ∂surfaceMeasure Ω := by
      simp only [smul_eq_mul]

end SobolevSpace.Trace.C1
