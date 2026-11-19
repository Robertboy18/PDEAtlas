/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.FiniteExponentCompactSupport

/-!
# Intrinsic finite-exponent flat traces

For `1 ≤ p`, we lift the tangential finite-exponent trace to the
intrinsic Hausdorff surface measure on the flat boundary hyperplane.
In particular, `p = 1` gives a bounded `W^{1,1} → L¹` trace with norm at most
one and almost-everywhere classical agreement on compactly supported `C¹` functions.
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace
namespace Boundary.Geometry.SurfaceMeasure

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {n : ℕ}

/-- For `1 ≤ p`, the flat trace valued intrinsically in surface-measure `L^p`
on the boundary hyperplane. -/
noncomputable def flatTraceLp (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)] :
    W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1)) →L[ℝ]
      MeasureTheory.Lp ℝ (ENNReal.ofReal p)
        (flatSurfaceMeasure (n := n)) :=
  (liftLp (n := n) (ENNReal.ofReal p)).toContinuousLinearMap.comp
    (Trace.HalfSpace.traceLp n p (ENNReal.one_le_ofReal.mp Fact.out))

/-- The intrinsic finite-exponent flat trace has the same quantitative bound
as its tangential-coordinate form. -/
theorem norm_flatTraceLp_le (n : ℕ) (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (u : W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1))) :
    ‖flatTraceLp n p u‖ ≤ p ^ (1 / p) * ‖u‖ := by
  change ‖liftLp (n := n) (ENNReal.ofReal p)
      (Trace.HalfSpace.traceLp n p (ENNReal.one_le_ofReal.mp Fact.out) u)‖ ≤ _
  rw [LinearIsometry.norm_map]
  exact Trace.HalfSpace.norm_traceLp_le n p (ENNReal.one_le_ofReal.mp Fact.out) u

/-- Intrinsic hyperplane form of the compact-`C1` finite-exponent trace
agreement theorem. -/
theorem flatTraceLp_c1 (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (f : Trace.HalfSpace.CompactSupport.c1CompactSubmodule n) :
    flatTraceLp n p
        (Trace.HalfSpace.CompactSupport.toUpperW1p p f) =
      (liftLp (n := n) (ENNReal.ofReal p)).toContinuousLinearMap
        (Trace.HalfSpace.CompactSupport.boundaryLpLinear p f) := by
  simp only [flatTraceLp, ContinuousLinearMap.comp_apply]
  rw [Trace.HalfSpace.CompactSupport.traceLp_c1 p (ENNReal.one_le_ofReal.mp Fact.out)]

/-- On the flat hyperplane, the finite-exponent trace of a compactly
supported `C¹` function agrees almost everywhere with that function. -/
theorem flatTraceLp_c1_apply_ae (p : ℝ)
    [Fact (1 ≤ ENNReal.ofReal p)]
    (f : Trace.HalfSpace.CompactSupport.c1CompactSubmodule n) :
    (flatTraceLp n p
        (Trace.HalfSpace.CompactSupport.toUpperW1p p f) :
      ℝ^(n + 1) → ℝ) =ᵐ[flatSurfaceMeasure (n := n)]
      (f : ℝ^(n + 1) → ℝ) := by
  rw [flatTraceLp_c1 p]
  have hlift := liftLp_apply_ae (n := n) (ENNReal.ofReal p)
    (Trace.HalfSpace.CompactSupport.boundaryLpLinear p f)
  have hboundary :=
    (measurePreserving_flatProjection (n := n)).quasiMeasurePreserving.ae
      (Trace.HalfSpace.CompactSupport.boundaryLpLinear_apply_ae p f)
  have hflatMeas : MeasurableSet
      {x : ℝ^(n + 1) | x (Fin.last n) = 0} := by
    rw [← frontier_upperHalfSpace (n := n)]
    exact isClosed_frontier.measurableSet
  have hmem : ∀ᵐ x ∂flatSurfaceMeasure (n := n),
      x (Fin.last n) = 0 := by
    simpa [flatSurfaceMeasure] using
      (MeasureTheory.ae_restrict_mem
        (μ := Measure.euclideanHausdorffMeasure n)
        (s := {x : ℝ^(n + 1) | x (Fin.last n) = 0})
        hflatMeas)
  filter_upwards [hlift, hboundary, hmem] with x hxlift hxboundary hxflat
  change ((liftLp (n := n) (ENNReal.ofReal p)
    (Trace.HalfSpace.CompactSupport.boundaryLpLinear p f) :
      MeasureTheory.Lp ℝ (ENNReal.ofReal p)
        (flatSurfaceMeasure (n := n))) :
      ℝ^(n + 1) → ℝ) x = (f : ℝ^(n + 1) → ℝ) x
  rw [hxlift, hxboundary]
  simp only [Trace.HalfSpace.smoothBoundaryValue,
    Trace.HalfSpace.normalSlice]
  change (f : ℝ^(n + 1) → ℝ)
      (flatEmbedding (flatProjection x)) =
      (f : ℝ^(n + 1) → ℝ) x
  rw [flatEmbedding_flatProjection_of_last_eq_zero hxflat]

end Boundary.Geometry.SurfaceMeasure
end SobolevSpace
