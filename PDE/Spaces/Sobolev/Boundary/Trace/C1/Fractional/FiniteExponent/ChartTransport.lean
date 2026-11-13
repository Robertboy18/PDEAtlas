/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.ChartTrace

/-!
# Prepared chart transport at general exponents

The target cutoff is one on the localized boundary data. After chart pullback, a
source cutoff extends the field to the whole space before restriction to the domain.
These auxiliary cutoffs do not apply the boundary partition a second time.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1.Fractional.FiniteExponent

open MeasureTheory Set
open Boundary.Geometry.SurfaceMeasure
open Boundary.C1ExtensionAtlas.DerivedCutoffs Extension.C1.BoundaryPiece
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- Transport a whole-space Sobolev field through one auxiliary chart and restrict to the domain. -/
def chartTransport (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin hΩ.N) :
    W^{1,p}(ℝ^(m + 1)) →L[ℝ] W^{1,p}(Ω) :=
  (GraphSpace.restrictCLM hΩ.isOpen.measurableSet (subset_univ _)).comp
    ((preparedChartCLM (p := p) i).comp
      (GraphSpace.restrictCLM (hΩ.chart i).open_target.measurableSet (subset_univ _)))

/-- Multiplication by the auxiliary target cutoff on flat boundary values. -/
def flatTargetCutoff (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin hΩ.N) :
    Lp ℝ p (flatSurfaceMeasure (n := m)) →L[ℝ] Lp ℝ p (flatSurfaceMeasure (n := m)) :=
  let η := targetSupportCutoff (Ω := Ω) i
  let hη := η.contDiff.continuous.memLp_top_of_hasCompactSupport
    η.hasCompactSupport (flatSurfaceMeasure (n := m))
  (ContinuousLinearMap.mul ℝ ℝ).holderL (flatSurfaceMeasure (n := m)) ∞ p p (hη.toLp η.toFun)

/-- The flat auxiliary cutoff has the literal multiplication representative. -/
theorem flatTargetCutoff_apply_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin hΩ.N)
    (v : Lp ℝ p (flatSurfaceMeasure (n := m))) :
    (flatTargetCutoff p i v : ℝ^(m + 1) → ℝ) =ᵐ[flatSurfaceMeasure (n := m)]
      fun y ↦ (targetSupportCutoff (Ω := Ω) i).toFun y * v y := by
  let η := targetSupportCutoff (Ω := Ω) i
  let hη := η.contDiff.continuous.memLp_top_of_hasCompactSupport
    η.hasCompactSupport (flatSurfaceMeasure (n := m))
  filter_upwards [(ContinuousLinearMap.mul ℝ ℝ).coeFn_holder
    (r := p) (hη.toLp η.toFun) v, hη.coeFn_toLp] with y hy hηy
  exact hy.trans (congrArg (· * v y) hηy)

/-- Whole-space representatives are transported by the prepared chart map almost everywhere. -/
theorem chartTransport_base_apply_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] (i : Fin hΩ.N)
    (u : W^{1,p}((univ : Set (ℝ^(m + 1))))) {f : ℝ^(m + 1) → ℝ}
    (hu : GraphSpace.baseRepresentative u =ᵐ[domainMeasure (m + 1) univ] f) :
    GraphSpace.baseRepresentative (chartTransport p i u) =ᵐ[domainMeasure (m + 1) Ω]
      chartTransportRepresentative i f := by
  let uT : W^{1,p}((hΩ.chart i).target) :=
    GraphSpace.restrictCLM (hΩ.chart i).open_target.measurableSet (subset_univ _) u
  have huT : GraphSpace.baseRepresentative uT
      =ᵐ[domainMeasure (m + 1) (hΩ.chart i).target] f :=
    (GraphSpace.restrictCLM_apply_ae (hΩ.chart i).open_target.measurableSet
      (subset_univ _) u (GraphSpace.baseIndex (m + 1) 1)).trans
        (hu.filter_mono (ae_mono (GraphSpace.domainMeasure_le (subset_univ _))))
  have hp := preparedChartCLM_base_apply_ae p i uT huT
  exact (GraphSpace.restrictCLM_apply_ae hΩ.isOpen.measurableSet (subset_univ _)
    (preparedChartCLM (p := p) i uT) (GraphSpace.baseIndex (m + 1) 1)).trans
      (hp.filter_mono (ae_mono (GraphSpace.domainMeasure_le (subset_univ _))))

/-- The auxiliary target cutoff fixes data already localized by the boundary partition. -/
theorem flatTargetCutoff_lift_localizedBoundaryCoordinates
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (i : Fin hΩ.N) (g : Lp ℝ p (surfaceMeasure Ω)) :
    flatTargetCutoff p i (liftLp p (localizedBoundaryCoordinates p i g)) =
      liftLp p (localizedBoundaryCoordinates p i g) := by
  apply Lp.ext
  filter_upwards [
    flatTargetCutoff_apply_ae p i (liftLp p (localizedBoundaryCoordinates p i g)),
    liftLp_localizedBoundaryCoordinates_apply_ae p i g
  ] with y hmul hcoords
  rw [hmul, hcoords]
  by_cases hyT : y ∈ (hΩ.chart i).target
  · rw [indicator_of_mem hyT]
    by_cases hψ : (hΩ.boundaryCutoff i).toFun ((hΩ.chart i).symm y) = 0
    · simp [hψ]
    · have hη := targetSupportCutoff_eq_one_on_boundarySupportInTarget i y
        ⟨(hΩ.chart i).symm y, subset_tsupport _ hψ, (hΩ.chart i).right_inv hyT⟩
      rw [hη, one_mul]
  · rw [indicator_of_notMem hyT, mul_zero]

end SobolevSpace.Trace.C1.Fractional.FiniteExponent
