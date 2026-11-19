/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.C1.Flattening
public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Operator

/-!
# Banach-valued traces on domains with a finite C¹ extension atlas

Localize a first-order Sobolev function by the finite boundary partition, flatten each piece,
take its half-space trace, and transport the resulting boundary class to surface measure.
The finite sum is a continuous linear trace for every finite exponent at least one.

For any ambient C¹ representative of the physical base, the resulting surface class is
literal boundary restriction. The chart cutoffs supply compact support, so the ambient
representative need not be compactly supported. The target is any complete real normed
space, and tangential dimension zero is included.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.C1

open Boundary.Geometry.SurfaceMeasure
open GraphSpace
open SobolevSpace.Trace.C1 (chartPhysicalization norm_chartPhysicalization_apply_le
  chartSurfaceBound)
open SobolevSpace.Trace.HalfSpace (normalSlice)

variable {m : ℕ} {Ω : Opens ℝ^(m + 1)}
  [hΩ : Boundary.C1ExtensionAtlas (m + 1) (Ω : Set ℝ^(m + 1))]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Lifting the tangential boundary value gives the flat surface class of the
localized chart representative. -/
theorem liftLp_flattenedClassicalPiece (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (i : Fin hΩ.N) {f : ℝ^(m + 1) → F} (hf : ContDiff ℝ 1 f) :
    liftLp p (HalfSpace.smoothBoundaryLp
      (flattenedClassicalPiece_contDiff i hf).continuous
      (flattenedClassicalPiece_hasCompactSupport i f)) =
        (flattenedClassicalPiece_memLp p i hf).toLp (flattenedClassicalPiece i f) := by
  apply Lp.ext
  have hcomp := (measurePreserving_flatProjection (n := m)).quasiMeasurePreserving.ae
    (HalfSpace.smoothBoundaryLp_coeFn_ae (p := p)
      (flattenedClassicalPiece_contDiff i hf).continuous
      (flattenedClassicalPiece_hasCompactSupport i f))
  have hflat : ∀ᵐ x ∂flatSurfaceMeasure (n := m), x (Fin.last m) = 0 := by
    have hm : MeasurableSet {x : ℝ^(m + 1) | x (Fin.last m) = 0} := by
      rw [← frontier_upperHalfSpace]
      exact isClosed_frontier.measurableSet
    exact ae_restrict_mem hm
  filter_upwards [liftLp_apply_ae p (HalfSpace.smoothBoundaryLp
    (flattenedClassicalPiece_contDiff i hf).continuous
    (flattenedClassicalPiece_hasCompactSupport i f)), hcomp, hflat,
    (flattenedClassicalPiece_memLp p i hf).coeFn_toLp] with x hlift hcomp hx hrep
  rw [hlift, hcomp, hrep]
  change flattenedClassicalPiece i f (flatEmbedding (flatProjection x)) =
    flattenedClassicalPiece i f x
  rw [flatEmbedding_flatProjection_of_last_eq_zero hx]

variable [CompleteSpace F] {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- The trace of one boundary partition piece, transported to physical surface measure. -/
def localPhysicalTrace (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p)
    (i : Fin hΩ.N) :
    W^{1,ENNReal.ofReal p}(Ω; F) →L[ℝ]
      Lp F (ENNReal.ofReal p) (surfaceMeasure (Ω : Set ℝ^(m + 1))) :=
  (chartPhysicalization (ENNReal.ofReal p) i).comp
    ((liftLp (ENNReal.ofReal p)).toContinuousLinearMap.comp
      ((HalfSpace.traceLp m p hp).comp (localizedFlatten i)))

/-- The chartwise Sobolev trace of a C¹ representative equals its classical surface class. -/
theorem localPhysicalTrace_c1 (hp : 1 ≤ p) (i : Fin hΩ.N)
    (U : W^{1,ENNReal.ofReal p}(Ω; F)) {f : ℝ^(m + 1) → F}
    (hf : ContDiff ℝ 1 f)
    (hU : (U.val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)
      =ᵐ[domainMeasure (m + 1) Ω] f) :
    localPhysicalTrace p hp i U =
      chartPhysicalization (ENNReal.ofReal p) i
        ((flattenedClassicalPiece_memLp (ENNReal.ofReal p) i hf).toLp
          (flattenedClassicalPiece i f)) := by
  change chartPhysicalization (ENNReal.ofReal p) i
    (liftLp (ENNReal.ofReal p) (HalfSpace.traceLp m p hp (localizedFlatten i U))) = _
  rw [HalfSpace.traceLp_c1 hp _ (flattenedClassicalPiece_contDiff i hf)
    (flattenedClassicalPiece_hasCompactSupport i f) (localizedFlatten_base_ae i U hU),
    liftLp_flattenedClassicalPiece (ENNReal.ofReal p) i hf]

/-- The chart measure distortion, flat trace estimate and localized flattening norm
control the physical trace of one piece. -/
theorem norm_localPhysicalTrace_apply_le (hp : 1 ≤ p) (i : Fin hΩ.N)
    (U : W^{1,ENNReal.ofReal p}(Ω; F)) :
    ‖localPhysicalTrace p hp i U‖ ≤
      (chartSurfaceBound i : ℝ) ^ (1 / ENNReal.ofReal p).toReal *
        p ^ (1 / p) * ‖localizedFlatten (p := ENNReal.ofReal p) (F := F) i‖ * ‖U‖ := by
  have hC : 0 ≤ (chartSurfaceBound i : ℝ) ^ (1 / ENNReal.ofReal p).toReal :=
    Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hp0 : 0 ≤ p ^ (1 / p) := Real.rpow_nonneg (zero_le_one.trans hp) _
  calc
    ‖localPhysicalTrace p hp i U‖ ≤
        (chartSurfaceBound i : ℝ) ^ (1 / ENNReal.ofReal p).toReal *
          ‖liftLp (ENNReal.ofReal p)
            (HalfSpace.traceLp m p hp (localizedFlatten i U))‖ :=
      norm_chartPhysicalization_apply_le _ i _
    _ = (chartSurfaceBound i : ℝ) ^ (1 / ENNReal.ofReal p).toReal *
        ‖HalfSpace.traceLp m p hp (localizedFlatten i U)‖ := by
      rw [(liftLp (ENNReal.ofReal p)).norm_map]
    _ ≤ (chartSurfaceBound i : ℝ) ^ (1 / ENNReal.ofReal p).toReal *
        (p ^ (1 / p) * ‖localizedFlatten i U‖) :=
      mul_le_mul_of_nonneg_left (HalfSpace.norm_traceLp_apply_le hp _) hC
    _ ≤ (chartSurfaceBound i : ℝ) ^ (1 / ENNReal.ofReal p).toReal *
        (p ^ (1 / p) * (‖localizedFlatten (p := ENNReal.ofReal p) (F := F) i‖ * ‖U‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ((localizedFlatten i).le_opNorm U) hp0) hC
    _ = _ := by ring

/-- The finite-atlas trace from the Banach-valued Sobolev graph to surface `Lp`. -/
def traceLp (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p) :
    W^{1,ENNReal.ofReal p}(Ω; F) →L[ℝ]
      Lp F (ENNReal.ofReal p) (surfaceMeasure (Ω : Set ℝ^(m + 1))) :=
  ∑ i : Fin hΩ.N, localPhysicalTrace p hp i

/-- The trace equals the physical boundary values of an ambient C¹ representative.
Only agreement of the Sobolev base on the domain is required. -/
theorem traceLp_coeFn_ae (hp : 1 ≤ p) (U : W^{1,ENNReal.ofReal p}(Ω; F))
    {f : ℝ^(m + 1) → F} (hf : ContDiff ℝ 1 f)
    (hU : (U.val (baseIndex (m + 1) 1) : ℝ^(m + 1) → F)
      =ᵐ[domainMeasure (m + 1) Ω] f) :
    (traceLp p hp U : ℝ^(m + 1) → F)
      =ᵐ[surfaceMeasure (Ω : Set ℝ^(m + 1))] f := by
  have hsum : traceLp p hp U =
      ∑ i : Fin hΩ.N, chartPhysicalization (ENNReal.ofReal p) i
        ((flattenedClassicalPiece_memLp (ENNReal.ofReal p) i hf).toLp
          (flattenedClassicalPiece i f)) := by
    simp only [traceLp, sum_apply]
    exact Finset.sum_congr rfl fun i _ ↦ localPhysicalTrace_c1 hp i U hf hU
  rw [hsum]
  exact sum_chartPhysicalization_flattenedClassicalPiece (ENNReal.ofReal p) hf

/-- The finite sum of the chartwise coefficients bounds the surface trace norm. -/
theorem norm_traceLp_apply_le (hp : 1 ≤ p) (U : W^{1,ENNReal.ofReal p}(Ω; F)) :
    ‖traceLp p hp U‖ ≤
      (∑ i : Fin hΩ.N, (chartSurfaceBound i : ℝ) ^ (1 / ENNReal.ofReal p).toReal *
        p ^ (1 / p) * ‖localizedFlatten (p := ENNReal.ofReal p) (F := F) i‖) * ‖U‖ := by
  calc
    ‖traceLp p hp U‖ ≤ ∑ i : Fin hΩ.N, ‖localPhysicalTrace p hp i U‖ := by
      simp only [traceLp, sum_apply]
      exact norm_sum_le _ _
    _ ≤ ∑ i : Fin hΩ.N, (chartSurfaceBound i : ℝ) ^ (1 / ENNReal.ofReal p).toReal *
        p ^ (1 / p) * ‖localizedFlatten (p := ENNReal.ofReal p) (F := F) i‖ * ‖U‖ :=
      Finset.sum_le_sum fun i _ ↦ norm_localPhysicalTrace_apply_le hp i U
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- A bound for the operator norm of the physical trace by a finite sum of atlas-dependent
chart constants. -/
theorem norm_traceLp_le (hp : 1 ≤ p) :
    ‖traceLp (Ω := Ω) (F := F) p hp‖ ≤
      ∑ i : Fin hΩ.N, (chartSurfaceBound i : ℝ) ^ (1 / ENNReal.ofReal p).toReal *
        p ^ (1 / p) * ‖localizedFlatten (p := ENNReal.ofReal p) (F := F) i‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg
      (mul_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)
        (Real.rpow_nonneg (zero_le_one.trans hp) _))
      (norm_nonneg (localizedFlatten (p := ENNReal.ofReal p) (F := F) i))
  · intro U
    exact norm_traceLp_apply_le hp U

end SobolevSpace.VectorValued.Trace.C1
