/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Area.Hausdorff
import PDE.Spaces.Sobolev.Boundary.Trace.C1.Area.PairedBounds

/-!
# Upper growth of surface measure in C¹ charts

The forward chart controls parameter distances by physical distances, and its
surface Jacobian is bounded. The area formula therefore bounds the surface measure
of a sufficiently small ball by a constant times the codimension-one power of its radius.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open Set Metric MeasureTheory Boundary.Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- Surface measure has codimension-one upper growth near every boundary point.
The constants are obtained from a chart through that point. -/
theorem exists_surfaceMeasure_closedBall_le (x : frontier Ω) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r < δ →
      (surfaceMeasure Ω).real (closedBall (x : ℝ^(m + 1)) r) ≤ A * r ^ m := by
  obtain ⟨i, hi⟩ := exists_chart_source_of_mem_frontier (Ω := Ω) x.property
  have himage : (x : ℝ^(m + 1)) ∈ chartBoundaryParametrization (Ω := Ω) i ''
      chartBoundaryParameterDomain (Ω := Ω) i := by
    rw [image_chartBoundaryParametrization i]
    exact ⟨hi, x.property⟩
  obtain ⟨a, ha, hx⟩ := himage
  obtain ⟨L, hL, hdist⟩ := exists_chartBoundaryParametrization_lower_bound (Ω := Ω) i
  obtain ⟨M, hM, hJac⟩ := exists_chartBoundaryJacobian_bound (Ω := Ω) i
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (hΩ.chart i).open_source x hi
  refine ⟨M * L ^ m * volume.real (closedBall (0 : ℝ^m) 1), by positivity,
    δ, hδ, ?_⟩
  intro r hr hrδ
  let S := closedBall (x : ℝ^(m + 1)) r
  let B := closedBall a (L * r)
  let D := chartBoundaryParameterDomain (Ω := Ω) i
  let P := chartBoundaryParametrization (Ω := Ω) i
  let J := chartBoundaryJacobian (Ω := Ω) i
  let g : ℝ^(m + 1) → ℝ := S.indicator (fun _ ↦ 1)
  have hS : MeasurableSet S := measurableSet_closedBall
  have hB : MeasurableSet B := measurableSet_closedBall
  have hsub : S ⊆ (hΩ.chart i).source :=
    (closedBall_subset_ball hrδ).trans hball
  have hg : Measurable g := measurable_const.indicator hS
  have hmeasure : (surfaceMeasure Ω).real S =
      ∫ b in D, J b * g (P b) := by
    calc
      _ = ∫ z, g z ∂surfaceMeasure Ω := by
        simp only [g, integral_indicator_const (1 : ℝ) hS, smul_eq_mul, mul_one]
      _ = ∫ z in (hΩ.chart i).source, g z ∂surfaceMeasure Ω := by
        simp only [g, integral_indicator_const (1 : ℝ) hS, smul_eq_mul, mul_one,
          measureReal_restrict_apply hS, inter_eq_self_of_subset_left hsub]
      _ = _ := by
        simpa only [D, J, P, smul_eq_mul] using
          integral_surfaceMeasure_restrict_chartSource i g hg.aestronglyMeasurable
  have hmajorant : Integrable (B.indicator (fun _ : ℝ^m ↦ M)) := by
    have hconst : IntegrableOn (fun _ : ℝ^m ↦ M) B :=
      integrableOn_const (isCompact_closedBall a (L * r)).measure_ne_top
    exact hconst.integrable_indicator hB
  have hnonneg (b : ℝ^m) (hb : b ∈ D) : 0 ≤ J b * g (P b) := by
    apply mul_nonneg (chartBoundaryJacobian_pos i hb).le
    exact indicator_nonneg (fun _ _ ↦ zero_le_one) _
  have hbound (b : ℝ^m) (hb : b ∈ D) :
      J b * g (P b) ≤ B.indicator (fun _ : ℝ^m ↦ M) b := by
    by_cases hs : P b ∈ S
    · have hbB : b ∈ B := by
        have h := hdist b hb a ha
        rw [hx] at h
        exact h.trans (mul_le_mul_of_nonneg_left (mem_closedBall.mp hs) (by linarith))
      rw [show g (P b) = 1 from indicator_of_mem hs _, indicator_of_mem hbB, mul_one]
      exact (Real.le_norm_self _).trans (hJac b hb)
    · rw [show g (P b) = 0 from indicator_of_notMem hs _, mul_zero]
      exact indicator_nonneg (fun _ _ ↦ hM) _
  rw [hmeasure]
  calc
    _ ≤ ∫ b in D, B.indicator (fun _ : ℝ^m ↦ M) b :=
      setIntegral_mono_of_nonneg hnonneg hbound hmajorant.integrableOn
    _ ≤ ∫ b, B.indicator (fun _ : ℝ^m ↦ M) b :=
      setIntegral_le_integral hmajorant (Filter.Eventually.of_forall
        (fun b ↦ indicator_nonneg (fun _ _ ↦ hM) b))
    _ = M * volume.real B := by rw [integral_indicator_const M hB]; simp [smul_eq_mul, mul_comm]
    _ = (M * L ^ m * volume.real (closedBall (0 : ℝ^m) 1)) * r ^ m := by
      rw [Measure.addHaar_real_closedBall' volume a (by positivity : 0 ≤ L * r),
        finrank_euclideanSpace_fin, mul_pow]
      ring

end SobolevSpace.Trace.C1
