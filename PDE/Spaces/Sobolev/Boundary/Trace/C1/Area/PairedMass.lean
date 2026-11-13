/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Area.PairedBounds
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Area.TangentPoisson
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Area.Hausdorff

/-!
# The actual paired-gradient mass on a C¹ boundary

In one chart through the base point, the area formula and a positive dilation
turn the surface integral into the rescaled parameter integral. The majorant
comes from actual chart geometry and normal separation. Dominated convergence
then identifies the local mass using the exact tangent Jacobian. The remaining
surface stays a fixed positive distance away, and its paired contribution is O(t).
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory PDE.Analysis PotentialTheory
open scoped Gradient Topology

namespace PotentialTheory

/-- The actual canonical gradient is measurable, including its total value at the pole. -/
theorem measurable_gradient_fundamentalSolution (n : ℕ) :
    Measurable (∇ (fundamentalSolution n)) :=
  (InnerProductSpace.toDual ℝ (ℝ^n)).symm.continuous.measurable.comp
    (measurable_fderiv ℝ (fundamentalSolution n))

/-- The actual paired normal-offset gradient is measurable in its integration variable. -/
theorem measurable_paired_gradient_fundamentalSolution (n : ℕ)
    (x ν : ℝ^n) (t : ℝ) :
    Measurable (fun y : ℝ^n ↦ ∇ (fundamentalSolution n) (x - t • ν - y) -
      ∇ (fundamentalSolution n) (x + t • ν - y)) := by
  exact ((measurable_gradient_fundamentalSolution n).comp
    (measurable_const.sub measurable_id)).sub
      ((measurable_gradient_fundamentalSolution n).comp
        (measurable_const.sub measurable_id))

end PotentialTheory

namespace SobolevSpace.Trace.C1

open Boundary.Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- On an actual chart through the base point, the paired gradient has limiting mass ν. -/
theorem tendsto_integral_chartBoundary_paired_gradient (hm : 1 ≤ m)
    (i : Fin hΩ.N) {a : ℝ^m} (ha : a ∈ chartBoundaryParameterDomain (Ω := Ω) i)
    (x : frontier Ω) (hx : chartBoundaryParametrization (Ω := Ω) i a = (x : ℝ^(m + 1))) :
    Tendsto (fun t : ℝ ↦ ∫ y in (hΩ.chart i).source,
      ∇ (fundamentalSolution (m + 1))
          ((x : ℝ^(m + 1)) - t • outwardUnitNormal (Ω := Ω) x - y) -
        ∇ (fundamentalSolution (m + 1))
          ((x : ℝ^(m + 1)) + t • outwardUnitNormal (Ω := Ω) x - y)
      ∂surfaceMeasure Ω) (𝓝[>] 0) (𝓝 (outwardUnitNormal (Ω := Ω) x)) := by
  let D := chartBoundaryParameterDomain (Ω := Ω) i
  let P := chartBoundaryParametrization (Ω := Ω) i
  let J := chartBoundaryJacobian (Ω := Ω) i
  let K : ℝ → ℝ^(m + 1) → ℝ^(m + 1) := fun t y ↦
    ∇ (fundamentalSolution (m + 1))
        ((x : ℝ^(m + 1)) - t • outwardUnitNormal (Ω := Ω) x - y) -
      ∇ (fundamentalSolution (m + 1))
        ((x : ℝ^(m + 1)) + t • outwardUnitNormal (Ω := Ω) x - y)
  let F : ℝ → ℝ^m → ℝ^(m + 1) := fun t v ↦
    D.indicator (fun b ↦ J b • (t ^ m • K t (P b))) (a + t • v)
  let G : ℝ^m → ℝ^(m + 1) := fun v ↦
    (J a * (2 / (unitSphereArea (m + 1) *
      ‖outwardUnitNormal (Ω := Ω) x - chartBoundaryTangentialDerivative i a v‖ ^
        (m + 1)))) • outwardUnitNormal (Ω := Ω) x
  have hD : MeasurableSet D := (isOpen_chartBoundaryParameterDomain i).measurableSet
  have hK (t : ℝ) : Measurable (K t) :=
    measurable_paired_gradient_fundamentalSolution (m + 1) x _ t
  have hF (t : ℝ) : Measurable (F t) := by
    apply Measurable.comp
      (Measurable.indicator _ hD) (by fun_prop : Measurable (fun v : ℝ^m ↦ a + t • v))
    apply (continuous_chartBoundaryJacobian i).measurable.smul
    simpa only [Function.comp_def, Pi.smul_def, P] using
      ((hK t).comp (contDiff_chartBoundaryParametrization i).continuous.measurable).const_smul
        (t ^ m)
  obtain ⟨C, hC, δ, hδ, hbound⟩ :=
    exists_chartBoundary_paired_gradient_rescale_bound hm i ha x hx
  have hmajorant : Integrable (fun v : ℝ^m ↦ C * ((1 + ‖v‖) ^ (m + 1))⁻¹) := by
    have hbase : Integrable (fun v : ℝ^m ↦ (1 + ‖v‖) ^ (-((m + 1 : ℕ) : ℝ))) :=
      integrable_one_add_norm (by simp)
    simpa only [Real.rpow_neg_natCast, zpow_neg, zpow_natCast] using hbase.const_mul C
  have hlimit (v : ℝ^m) : Tendsto (fun t : ℝ ↦ F t v) (𝓝[>] 0) (𝓝 (G v)) := by
    apply (tendsto_chartBoundary_paired_gradient_rescale hm i ha x hx v).congr'
    have hmem := (eventually_rescale_mem_chartBoundaryParameterDomain i ha v).filter_mono
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    filter_upwards [hmem] with t ht
    exact (indicator_of_mem ht
      (fun b ↦ chartBoundaryJacobian (Ω := Ω) i b • (t ^ m • K t (P b)))).symm
  have hmass : Tendsto (fun t : ℝ ↦ ∫ v, F t v) (𝓝[>] 0) (𝓝 (∫ v, G v)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun v : ℝ^m ↦ C * ((1 + ‖v‖) ^ (m + 1))⁻¹)
    · exact Eventually.of_forall (fun t ↦ (hF t).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
      apply ae_of_all
      intro v
      by_cases hv : a + t • v ∈ D
      · simpa only [F, indicator_of_mem hv, J, K, P] using hbound t ht htδ v hv
      · simp only [F, indicator_of_notMem hv, norm_zero]
        positivity
    · exact hmajorant
    · exact ae_of_all _ hlimit
  have hG : (∫ v, G v) = outwardUnitNormal (Ω := Ω) x := by
    simpa only [G, J, one_smul, mul_one, unitSphereArea_eq] using
      integral_chartBoundary_tangent_poisson_smul_normal i ha x hx (t := 1) zero_lt_one
  rw [hG] at hmass
  refine hmass.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  change (∫ v, F t v) = ∫ y in (hΩ.chart i).source, K t y ∂surfaceMeasure Ω
  rw [integral_surfaceMeasure_restrict_chartSource i (K t) (hK t).aestronglyMeasurable]
  have hscale := Measure.integral_comp_smul_of_nonneg volume
    (fun b : ℝ^m ↦ D.indicator (fun c ↦ J c • K t (P c)) (a + b)) t (hR := ht.le)
  simp only [finrank_euclideanSpace_fin, integral_add_left_eq_self,
    integral_indicator hD] at hscale
  have hFscale : F t = fun v ↦
      t ^ m • D.indicator (fun c ↦ J c • K t (P c)) (a + t • v) := by
    funext v
    by_cases hv : a + t • v ∈ D
    · simp only [F, indicator_of_mem hv]
      exact smul_comm _ _ _
    · simp only [F, indicator_of_notMem hv, smul_zero]
  rw [hFscale, integral_smul, hscale, smul_smul,
    mul_inv_cancel₀ (pow_ne_zero _ (ne_of_gt ht)), one_smul]

/-- The actual paired gradient is surface-integrable at every sufficiently small positive height. -/
theorem eventually_integrable_paired_gradient_fundamentalSolution (hm : 1 ≤ m)
    (x : frontier Ω) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, Integrable (fun y : ℝ^(m + 1) ↦
      ∇ (fundamentalSolution (m + 1))
          ((x : ℝ^(m + 1)) - t • outwardUnitNormal (Ω := Ω) x - y) -
        ∇ (fundamentalSolution (m + 1))
          ((x : ℝ^(m + 1)) + t • outwardUnitNormal (Ω := Ω) x - y))
      (surfaceMeasure Ω) := by
  obtain ⟨δ, hδ, hbound⟩ := exists_paired_gradient_fundamentalSolution_bound
    (Ω := Ω) (by omega : 2 ≤ m + 1) x
  let A : ℝ := 2 ^ (m + 2) * (((m + 1 : ℕ) : ℝ) + 1) / unitSphereArea (m + 1)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (by positivity) (unitSphereArea_pos (n := m + 1)).le
  have hfrontier : ∀ᵐ y ∂surfaceMeasure Ω, y ∈ frontier Ω :=
    ae_restrict_mem isClosed_frontier.measurableSet
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
  apply (integrable_const (A * t / t ^ (m + 1))).mono'
    (measurable_paired_gradient_fundamentalSolution (m + 1) x _ t).aestronglyMeasurable
  filter_upwards [hfrontier] with y hy
  exact (hbound t ht htδ y hy).trans
    (div_le_div_of_nonneg_left (mul_nonneg hA (le_of_lt ht)) (pow_pos ht _)
      (pow_le_pow_left₀ (le_of_lt ht) (le_add_of_nonneg_right (norm_nonneg _)) _))

/-- Outside any fixed neighborhood of the base point, the actual paired surface integral vanishes.
The proof bounds its norm by a fixed constant times the normal height. -/
theorem tendsto_setIntegral_paired_gradient_fundamentalSolution_compl (hm : 1 ≤ m)
    (x : frontier Ω) {s : Set ℝ^(m + 1)} (hs : IsOpen s) (hxs : (x : ℝ^(m + 1)) ∈ s) :
    Tendsto (fun t : ℝ ↦ ∫ y in sᶜ,
      ∇ (fundamentalSolution (m + 1))
          ((x : ℝ^(m + 1)) - t • outwardUnitNormal (Ω := Ω) x - y) -
        ∇ (fundamentalSolution (m + 1))
          ((x : ℝ^(m + 1)) + t • outwardUnitNormal (Ω := Ω) x - y)
      ∂surfaceMeasure Ω) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hs x hxs
  obtain ⟨δ, hδ, hbound⟩ := exists_paired_gradient_fundamentalSolution_bound
    (Ω := Ω) (by omega : 2 ≤ m + 1) x
  let A : ℝ := 2 ^ (m + 2) * (((m + 1 : ℕ) : ℝ) + 1) / unitSphereArea (m + 1)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg (by positivity) (unitSphereArea_pos (n := m + 1)).le
  have hfrontier : ∀ᵐ y ∂surfaceMeasure Ω, y ∈ frontier Ω :=
    ae_restrict_mem isClosed_frontier.measurableSet
  have hzero : Tendsto (fun t : ℝ ↦ A * t / r ^ (m + 1) * (surfaceMeasure Ω).real sᶜ)
      (𝓝[>] 0) (𝓝 0) := by
    have htend : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
    simpa only [mul_zero, zero_div, zero_mul] using
      ((htend.const_mul A).div_const (r ^ (m + 1))).mul_const ((surfaceMeasure Ω).real sᶜ)
  apply squeeze_zero_norm' _ hzero
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with t ht htδ
  apply norm_setIntegral_le_of_norm_le_const_ae (by finiteness)
  filter_upwards [ae_restrict_of_ae hfrontier,
    ae_restrict_mem hs.measurableSet.compl] with y hy hys
  have hrDist : r ≤ ‖(x : ℝ^(m + 1)) - y‖ := by
    by_contra h
    apply hys (hball _)
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using lt_of_not_ge h
  exact (hbound t ht htδ y hy).trans
    (div_le_div_of_nonneg_left (mul_nonneg hA (le_of_lt ht)) (pow_pos hr _)
      (pow_le_pow_left₀ hr.le (hrDist.trans (le_add_of_nonneg_left (le_of_lt ht))) _))

/-- The actual inward-minus-outward fundamental-gradient surface mass tends to the outward normal.
The local chart mass and the distant contribution are both derived from the operational C¹ atlas. -/
theorem tendsto_integral_paired_gradient_fundamentalSolution (hm : 1 ≤ m)
    (x : frontier Ω) :
    Tendsto (fun t : ℝ ↦ ∫ y : ℝ^(m + 1),
      ∇ (fundamentalSolution (m + 1))
          ((x : ℝ^(m + 1)) - t • outwardUnitNormal (Ω := Ω) x - y) -
        ∇ (fundamentalSolution (m + 1))
          ((x : ℝ^(m + 1)) + t • outwardUnitNormal (Ω := Ω) x - y)
      ∂surfaceMeasure Ω) (𝓝[>] 0) (𝓝 (outwardUnitNormal (Ω := Ω) x)) := by
  obtain ⟨i, hi⟩ := exists_chart_source_of_mem_frontier (Ω := Ω) x.property
  have himage : (x : ℝ^(m + 1)) ∈ chartBoundaryParametrization (Ω := Ω) i ''
      chartBoundaryParameterDomain (Ω := Ω) i := by
    rw [image_chartBoundaryParametrization i]
    exact ⟨hi, x.property⟩
  obtain ⟨a, ha, hx⟩ := himage
  have hlocal := tendsto_integral_chartBoundary_paired_gradient hm i ha x hx
  have hfar := tendsto_setIntegral_paired_gradient_fundamentalSolution_compl hm x
    (hΩ.chart i).open_source hi
  have hsum := hlocal.add hfar
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_integrable_paired_gradient_fundamentalSolution hm x] with t ht
  exact integral_add_compl (hΩ.chart i).open_source.measurableSet ht

end SobolevSpace.Trace.C1
