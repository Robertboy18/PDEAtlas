/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.InverseSquareBounds
public import PDE.Analysis.MeasureTheory.Measure.WeightedSublevel
public import PDE.Parabolic.Heat.Nonlinear.Absorption.Ball
public import PDE.Parabolic.Heat.Nonlinear.PositiveTimeLowerBound
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.DistanceBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Uniform negative weighted moments from distance barriers

The universal inverse-time bound and the interior distance barrier control the
negative part. Linear collar volume growth then gives a uniform weighted moment.
-/

@[expose] public noncomputable section

open Filter Set
open PDE (laplacian)
open scoped Topology

open MeasureTheory

namespace HeatEquation.Nonlinear

/-- On a bounded C1 domain with a linear distance-collar volume bound, the
negative weighted moment of a signed quadratic heat solution stays bounded
as time approaches zero. No bound at the original corner is assumed. -/
theorem exists_uniform_negative_moment_of_collar_bound
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {u : ℝ → ℝ^n → ℝ}
    {w : ℝ^n → ℝ} {C : ℝ}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hb : Bornology.IsBounded Ω)
    (hgraph : SobolevSpace.Boundary.HasC1GraphBoundary Ω)
    (hw : SobolevSpace.ContDiffUpToBoundary 1 w Ω)
    (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 ≤ w x)
    (hC : 0 < C)
    (hlayer : ∀ r > 0,
      volume.real {x : ℝ^n | x ∈ Ω ∧ Metric.infDist x Ωᶜ ≤ r} ≤ C * r)
    (hc0 : ContinuousOn u.uncurry (Ici 0 ×ˢ Ω))
    (hc : ContinuousOn u.uncurry (Ioi 0 ×ˢ closure Ω))
    (hs : ContDiffOn ℝ 2 u.uncurry (Ioi 0 ×ˢ Ω))
    (heq : ∀ t > 0, ∀ x ∈ Ω,
      deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2)
    (hboundary : ∀ x ∈ frontier Ω, ∀ t > 0, u t x = 0)
    (hinit : ∀ x ∈ Ω, 0 ≤ u 0 x) :
    ∃ K > 0, ∀ t > 0, (∫ x in Ω, w x * max (-u t x) 0) ≤ K := by
  let : Nonempty (Fin n) := ⟨⟨0, Fact.out⟩⟩
  have hcompl : Ωᶜ.Nonempty := Set.nonempty_compl.mpr fun h ↦
    hb.isCompact_closure.ne_univ (by rw [h, closure_univ])
  obtain ⟨L, hL, hwL⟩ := hw.exists_norm_le_mul_infDist_compl hΩ hb hgraph hwc hwzero
  let ν : Measure (ℝ^n) := volume.restrict Ω
  let μ : Measure (ℝ^n) := ν.withDensity (fun x ↦ ENNReal.ofReal (w x))
  let : IsFiniteMeasure ν := ⟨by simpa [ν] using hb.measure_lt_top (μ := volume)⟩
  have hwi : Integrable w ν :=
    (hwc.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hwi.hasFiniteIntegral
  have hac : μ ≪ ν := withDensity_absolutelyContinuous _ _
  have hmemν : ∀ᵐ x ∂ν, x ∈ Ω := ae_restrict_mem hΩ.measurableSet
  have hmem : ∀ᵐ x ∂μ, x ∈ Ω := hac.ae_le hmemν
  have hwposν : 0 ≤ᵐ[ν] w := hmemν.mono fun x hx ↦ hwpos x hx
  have hI (f : ℝ^n → ℝ) : (∫ x, f x ∂μ) = ∫ x in Ω, w x * f x := by
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hwi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [hwposν] with x hx
    simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]
  let d : ℝ^n → ℝ := fun x ↦ Metric.infDist x Ωᶜ
  have hdmeas : Measurable d := (Metric.continuous_infDist_pt _).measurable
  have hdpos : ∀ᵐ x ∂μ, 0 < d x := hmem.mono fun x hx ↦
    (hΩ.isClosed_compl.notMem_iff_infDist_pos hcompl).mp (not_not.mpr hx)
  have hvol (r : ℝ) (hr : 0 < r) : ν.real {x | d x ≤ r} ≤ C * r := by
    rw [measureReal_restrict_apply (measurableSet_le hdmeas measurable_const)]
    convert hlayer r hr using 1
    congr 1
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, and_comm, d]
  have hwbound : ∀ᵐ x ∂ν, w x ≤ L * d x := hmemν.mono fun x hx ↦
    (le_abs_self _).trans (hwL x hx)
  have hgrowth (r : ℝ) (hr : 0 < r) : μ.real {x | d x ^ 2 ≤ r} ≤ (L * C) * r :=
    measureReal_withDensity_sq_sublevel_le hwi hwposν hL.le hr hdmeas hwbound hvol
  let D : ℝ := 16 * (4 * (n : ℝ) + 40) ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨2 * (L * C) * Real.sqrt D, by positivity, fun t ht ↦ ?_⟩
  have huc : ContinuousOn (u t) (closure Ω) :=
    hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun x hx ↦ ⟨ht, hx⟩)
  obtain ⟨B, hB⟩ := hb.isCompact_closure.exists_bound_of_continuousOn huc
  have huLp : MemLp (u t) 2 μ :=
    MemLp.of_bound (AEStronglyMeasurable.mono_ac hac
      ((huc.mono subset_closure).aestronglyMeasurable hΩ.measurableSet)) B
      (hmem.mono fun x hx ↦ hB x (subset_closure hx))
  have hceiling : ∀ᵐ x ∂μ, max (-u t x) 0 ≤ 1 / t := by
    filter_upwards [hmem] with x hx
    have hp := neg_one_le_time_mul_of_global_dirichlet_square_solution
      hΩ hne hb hc hs heq hboundary ht (subset_closure hx)
    refine max_le ((le_div_iff₀ ht).mpr ?_) (by positivity)
    nlinarith only [hp]
  have henv : ∀ᵐ x ∂μ, max (-u t x) 0 ≤ D * t / (d x ^ 2) ^ 2 := by
    filter_upwards [hmem] with x hx
    have hp := neg_le_infDist_bound_of_square_equation hΩ hcompl
      (hc0.mono (prod_mono Icc_subset_Ici_self Subset.rfl)) hs heq hinit
      ⟨ht.le, le_rfl⟩ hx
    apply max_le _ (div_nonneg (mul_nonneg hD.le ht.le) (sq_nonneg _))
    simpa only [D, d, ← pow_mul] using hp
  have hbound := integral_le_of_time_inverse_sq_bounds
    (huLp.neg_part.integrable (by norm_num))
    (Eventually.of_forall fun x ↦ le_max_right (-u t x) 0) hD ht hceiling
    (hdpos.mono fun x hx ↦ pow_pos hx 2) henv hgrowth
  rwa [hI] at hbound

end HeatEquation.Nonlinear
