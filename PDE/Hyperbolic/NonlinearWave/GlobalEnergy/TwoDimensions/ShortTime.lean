/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.ThreeDimensions.ShortTime
public import PDE.Analysis.Calculus.CoordinateProjection

/-!
# Planar tails by constant-coordinate descent

A planar wave, extended to `ℝ³` independently of the last coordinate, solves the same
semilinear equation. The lifted Cauchy data have bounded jets although their supports
are unbounded cylinders, so the three-dimensional short-time bound applies. Projecting
the Kirchhoff spheres to the plane shows that the lifted free wave vanishes outside
the planar support enlarged by the elapsed time.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory PDE PDE.Analysis PDE.Common
open scoped Topology

namespace WaveEquation

/-- Dropping the last spatial coordinate preserves the time coordinate. -/
theorem coordinateProjection_timeSpaceCons {n : ℕ} (t : ℝ) (x : ℝ^(n + 1)) :
    coordinateProjection (timeSpaceCons t x) = timeSpaceCons t (coordinateProjection x) := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [coordinateProjection_apply]

/-- Lifting a field independently of the last spatial coordinate commutes with the wave
operator. -/
theorem waveOperator_coordinateProjection_timeSpaceCons {u : ℝ^3 → ℝ} (hu : ContDiff ℝ 2 u) (t : ℝ)
    (x : ℝ^3) :
    waveOperator (u ∘ coordinateProjection) (timeSpaceCons t x) =
      waveOperator u (timeSpaceCons t (coordinateProjection x)) := by
  rw [waveOperator_timeSpaceCons (hu.comp coordinateProjection.contDiff),
    waveOperator_timeSpaceCons hu]
  simp only [Function.comp_apply, coordinateProjection_timeSpaceCons]
  congr 1
  exact laplacian_comp_coordinateProjection (hu.comp (contDiff_timeSpaceCons_spatial 2 t)) x

/-- If the planar data `g` and `h` vanish outside the disk of radius `R`, the free wave
of their lifts to `ℝ³` vanishes at `(t, x)` whenever the projection of `x` lies outside
the disk of radius `R + t`. -/
theorem kirchhoffFormula_eq_zero_of_projected_support {g h : ℝ^2 → ℝ} {R t : ℝ}
    (hg : ContDiff ℝ 1 g) (hh : Continuous h) (hgs : tsupport g ⊆ Metric.closedBall 0 R)
    (hhs : tsupport h ⊆ Metric.closedBall 0 R) (ht : 0 ≤ t) (x : ℝ^3)
    (hx : R + t < ‖coordinateProjection x‖) :
    kirchhoffFormula (g ∘ coordinateProjection) (h ∘ coordinateProjection) x t = 0 := by
  have hout (ω : Metric.sphere (0 : ℝ^3) 1) :
      R < ‖coordinateProjection (x + t • (ω : ℝ^3))‖ := by
    have hω : ‖(ω : ℝ^3)‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using ω.property
    have hdist : ‖coordinateProjection (x + t • (ω : ℝ^3)) -
        coordinateProjection x‖ ≤ t := by
      rw [← map_sub]
      exact (norm_coordinateProjection_apply_le _).trans
        (by simp only [add_sub_cancel_left, norm_smul, hω, mul_one,
          Real.norm_of_nonneg ht, le_refl])
    have hn := norm_le_norm_add_norm_sub (coordinateProjection (x + t • (ω : ℝ^3)))
      (coordinateProjection x)
    linarith
  have hnot {q : ℝ^2 → ℝ} (hq : tsupport q ⊆ Metric.closedBall 0 R)
      (ω : Metric.sphere (0 : ℝ^3) 1) :
      coordinateProjection (x + t • (ω : ℝ^3)) ∉ tsupport q := by
    intro hm
    have hb := hq hm
    exact (hout ω).not_ge (by simpa only [Metric.mem_closedBall, dist_zero_right] using hb)
  have hgzero (ω : Metric.sphere (0 : ℝ^3) 1) :
      (g ∘ coordinateProjection) (x + t • (ω : ℝ^3)) = 0 := by
    change g (coordinateProjection (x + t • (ω : ℝ^3))) = 0
    exact image_eq_zero_of_notMem_tsupport (hnot hgs ω)
  have hhzero (ω : Metric.sphere (0 : ℝ^3) 1) :
      (h ∘ coordinateProjection) (x + t • (ω : ℝ^3)) = 0 := by
    change h (coordinateProjection (x + t • (ω : ℝ^3))) = 0
    exact image_eq_zero_of_notMem_tsupport (hnot hhs ω)
  have hdzero (ω : Metric.sphere (0 : ℝ^3) 1) :
      fderiv ℝ (g ∘ coordinateProjection) (x + t • (ω : ℝ^3)) (ω : ℝ^3) = 0 := by
    rw [fderiv_comp _ (hg.differentiable one_ne_zero _)
      coordinateProjection.differentiableAt, fderiv_of_notMem_tsupport ℝ (hnot hgs ω)]
    simp
  rw [kirchhoffFormula_eq_mean_add_sphericalCauchyTrace
    (hg.comp coordinateProjection.contDiff) (hh.comp coordinateProjection.continuous)]
  simp only [unitSphereAverage, sphericalCauchyTrace, hgzero, hhzero, hdzero,
    add_zero, integral_zero, zero_div, mul_zero]

/-- A planar wave with compact Cauchy data has small tails on an initial
window, by the three-dimensional bound for bounded lifted initial jets. -/
theorem exists_pos_uniform_tail_of_compact_cauchy_two {u : ℝ^3 → ℝ} {f : ℝ → ℝ} {g h : ℝ^2 → ℝ}
    {b : ℝ} (hu : ContDiff ℝ 4 u) (hb : 0 < b) (hf : Continuous f) (hg : ContDiff ℝ 3 g)
    (hh : ContDiff ℝ 2 h) (hgc : HasCompactSupport g) (hhc : HasCompactSupport h)
    (hposition : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x, (∂[0] u) (timeSpaceCons 0 x) = h x)
    (hwave : ∀ t ∈ Ioo 0 b, ∀ x, waveOperator u (timeSpaceCons t x) + f (u (timeSpaceCons t x)) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∃ R : ℝ, ∀ t ∈ Icc 0 δ, ∀ x : ℝ^2, R < ‖x‖ → ‖u (timeSpaceCons t x)‖ < ε := by
  let U : ℝ^4 → ℝ := u ∘ coordinateProjection
  have hU : ContDiff ℝ 4 U := hu.comp coordinateProjection.contDiff
  obtain ⟨G, hG⟩ := hg.continuous.bounded_above_of_compact_support hgc
  obtain ⟨K, hK⟩ := (hg.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hgc.fderiv ℝ)
  obtain ⟨B, hB⟩ := hh.continuous.bounded_above_of_compact_support hhc
  have hKlift (x : ℝ^3) : ‖fderiv ℝ (g ∘ coordinateProjection) x‖ ≤ K := by
    rw [fderiv_comp _ (hg.differentiable (by norm_num) _) coordinateProjection.differentiableAt,
      coordinateProjection.fderiv]
    calc
      _ ≤ ‖fderiv ℝ g (coordinateProjection x)‖ * ‖coordinateProjection (n := 2)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ g (coordinateProjection x)‖ * 1 :=
        mul_le_mul_of_nonneg_left norm_coordinateProjection_le (norm_nonneg _)
      _ ≤ K := by rw [mul_one]; exact hK _
  have hpos (x : ℝ^3) : U (timeSpaceCons 0 x) = (g ∘ coordinateProjection) x := by
    simp only [U, Function.comp_apply, coordinateProjection_timeSpaceCons, hposition]
  have hvel (x : ℝ^3) : (∂[0] U) (timeSpaceCons 0 x) = (h ∘ coordinateProjection) x := by
    change (∂[(0 : Fin 3).castSucc] (u ∘ coordinateProjection)) (timeSpaceCons 0 x) = _
    rw [partialDeriv_comp_coordinateProjection (hu.differentiable (by norm_num))]
    simp only [Function.comp_apply, coordinateProjection_timeSpaceCons, hinitial]
  have hw (t : ℝ) (ht : t ∈ Ioo 0 b) (x : ℝ^3) :
      waveOperator U (timeSpaceCons t x) + f (U (timeSpaceCons t x)) = 0 := by
    rw [show waveOperator U (timeSpaceCons t x) =
      waveOperator u (timeSpaceCons t (coordinateProjection x)) from
        waveOperator_coordinateProjection_timeSpaceCons (hu.of_le (by norm_num)) t x]
    simpa only [U, Function.comp_apply, coordinateProjection_timeSpaceCons] using
      hwave t ht (coordinateProjection x)
  obtain ⟨d, hd, A, hA, _, herr⟩ := exists_pos_amplitude_and_retarded_bound_three
    (a := -1) hU.contDiffOn (by norm_num) hb hf
    (hg.comp coordinateProjection.contDiff) (hh.comp coordinateProjection.contDiff)
    hpos hvel (fun x ↦ hG (coordinateProjection x)) hKlift (fun x ↦ hB (coordinateProjection x)) hw
  have hnear : ∀ᶠ r : ℝ in 𝓝 0, r ^ 2 * A / 2 < ε := by
    have hc : Continuous (fun r : ℝ ↦ r ^ 2 * A / 2) := by fun_prop
    exact hc.continuousAt.eventually (gt_mem_nhds (by simpa using hε))
  have hright : ∀ᶠ r : ℝ in 𝓝[>] 0, r ^ 2 * A / 2 < ε := nhdsWithin_le_nhds hnear
  have htime : ∀ᶠ r : ℝ in 𝓝[>] 0, r < d := nhdsWithin_le_nhds (gt_mem_nhds hd.1)
  obtain ⟨δ, ⟨hδsmall, hδd⟩, hδ⟩ := ((hright.and htime).and eventually_mem_nhdsWithin).exists
  have hδpos : 0 < δ := hδ
  obtain ⟨R, hR⟩ := (hgc.isCompact.union hhc.isCompact).isBounded.subset_closedBall (0 : ℝ^2)
  refine ⟨δ, hδpos, R + δ, ?_⟩
  intro t ht x hx
  have hzero := kirchhoffFormula_eq_zero_of_projected_support
    (hg.of_le (by norm_num)) hh.continuous
    (fun _ hy ↦ hR (Or.inl hy)) (fun _ hy ↦ hR (Or.inr hy)) ht.1 (coordinateInclusion x)
    (by rw [coordinateProjection_coordinateInclusion]; linarith [ht.2])
  have he := herr t ⟨ht.1, ht.2.trans hδd.le⟩ (coordinateInclusion x)
  rw [hzero, sub_zero] at he
  have hfinal := he.trans_lt ((div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.1 ht.2 2) hA)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_lt hδsmall)
  simpa only [U, Function.comp_apply, coordinateProjection_timeSpaceCons,
    coordinateProjection_coordinateInclusion] using hfinal

end WaveEquation
