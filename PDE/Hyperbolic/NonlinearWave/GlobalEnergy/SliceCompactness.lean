/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.InitialCompactness
import PDE.FDeriv.PartialDeriv.Transforms

/-!
# Compact wave energy at each nonnegative time

Time translation applies compactness of the initial velocity at every forward time.
Together with compact displacement support and a normalized potential, this gives
compact support of the energy density on each slice.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE PDE.Common PDE.Analysis WaveEquation
open scoped Topology

namespace WaveEquation

/-- Time translation reuses the proved compact initial-velocity theorem. -/
theorem hasCompactSupport_velocity_at_nonneg_time {n : ℕ} [Fact (0 < n)] {V : ℝ → ℝ}
    {u : ℝ^(n + 1) → ℝ} (hV : ContDiff ℝ 1 V) (hu : ContDiff ℝ 3 u)
    (hwave : ∀ t, 0 < t → ∀ x, semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x))) {a : ℝ}
    (ha : 0 ≤ a) :
    HasCompactSupport (fun x : ℝ^n ↦ (∂[0] u) (timeSpaceCons a x)) := by
  let v : ℝ^(n + 1) → ℝ := fun p ↦ u (p + a • EuclideanSpace.single 0 1)
  have hv : ContDiff ℝ 3 v := hu.comp (contDiff_id.add contDiff_const)
  have hshift (t : ℝ) (x : ℝ^n) :
      timeSpaceCons t x + a • EuclideanSpace.single 0 1 = timeSpaceCons (t + a) x := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  have hw (t : ℝ) (ht : 0 < t) (x : ℝ^n) :
      waveOperator v (timeSpaceCons t x) + deriv V (v (timeSpaceCons t x)) = 0 := by
    simpa only [v, waveOperator, partialDeriv_comp_add_right, hshift,
      semilinearWaveOperator] using hwave (t + a) (add_pos_of_pos_of_nonneg ht ha) x
  have hc (t : ℝ) (ht : 0 ≤ t) :
      HasCompactSupport (fun x : ℝ^n ↦ v (timeSpaceCons t x)) := by
    simpa only [v, hshift] using hs (t + a) (add_nonneg ht ha)
  simpa only [v, partialDeriv_comp_add_right, hshift, zero_add] using
    hasCompactSupport_initial_velocity_of_compact_slices hV.continuous_deriv_one hv hw hc

/-- Energy is compact on each slice, including its kinetic term. -/
theorem hasCompactSupport_energy_at_nonneg_time
    {n : ℕ} [Fact (0 < n)] {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0) (hu : ContDiff ℝ 3 u)
    (hwave : ∀ t, 0 < t → ∀ x, semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (hs : ∀ t, 0 ≤ t → HasCompactSupport (fun x : ℝ^n ↦ u (timeSpaceCons t x)))
    {a : ℝ} (ha : 0 ≤ a) : HasCompactSupport (semilinearWaveSpatialEnergyDensity V u a) := by
  have hv := hasCompactSupport_velocity_at_nonneg_time hV hu hwave hs ha
  refine HasCompactSupport.intro ((hs a ha).isCompact.union hv.isCompact) fun x hx ↦ ?_
  have hxu : x ∉ tsupport (fun y : ℝ^n ↦ u (timeSpaceCons a y)) := fun hy ↦ hx (Or.inl hy)
  have hxv : x ∉ tsupport (fun y : ℝ^n ↦ (∂[0] u) (timeSpaceCons a y)) := fun hy ↦ hx (Or.inr hy)
  have hz := image_eq_zero_of_notMem_tsupport hxu
  have ht := image_eq_zero_of_notMem_tsupport hxv
  have hg : classicalWaveSpatialGradient u (timeSpaceCons a x) = 0 := by
    ext i
    change (∂[i.succ] u) (timeSpaceCons a x) = 0
    rw [← partialDeriv_timeSpaceCons_spatial i u a x
      ((hu.differentiable (by norm_num)).differentiableAt)]
    simp only [partialDeriv, fderiv_of_notMem_tsupport ℝ hxu, zero_apply]
  simp only [semilinearWaveSpatialEnergyDensity, semilinearWaveEnergyDensity,
    classicalWaveEnergyDensity, ht, hg, hz, hVzero, norm_zero,
    zero_pow (by decide : 2 ≠ 0), add_zero, mul_zero]

end WaveEquation
