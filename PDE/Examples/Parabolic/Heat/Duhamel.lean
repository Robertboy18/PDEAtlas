/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.DuhamelClassical.ClassicalSolution.SpatialJets.ForwardTime
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A heat source that switches off

Multiply a smooth spatial bump by `max 0 (1 - t)`. This source is nonzero initially
and vanishes from time one onward. Its time dependence has a corner, but its spatial
derivatives remain continuous. Duhamel's formula still gives a classical heat solution:
the forward-time theorem needs spatial regularity and continuity of the source.
-/

@[expose] public section

open Set PDE.Common
open scoped Topology

namespace PDE.Examples.HeatDuhamel

variable {n : ℕ}

/-- A compact spatial heat source whose strength decreases linearly to zero at time one. -/
noncomputable def shutdownSource (φ : ContDiffBump (0 : ℝ^n)) (p : ℝ^(n + 1)) : ℝ :=
  max 0 (1 - p 0) * φ (spatialPart p)

/-- In time-space coordinates the source separates into its temporal and spatial factors. -/
theorem shutdownSource_timeSpaceCons (φ : ContDiffBump (0 : ℝ^n)) (t : ℝ) (x : ℝ^n) :
    shutdownSource φ (timeSpaceCons t x) = max 0 (1 - t) * φ x := by
  simp [shutdownSource]

/-- The forcing is nonzero at the initial time, even though the solution starts from zero. -/
theorem shutdownSource_initial_origin (φ : ContDiffBump (0 : ℝ^n)) :
    shutdownSource φ (timeSpaceCons 0 0) = 1 := by
  rw [shutdownSource_timeSpaceCons,
    φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le)]
  norm_num

/-- The source has completely switched off by time one. -/
theorem shutdownSource_after_one (φ : ContDiffBump (0 : ℝ^n)) (t : ℝ) (ht : 1 ≤ t)
    (x : ℝ^n) : shutdownSource φ (timeSpaceCons t x) = 0 := by
  rw [shutdownSource_timeSpaceCons, max_eq_left (sub_nonpos.mpr ht), zero_mul]

/-- The source produces a classical forced heat solution through its switching time,
with zero initial data and a uniform initial trace. No temporal derivative of the source
is required. This also applies in zero spatial dimensions. -/
theorem shutdownSource_classical (φ : ContDiffBump (0 : ℝ^n)) :
    Continuous (fun p : ℝ^n × ℝ ↦ HeatEquation.nonhomogeneousSolution (shutdownSource φ) p.1 p.2) ∧
    ContDiffOn ℝ 1
      (fun p : ℝ^n × ℝ ↦ HeatEquation.nonhomogeneousSolution (shutdownSource φ) p.1 p.2)
      (univ ×ˢ Ioi 0) ∧
    (∀ t : ℝ, ContDiff ℝ 2 (fun x ↦ HeatEquation.nonhomogeneousSolution (shutdownSource φ) x t)) ∧
    (∀ i j : Fin n, Continuous (fun p : ℝ^n × ℝ ↦
      (∂[i] (∂[j]
        (fun x ↦ HeatEquation.nonhomogeneousSolution (shutdownSource φ) x p.2))) p.1)) ∧
    (∀ (x : ℝ^n) (t : ℝ), 0 < t →
      deriv (fun τ ↦ HeatEquation.nonhomogeneousSolution (shutdownSource φ) x τ) t -
        laplacian (fun y ↦ HeatEquation.nonhomogeneousSolution (shutdownSource φ) y t) x =
          max 0 (1 - t) * φ x) ∧
    (∀ x : ℝ^n, HeatEquation.nonhomogeneousSolution (shutdownSource φ) x 0 = 0) ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (x : ℝ^n) (t : ℝ), 0 < t → t < δ →
        |HeatEquation.nonhomogeneousSolution (shutdownSource φ) x t| < ε := by
  have htime : Continuous (fun p : Ici (0 : ℝ) × ℝ^n ↦ max 0 (1 - (p.1 : ℝ))) := by
    fun_prop
  have hsource : Continuous
      (fun p : Ici (0 : ℝ) × ℝ^n ↦ shutdownSource φ (timeSpaceCons p.1 p.2)) := by
    simp_rw [shutdownSource_timeSpaceCons]
    exact htime.mul (φ.continuous.comp continuous_snd)
  have hslice (s : ℝ) : ContDiff ℝ 2
      (fun x ↦ shutdownSource φ (timeSpaceCons s x)) := by
    simp_rw [shutdownSource_timeSpaceCons]
    exact contDiff_const.mul φ.contDiff
  have hcompact : HasCompactSupport
      (fun p : Ici (0 : ℝ) × ℝ^n ↦ shutdownSource φ (timeSpaceCons p.1 p.2)) := by
    let a : Ici (0 : ℝ) := ⟨0, by simp⟩
    let b : Ici (0 : ℝ) := ⟨1, by simp⟩
    have htimeCompact : IsCompact (Icc a b) :=
      isClosed_Ici.isClosedEmbedding_subtypeVal.isCompact_preimage
        (show IsCompact (Icc (0 : ℝ) 1) from isCompact_Icc)
    refine HasCompactSupport.intro (htimeCompact.prod φ.hasCompactSupport.isCompact) ?_
    intro p hp
    change p ∉ (Icc a b ×ˢ tsupport (φ : ℝ^n → ℝ)) at hp
    simp only [shutdownSource_timeSpaceCons]
    by_cases ht : (p.1 : ℝ) ≤ 1
    · have hx : p.2 ∉ tsupport (φ : ℝ^n → ℝ) := fun hx ↦
        hp ⟨⟨p.1.property, ht⟩, hx⟩
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
    · rw [max_eq_left (by linarith), zero_mul]
  have hfirst (i : Fin n) : Continuous
      (fun p : Ici (0 : ℝ) × ℝ^n ↦
        (∂[i] (fun x ↦ shutdownSource φ (timeSpaceCons p.1 x))) p.2) := by
    simp only [shutdownSource_timeSpaceCons, ← smul_eq_mul, partialDeriv_const_smul]
    exact htime.smul ((contDiff_partialDeriv_of_succ
      (φ.contDiff : ContDiff ℝ 1 φ)).continuous.comp continuous_snd)
  have hsecond (i j : Fin n) : Continuous
      (fun p : Ici (0 : ℝ) × ℝ^n ↦ (∂[i]
        (∂[j] (fun x ↦ shutdownSource φ (timeSpaceCons p.1 x)))) p.2) := by
    simp only [shutdownSource_timeSpaceCons, ← smul_eq_mul]
    change Continuous (fun p : Ici (0 : ℝ) × ℝ^n ↦ (∂[i]
      (fun x ↦ (∂[j] (fun y ↦ max 0 (1 - (p.1 : ℝ)) • φ y)) x)) p.2)
    simp_rw [partialDeriv_const_smul]
    have hfirst : ContDiff ℝ 1 (∂[j] (φ : ℝ^n → ℝ)) :=
      contDiff_partialDeriv_of_succ (φ.contDiff : ContDiff ℝ 2 φ)
    exact htime.smul ((contDiff_partialDeriv_of_succ hfirst).continuous.comp continuous_snd)
  simpa only [shutdownSource_timeSpaceCons] using
    HeatEquation.nonhomogeneousSolution_regularity_of_forward_spatial_jets
      (shutdownSource φ) hsource (fun s _ ↦ hslice s) hcompact hfirst hsecond

end PDE.Examples.HeatDuhamel
