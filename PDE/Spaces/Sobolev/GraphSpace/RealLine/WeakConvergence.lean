/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.RealLine.Representative
public import PDE.Spaces.Sobolev.GraphSpace.Topology.SupportedBall
public import PDE.Spaces.Sobolev.GraphSpace.Operators.WeakConvergence

/-!
# Recovering an H¹ limit from real L² convergence

A uniform H¹ bound supplies weak compactness of the derivative coordinate.
Strong convergence of the real L² base then identifies a unique limiting
Sobolev graph. Thus the whole family converges weakly in H¹; no convergence
of the derivative norms is required. Point evaluation is continuous
on H¹, so the real representatives converge at every fixed point.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology Sobolev

namespace SobolevSpace.GraphSpace

/-- A uniform H¹ bound and strong convergence of the real base coordinates
construct an H¹ graph for the limiting L² class, with the same norm bound. -/
theorem exists_h1_of_tendsto_realLineCoordinate
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (u : ι → W^{1,2}(ℝ^1)) (f : Lp ℝ 2 (volume : Measure ℝ)) {B : ℝ}
    (hbound : ∀ i, ‖u i‖ ≤ B)
    (hbase : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (u i))
      l (𝓝 f)) :
    ∃ U : W^{1,2}(ℝ^1), ‖U‖ ≤ B ∧
      realLineCoordinateCLM (baseIndex 1 1) U = f := by
  have hbase' : Tendsto (fun i ↦ wkpBaseCoordinateCLM (u i)) l
      (𝓝 (oneDimensionalPullbackL2 f)) := by
    have h := (oneDimensionalPullbackL2.continuous.tendsto f).comp hbase
    simpa only [Function.comp_def, wkpBaseCoordinateCLM, realLineCoordinateCLM,
      ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap,
      oneDimensionalPullbackL2_pushforward] using h
  obtain ⟨U, hU, hUf⟩ := exists_hk_of_tendsto_base u _ hbound hbase'
  refine ⟨U, hU, ?_⟩
  change oneDimensionalPushforwardL2 (wkpCoordinateCLM (baseIndex 1 1) U) = f
  simp only [wkpBaseCoordinateCLM] at hUf
  rw [hUf, oneDimensionalPushforwardL2_pullback]

/-- A uniformly bounded H¹ family converges weakly to its constructed
limit whenever its real L² base converges strongly. -/
theorem tendsto_weak_h1_of_realLineCoordinate
    {ι : Type*} {l : Filter ι} (u : ι → W^{1,2}(ℝ^1)) (U : W^{1,2}(ℝ^1))
    {B : ℝ} (hbound : ∀ i, ‖u i‖ ≤ B)
    (hbase : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (u i))
      l (𝓝 (realLineCoordinateCLM (baseIndex 1 1) U))) :
    Tendsto (fun i ↦ toWeakSpace ℝ (W^{1,2}(ℝ^1)) (u i)) l
      (𝓝 (toWeakSpace ℝ (W^{1,2}(ℝ^1)) U)) := by
  have hbounded : Bornology.IsBounded (range u) := by
    apply isBounded_iff_forall_norm_le.mpr
    exact ⟨B, by rintro _ ⟨i, rfl⟩; exact hbound i⟩
  apply tendsto_weak_hk_of_base isOpen_univ u U hbounded
  have hbase' : Tendsto (fun i ↦ wkpBaseCoordinateCLM (u i)) l
      (𝓝 (wkpBaseCoordinateCLM U)) := by
    have h := (oneDimensionalPullbackL2.continuous.tendsto
      (realLineCoordinateCLM (baseIndex 1 1) U)).comp hbase
    simpa only [Function.comp_def, wkpBaseCoordinateCLM, realLineCoordinateCLM,
      ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap,
      oneDimensionalPullbackL2_pushforward] using h
  exact (toWeakSpaceCLM ℝ (DerivLp 1 2 univ)).continuous.continuousAt.tendsto.comp hbase'

/-- Every coordinate, including the first weak derivative, converges
weakly when a bounded H¹ family's real base converges strongly. -/
theorem tendsto_weak_realLineCoordinate_of_h1_bound
    {ι : Type*} {l : Filter ι} (u : ι → W^{1,2}(ℝ^1)) (U : W^{1,2}(ℝ^1))
    {B : ℝ} (hbound : ∀ i, ‖u i‖ ≤ B)
    (hbase : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (u i))
      l (𝓝 (realLineCoordinateCLM (baseIndex 1 1) U)))
    (j : DerivIndex 1 1) :
    Tendsto
      (fun i ↦ toWeakSpace ℝ (Lp ℝ 2 (volume : Measure ℝ)) (realLineCoordinateCLM j (u i)))
      l (𝓝 (toWeakSpace ℝ (Lp ℝ 2 (volume : Measure ℝ)) (realLineCoordinateCLM j U))) := by
  have hweak := tendsto_weak_h1_of_realLineCoordinate u U hbound hbase
  exact ((WeakSpace.map (realLineCoordinateCLM j)).continuous.tendsto
    (toWeakSpace ℝ (W^{1,2}(ℝ^1)) U)).comp hweak

/-- Bounded H¹ families with strongly convergent real L² bases converge at every real point. -/
theorem tendsto_realLineRepresentative_eval_of_L2_tendsto
    {ι : Type*} {l : Filter ι} {u : ι → W^{1,2}(ℝ^1)} {U : W^{1,2}(ℝ^1)}
    {B : ℝ} (hbound : ∀ i, ‖u i‖ ≤ B)
    (hbase : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (u i)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) U))) (x : ℝ) :
    Tendsto (fun i ↦ realLineRepresentative (u i) x) l (𝓝 (realLineRepresentative U x)) := by
  exact PDE.Analysis.WeakCompactness.tendsto_evaluation
    (tendsto_weak_h1_of_realLineCoordinate u U hbound hbase) (realLineRepresentativeEvalCLM x)

/-- A fixed trace shared eventually by a bounded H¹ family survives its strong L² limit. -/
theorem realLineRepresentative_limit_value_of_L2_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → W^{1,2}(ℝ^1)} {U : W^{1,2}(ℝ^1)} {B x c : ℝ}
    (hbound : ∀ i, ‖u i‖ ≤ B)
    (hbase : Tendsto (fun i ↦ realLineCoordinateCLM (baseIndex 1 1) (u i)) l
      (𝓝 (realLineCoordinateCLM (baseIndex 1 1) U)))
    (htrace : ∀ᶠ i in l, realLineRepresentative (u i) x = c) :
    realLineRepresentative U x = c :=
  tendsto_nhds_unique (tendsto_realLineRepresentative_eval_of_L2_tendsto hbound hbase x)
    (tendsto_const_nhds.congr' (EventuallyEq.symm htrace))

end SobolevSpace.GraphSpace
