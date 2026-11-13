/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity.Finset

/-!
# Uniform completion from an initial-data and forcing estimate

An energy estimate controls the distance between two trajectories by the distances
between their initial data and loads. Convergent data therefore give a uniformly
convergent sequence of trajectories, and evaluation preserves the initial value.

The parameter space can be a closed time interval. No extension of a trajectory or
coefficient outside that interval is used. The final estimate compares limits obtained
from different approximation sequences.
-/

@[expose] public section

noncomputable section

open Filter
open scoped BoundedContinuousFunction Topology

namespace PDE.Analysis.Evolution

variable {T H Y : Type*} [TopologicalSpace T] [MetricSpace H] [MetricSpace Y]

/-- A squared stability estimate makes trajectories Cauchy in the uniform metric when
both their initial data and their loads are Cauchy. Completeness is not needed here. -/
theorem cauchySeq_of_initial_forcing_sq_stability
    {x : ℕ → H} {f : ℕ → Y} {u : ℕ → T →ᵇ H}
    (hx : CauchySeq x) (hf : CauchySeq f) {K : ℝ} (hK : 0 ≤ K)
    (hstable : ∀ i j t,
      dist (u i t) (u j t) ^ 2 ≤ K * (dist (x i) (x j) ^ 2 +
        dist (f i) (f j) ^ 2)) :
    CauchySeq u := by
  have hlinear (i j : ℕ) :
      dist (u i) (u j) ≤ (√K + 1) *
        (dist (x i) (x j) + dist (f i) (f j)) := by
    apply (BoundedContinuousFunction.dist_le (by positivity)).2
    intro t
    have hsquare :
        dist (u i t) (u j t) ^ 2 ≤
          (√K * (dist (x i) (x j) + dist (f i) (f j))) ^ 2 := by
      calc
        _ ≤ K * (dist (x i) (x j) ^ 2 + dist (f i) (f j) ^ 2) :=
          hstable i j t
        _ ≤ K * (dist (x i) (x j) + dist (f i) (f j)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hK
          nlinarith only [mul_nonneg
            (dist_nonneg : 0 ≤ dist (x i) (x j))
            (dist_nonneg : 0 ≤ dist (f i) (f j))]
        _ = _ := by rw [mul_pow, Real.sq_sqrt hK]
    have hroot := (sq_le_sq₀ dist_nonneg (by positivity)).1 hsquare
    exact hroot.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right zero_le_one) (add_nonneg dist_nonneg dist_nonneg))
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hM : 0 < √K + 1 := by positivity
  have hδ : 0 < ε / (2 * (√K + 1)) := by positivity
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hx _ hδ
  obtain ⟨M, hM'⟩ := Metric.cauchySeq_iff.mp hf _ hδ
  refine ⟨max N M, ?_⟩
  intro i hi j hj
  have hxi := hN i ((le_max_left _ _).trans hi) j ((le_max_left _ _).trans hj)
  have hfi := hM' i ((le_max_right _ _).trans hi) j ((le_max_right _ _).trans hj)
  calc
    dist (u i) (u j) ≤ (√K + 1) *
        (dist (x i) (x j) + dist (f i) (f j)) := hlinear i j
    _ < (√K + 1) *
        (ε / (2 * (√K + 1)) + ε / (2 * (√K + 1))) :=
      mul_lt_mul_of_pos_left (add_lt_add hxi hfi) hM
    _ = ε := by
      field_simp [ne_of_gt hM]
      ring

/-- Complete the trajectories in the uniform metric and retain the prescribed initial
value. On a compact interval, every continuous trajectory is a bounded continuous map. -/
theorem exists_uniform_limit_with_initial_of_sq_stability [CompleteSpace H]
    {x : ℕ → H} {f : ℕ → Y} {u : ℕ → T →ᵇ H} {x₀ : H} {f₀ : Y}
    (hx : Tendsto x atTop (𝓝 x₀)) (hf : Tendsto f atTop (𝓝 f₀))
    {K : ℝ} (hK : 0 ≤ K)
    (hstable : ∀ i j t,
      dist (u i t) (u j t) ^ 2 ≤ K * (dist (x i) (x j) ^ 2 +
        dist (f i) (f j) ^ 2))
    (t₀ : T) (hinit : ∀ i, u i t₀ = x i) :
    ∃ v : T →ᵇ H, Tendsto u atTop (𝓝 v) ∧ v t₀ = x₀ := by
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_initial_forcing_sq_stability hx.cauchySeq hf.cauchySeq hK hstable)
  refine ⟨v, hv, ?_⟩
  have heval : Continuous (fun w : T →ᵇ H ↦ w t₀) :=
    (BoundedContinuousFunction.lipschitz_eval_const t₀).continuous
  have htrace : Tendsto x atTop (𝓝 (v t₀)) := by
    simpa only [Function.comp_def, hinit] using (heval.tendsto v).comp hv
  exact tendsto_nhds_unique htrace hx

/-- The same estimate holds between limits of two different approximation families.
Equal limiting initial data and loads force equal limiting trajectories. No derivative
or spatial regularity of either limit is assumed. -/
theorem dist_sq_le_of_initial_forcing_limits
    {x y : ℕ → H} {f g : ℕ → Y} {u v : ℕ → T →ᵇ H}
    {x₀ y₀ : H} {f₀ g₀ : Y} {u₀ v₀ : T →ᵇ H}
    (hx : Tendsto x atTop (𝓝 x₀)) (hy : Tendsto y atTop (𝓝 y₀))
    (hf : Tendsto f atTop (𝓝 f₀)) (hg : Tendsto g atTop (𝓝 g₀))
    (hu : Tendsto u atTop (𝓝 u₀)) (hv : Tendsto v atTop (𝓝 v₀))
    (K : ℝ)
    (hstable : ∀ i t,
      dist (u i t) (v i t) ^ 2 ≤ K * (dist (x i) (y i) ^ 2 +
        dist (f i) (g i) ^ 2)) (t : T) :
    dist (u₀ t) (v₀ t) ^ 2 ≤ K * (dist x₀ y₀ ^ 2 + dist f₀ g₀ ^ 2) := by
  have heval : Continuous (fun w : T →ᵇ H ↦ w t) :=
    (BoundedContinuousFunction.lipschitz_eval_const t).continuous
  exact le_of_tendsto_of_tendsto
    (((heval.tendsto _).comp hu).dist ((heval.tendsto _).comp hv) |>.pow 2)
    (tendsto_const_nhds.mul (((hx.dist hy).pow 2).add ((hf.dist hg).pow 2)))
    (Eventually.of_forall fun i ↦ hstable i t)

end PDE.Analysis.Evolution
