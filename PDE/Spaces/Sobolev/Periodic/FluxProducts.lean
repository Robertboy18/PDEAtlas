/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Periodic.FluxTesting
public import PDE.Spaces.Sobolev.Localization.Cutoff.Coordinates
public import PDE.Analysis.Integration.PeriodicAveraging.VectorAveraging
public import PDE.Analysis.WeakCompactness

/-!
# Compensated pairings with periodic solenoidal fluxes

The canonical Sobolev cutoff product rule transfers the weak derivative in a
weighted flux pairing to the cutoff. Strong convergence of the value coordinates,
weak periodic averaging, and uniform rescaling bounds then give convergence of the
weighted pairings. No convergence assumption on the varying gradients is needed.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter TopologicalSpace
open PDE.Analysis.PeriodicAveraging
open scoped ENNReal Topology InnerProductSpace Sobolev Distributions

namespace SobolevSpace.Periodic

/-- Testing a divergence-free L² flux against a cutoff Sobolev function transfers
its weak gradient to the smooth cutoff. -/
theorem inner_weighted_gradient_eq_neg {n : ℕ} {Ω : Set (ℝ^n)} (hΩo : IsOpen Ω)
    (q : Lp (ℝ^n) 2 (domainMeasure n Ω))
    (hq : ∀ u : H¹₀(Ω), ⟪q, GraphSpace.gradientCLM u⟫_ℝ = 0)
    (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (u : H¹₀(Ω)) :
    ⟪q, GraphSpace.testFunctionLpTop (Ω := Ω) κ • GraphSpace.gradientCLM u⟫_ℝ =
      -⟪q, Lp.euclideanTuple (fun i ↦
        GraphSpace.partialTestFunctionLpTop (Ω := Ω) κ i • GraphSpace.baseCoordCLM u)⟫_ℝ := by
  have hg : GraphSpace.gradientCLM (GraphSpace.cutoffH10 hΩo κ u) =
      GraphSpace.testFunctionLpTop (Ω := Ω) κ • GraphSpace.gradientCLM u +
        Lp.euclideanTuple (fun i ↦
          GraphSpace.partialTestFunctionLpTop (Ω := Ω) κ i • GraphSpace.baseCoordCLM u) := by
    have he (w : H¹₀(Ω)) : GraphSpace.gradientCLM w =
        Lp.euclideanTuple (fun i ↦ GraphSpace.derivCoordCLM i w) := rfl
    rw [he, he, ← Lp.euclideanTuple_lpSMul, ← map_add]
    congr 1
    funext i
    exact GraphSpace.derivCoordCLM_cutoffH10 hΩo κ u i
  have hz := hq (GraphSpace.cutoffH10 hΩo κ u)
  rw [hg, inner_add_right] at hz
  exact eq_neg_of_add_eq_zero_left hz

/-- A rescaled periodic solenoidal flux may be paired with weak gradients of a
varying zero-boundary Sobolev family whose values converge strongly in L².
The limit is the same pairing with the actual cell-mean flux. -/
theorem tendsto_inner_rescale_weighted_gradient {n : ℕ} {Ω : Set (ℝ^n)}
    (hΩ : Bornology.IsBounded Ω) (hΩo : IsOpen Ω)
    [IsFiniteMeasure (volume.restrict Ω)]
    (v : Lp (ℝ^n) 2 (cellMeasure n))
    (hv : ∀ w : h1Space n, ⟪v, gradientCLM n w⟫_ℝ = 0)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (ε : ι → ℝ) (hε : ∀ j, 0 < ε j) (hε1 : ∀ j, ε j ≤ 1)
    (ht : Tendsto ε l (𝓝 0)) (u : ι → H¹₀(Ω)) (U : H¹₀(Ω))
    (hu : Tendsto (fun j ↦ GraphSpace.baseCoordCLM (u j)) l
      (𝓝 (GraphSpace.baseCoordCLM U))) (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    Tendsto (fun j ↦ ⟪rescaleLp hΩ (ε j) (hε j) (hε1 j) v,
      GraphSpace.testFunctionLpTop (Ω := Ω) κ • GraphSpace.gradientCLM (u j)⟫_ℝ) l
      (𝓝 ⟪Lp.const 2 (volume.restrict Ω) (∫ y, v y ∂cellMeasure n),
        GraphSpace.testFunctionLpTop (Ω := Ω) κ • GraphSpace.gradientCLM U⟫_ℝ) := by
  let q := fun j ↦ rescaleLp hΩ (ε j) (hε j) (hε1 j) v
  let Q := Lp.const 2 (volume.restrict Ω) (∫ y, v y ∂cellMeasure n)
  have hq : ∀ j, ∀ w : H¹₀(Ω), ⟪q j, GraphSpace.gradientCLM w⟫_ℝ = 0 :=
    fun j w ↦ inner_rescale_gradient_eq_zero hΩ v hv (ε j) (hε j) (hε1 j) w
  have hweak := tendsto_weak_rescaleLp_euclidean hΩ hΩo.measurableSet ε hε hε1 ht v
  have hQ (w : H¹₀(Ω)) : ⟪Q, GraphSpace.gradientCLM w⟫_ℝ = 0 := by
    have he := PDE.Analysis.WeakCompactness.tendsto_evaluation hweak
      (innerSL ℝ (GraphSpace.gradientCLM w))
    change Tendsto (fun j ↦ ⟪GraphSpace.gradientCLM w, q j⟫_ℝ) l
      (𝓝 ⟪GraphSpace.gradientCLM w, Q⟫_ℝ) at he
    calc
      _ = ⟪GraphSpace.gradientCLM w, Q⟫_ℝ := real_inner_comm _ _
      _ = 0 := tendsto_nhds_unique_of_forall he tendsto_const_nhds
        (fun j ↦ (real_inner_comm _ _).trans (hq j w))
  let M : GraphSpace.DerivLp n 2 Ω →L[ℝ] Lp (ℝ^n) 2 (domainMeasure n Ω) :=
    Lp.euclideanTuple.comp (ContinuousLinearMap.pi fun i ↦
      GraphSpace.mulLpLeft (GraphSpace.partialTestFunctionLpTop (Ω := Ω) κ i))
  have hM (a : GraphSpace.DerivLp n 2 Ω) : M a =
      Lp.euclideanTuple (fun i ↦ GraphSpace.partialTestFunctionLpTop (Ω := Ω) κ i • a) := rfl
  obtain ⟨C, _hC, hbound⟩ := exists_norm_rescaleLp_le (E := ℝ^n) (p := 2) hΩ
  have hpair := PDE.Analysis.WeakCompactness.tendsto_dual_apply_of_tendsto_strong_weak
    ((innerSL ℝ).continuous.tendsto (M (GraphSpace.baseCoordCLM U)) |>.comp
      ((M.continuous.tendsto (GraphSpace.baseCoordCLM U)).comp hu)) hweak
    (C * ‖v‖) (fun j ↦ hbound (ε j) (hε j) (hε1 j) v)
  change Tendsto (fun j ↦ ⟪M (GraphSpace.baseCoordCLM (u j)), q j⟫_ℝ) l
    (𝓝 ⟪M (GraphSpace.baseCoordCLM U), Q⟫_ℝ) at hpair
  have hj (j : ι) := inner_weighted_gradient_eq_neg hΩo (q j) (hq j) κ (u j)
  have hlim := inner_weighted_gradient_eq_neg hΩo Q hQ κ U
  have hji (j : ι) :
      ⟪q j, GraphSpace.testFunctionLpTop (Ω := Ω) κ •
        GraphSpace.gradientCLM (u j)⟫_ℝ =
      -⟪M (GraphSpace.baseCoordCLM (u j)), q j⟫_ℝ := by
    rw [hj, hM, real_inner_comm]
  have hli : ⟪Q, GraphSpace.testFunctionLpTop (Ω := Ω) κ •
      GraphSpace.gradientCLM U⟫_ℝ = -⟪M (GraphSpace.baseCoordCLM U), Q⟫_ℝ := by
    rw [hlim, hM, real_inner_comm]
  change Tendsto (fun j ↦ ⟪q j, GraphSpace.testFunctionLpTop (Ω := Ω) κ •
    GraphSpace.gradientCLM (u j)⟫_ℝ) l
    (𝓝 ⟪Q, GraphSpace.testFunctionLpTop (Ω := Ω) κ • GraphSpace.gradientCLM U⟫_ℝ)
  simp_rw [hji, hli]
  exact hpair.neg

end SobolevSpace.Periodic
