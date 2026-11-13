/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.VectorValued.Mollification.Graph

/-!
# Smooth density in whole-space Banach-valued Sobolev spaces

Convolution at positive scales tending to zero gives smooth representatives converging
in the full finite-order Sobolev graph norm. The codomain is any complete real normed space.
The mollification of an arbitrary Sobolev function need not have compact support.
-/

@[expose] public noncomputable section

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev Topology

namespace SobolevSpace.VectorValued

open Approximation GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A whole-space Sobolev bundle can be approximated to any prescribed positive graph-norm
error by a bundle with a globally smooth Banach-valued representative. -/
theorem exists_smooth_approximation_univ (μ : Mollifier n) (hp : p ≠ ∞)
    (U : W^{k,p}((⊤ : Opens ℝ^n); F)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ V : W^{k,p}((⊤ : Opens ℝ^n); F), ∃ f : ℝ^n → F,
      ContDiff ℝ (⊤ : ℕ∞) f ∧
      (V.val (baseIndex n k) : ℝ^n → F) =ᵐ[volume] f ∧ ‖V - U‖ < δ := by
  let ε (m : ℕ) : ℝ := 1 / (m + 1)
  have hε (m : ℕ) : 0 < ε m := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht := mollify_tendsto μ hp U ε hε hε0
  have he := ((ht.sub tendsto_const_nhds).norm).eventually
    (gt_mem_nhds (show ‖U - U‖ < δ by simpa using hδ))
  obtain ⟨m, hm⟩ := he.exists
  obtain ⟨f, hf, hbase⟩ := mollify_has_smooth_representative μ (hε m) hp U
  exact ⟨mollify μ (hε m) hp U, f, hf, hbase, hm⟩

/-- Smooth representatives are dense in every finite-order whole-space Banach-valued
Sobolev graph at every finite exponent at least one. -/
theorem dense_smooth_univ (μ : Mollifier n) (hp : p ≠ ∞) :
    Dense {U : W^{k,p}((⊤ : Opens ℝ^n); F) | ∃ f : ℝ^n → F,
      ContDiff ℝ (⊤ : ℕ∞) f ∧
      (U.val (baseIndex n k) : ℝ^n → F) =ᵐ[volume] f} := by
  intro U
  apply Metric.mem_closure_iff.mpr
  intro δ hδ
  obtain ⟨V, f, hf, hbase, hnorm⟩ := exists_smooth_approximation_univ μ hp U hδ
  exact ⟨V, ⟨f, hf, hbase⟩, by simpa only [dist_eq_norm, norm_sub_rev] using hnorm⟩

end SobolevSpace.VectorValued
