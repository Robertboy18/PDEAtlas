/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.Domain.Slobodeckij.Mollification.Graph

/-!
# Smooth approximation in the whole-space fractional graph

Every element of the whole-space Gagliardo graph has smooth representatives
arbitrarily close in its full norm. The approximating functions need not have
compact support. The result includes Banach-valued functions and every finite
exponent `p ≥ 1`.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology FractionalSobolev
open SobolevSpace.Approximation

namespace SobolevSpace.Fractional.GagliardoSpace

variable {n : ℕ} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Every whole-space fractional Sobolev element admits a globally smooth
representative within any prescribed positive graph-norm error. -/
theorem exists_smooth_approximation (μ : Mollifier n) (hp : p ≠ ∞)
    (u : W^{s,p}(ℝ^n; F)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ v : W^{s,p}(ℝ^n; F), ∃ f : ℝ^n → F,
      ContDiff ℝ (⊤ : ℕ∞) f ∧ (toLp n s Set.univ v : ℝ^n → F) =ᵐ[volume] f ∧
      ‖v - u‖ < δ := by
  let ε (m : ℕ) : ℝ := 1 / (m + 1)
  have hε (m : ℕ) : 0 < ε m := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall hε⟩
    simpa only [ε] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have ht := tendsto_mollify μ hp u ε hε hε0
  have he := ((ht.sub tendsto_const_nhds).norm).eventually
    (gt_mem_nhds (show ‖u - u‖ < δ by simpa using hδ))
  obtain ⟨m, hm⟩ := he.exists
  obtain ⟨f, hf, hbase⟩ := mollify_has_smooth_representative μ (hε m) hp u
  exact ⟨mollify μ (hε m) hp u, f, hf, hbase, hm⟩

/-- Globally smooth representatives are dense in the whole-space fractional
Sobolev graph for every finite exponent `p ≥ 1` and Banach codomain. -/
theorem dense_smooth (hp : p ≠ ∞) :
    Dense {u : W^{s,p}(ℝ^n; F) |
      ∃ f : ℝ^n → F, ContDiff ℝ (⊤ : ℕ∞) f ∧
        (toLp n s Set.univ u : ℝ^n → F) =ᵐ[volume] f} := by
  intro u
  apply Metric.mem_closure_iff.mpr
  intro δ hδ
  obtain ⟨v, f, hf, hbase, hnorm⟩ :=
    exists_smooth_approximation (standardMollifier n) hp u hδ
  refine ⟨v, ⟨f, hf, hbase⟩, ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  exact hnorm

end SobolevSpace.Fractional.GagliardoSpace
