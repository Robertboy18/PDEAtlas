/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Removing a compact term from a norm estimate

Suppose `‖u‖ ≤ ‖J u‖ + C ‖G u‖`, where `J` is compact and `G` is injective.
On a Banach space the compact term can be removed: `‖u‖ ≤ K ‖G u‖` for some `K`.

The proof normalizes a hypothetical counterexample sequence. Compactness gives convergence
of its `J` images, while its `G` images tend to zero. The original estimate then makes the
sequence Cauchy. Its nonzero limit contradicts injectivity of `G`.
-/

@[expose] public section

open Filter
open scoped NNReal Topology

namespace IsCompactOperator

variable {E F H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A compact term in a graph norm estimate can be removed if the other operator is
injective. Completeness and the initial estimate supply convergence in the source space. -/
theorem exists_norm_le_of_injective
    {J : E →L[ℝ] F} (hJ : IsCompactOperator J) (G : E →L[ℝ] H)
    (C : ℝ≥0) (hbound : ∀ u, ‖u‖ ≤ ‖J u‖ + C * ‖G u‖)
    (hinj : Function.Injective G) :
    ∃ K : ℝ, 0 < K ∧ ∀ u, ‖u‖ ≤ K * ‖G u‖ := by
  by_contra! h
  have hsmall (ε : ℝ) (hε : 0 < ε) :
      ∃ u : E, ‖u‖ = 1 ∧ ‖G u‖ < ε := by
    obtain ⟨v, hv⟩ := h ε⁻¹ (inv_pos.mpr hε)
    have hvpos : 0 < ‖v‖ :=
      lt_of_le_of_lt (mul_nonneg (inv_nonneg.mpr hε.le) (norm_nonneg _)) hv
    refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hvpos.le)]
      exact inv_mul_cancel₀ hvpos.ne'
    · rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hvpos.le)]
      have hv' : ‖G v‖ < ε * ‖v‖ := by
        simpa only [mul_inv_cancel_left₀ hε.ne'] using
          mul_lt_mul_of_pos_left hv hε
      calc
        ‖v‖⁻¹ * ‖G v‖ < ‖v‖⁻¹ * (ε * ‖v‖) :=
          mul_lt_mul_of_pos_left hv' (inv_pos.mpr hvpos)
        _ = ε := by field_simp
  let ε : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by
    dsimp [ε]
    positivity
  choose u hu hGu using fun k ↦ hsmall (ε k) (hε k)
  have hGzero : Tendsto (fun k ↦ G (u k)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k ↦ (hGu k).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨S, hS, hJS⟩ := hJ.image_closedBall_subset_compact 1
  obtain ⟨v, _, ψ, hψ, hJψ⟩ := hS.tendsto_subseq
    (fun k ↦ hJS ⟨u k, by simp [Metric.mem_closedBall, hu], rfl⟩)
  have hprod : Tendsto (fun k ↦ (J.prod G) (u (ψ k))) atTop (𝓝 (v, 0)) :=
    hJψ.prodMk_nhds (hGzero.comp hψ.tendsto_atTop)
  have hanti : AntilipschitzWith (1 + C) (J.prod G) := by
    apply ContinuousLinearMap.antilipschitz_of_bound
    intro z
    calc
      ‖z‖ ≤ ‖J z‖ + C * ‖G z‖ := hbound z
      _ ≤ ‖(J.prod G) z‖ + C * ‖(J.prod G) z‖ :=
        add_le_add (norm_fst_le (J z, G z))
          (mul_le_mul_of_nonneg_left (norm_snd_le (J z, G z)) C.coe_nonneg)
      _ = (1 + C : ℝ≥0) * ‖(J.prod G) z‖ := by
        simp only [NNReal.coe_add, NNReal.coe_one]
        ring
  have hcauchy : CauchySeq (fun k ↦ u (ψ k)) :=
    (hanti.isUniformInducing (J.prod G).uniformContinuous).cauchy_map_iff.mp
      (by simpa only [CauchySeq, Filter.map_map, Function.comp_def] using hprod.cauchySeq)
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hGz : G z = 0 := tendsto_nhds_unique
    (G.continuous.continuousAt.tendsto.comp hz) (hGzero.comp hψ.tendsto_atTop)
  have hz0 : z = 0 := hinj (hGz.trans G.map_zero.symm)
  have hnorm : ‖z‖ = 1 :=
    tendsto_nhds_unique hz.norm (by simpa only [hu] using tendsto_const_nhds)
  simp [hz0] at hnorm

end IsCompactOperator
