/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Sobolev.HigherOrder.CompactSupportSupercritical
public import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.Embedding

/-!
# Local continuous representatives of square-integrable Sobolev fields

Above the continuity threshold, multiplying a Sobolev field by a smooth compact
cutoff gives a bounded continuous representative. The Sobolev and Morrey embeddings
construct it; uniqueness of continuous representatives makes the construction linear.
The closed graph theorem then gives continuity in the supremum norm.

Evaluation where the cutoff equals one is therefore a continuous linear functional
on the Sobolev space. This lets pointwise normalizations survive completion without
evaluating an arbitrary almost-everywhere representative.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace Filter Set
open scoped Distributions BoundedContinuousFunction ENNReal Topology Sobolev

namespace SobolevSpace.GraphSpace

variable {n m : ℕ}

private theorem exists_boundedRepresentative_of_dimension_lt
    {q : NNReal} [hq : Fact (1 ≤ (q : ℝ≥0∞))]
    (hn : 0 < n) (hqn : (n : ℝ) < q) :
    ∀ V : W^{1,(q : ℝ≥0∞)}(ℝ^n), ∃ F : (ℝ^n) →ᵇ ℝ,
      (F : ℝ^n → ℝ) =ᵐ[volume] baseRepresentative V := by
  have hqR : 1 < (q : ℝ) := lt_of_le_of_lt (by exact_mod_cast hn) hqn
  revert hq
  rw [← ENNReal.ofReal_coe_nnreal (p := q)]
  intro inst V
  exact ⟨(finiteMorreyEmbedding hn hqn
    (Real.HolderConjugate.conjExponent hqR) V).toBoundedContinuousFunction,
    finiteMorreyEmbedding_ae hn hqn (Real.HolderConjugate.conjExponent hqR) V⟩

private theorem exists_cutoff_boundedRepresentative
    (hn : 0 < n) (hm : 1 + n / 2 ≤ m)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : W^{m,2}(ℝ^n)) :
    ∃ F : (ℝ^n) →ᵇ ℝ, (F : ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ ψ.toFun x * baseRepresentative U x := by
  obtain ⟨q, hq, hqn, V, hV⟩ := exists_global_supercritical_cutoff (k := 0)
    hn isOpen_univ ψ (subset_univ _)
    (lowerOrderCLM (n := n) (p := 2) (Ω := univ) hm U)
  have : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq⟩
  obtain ⟨F, hF⟩ := exists_boundedRepresentative_of_dimension_lt hn hqn V
  refine ⟨F, hF.trans ?_⟩
  simpa [baseRepresentative] using hV

private def cutoffBoundedRepresentative
    (hn : 0 < n) (hm : 1 + n / 2 ≤ m)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : W^{m,2}(ℝ^n)) : (ℝ^n) →ᵇ ℝ :=
  (exists_cutoff_boundedRepresentative hn hm ψ U).choose

private theorem cutoffBoundedRepresentative_ae
    (hn : 0 < n) (hm : 1 + n / 2 ≤ m)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : W^{m,2}(ℝ^n)) :
    (cutoffBoundedRepresentative hn hm ψ U : ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ ψ.toFun x * baseRepresentative U x :=
  (exists_cutoff_boundedRepresentative hn hm ψ U).choose_spec

private def cutoffBoundedRepresentativeLinearMap
    (hn : 0 < n) (hm : 1 + n / 2 ≤ m)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    W^{m,2}(ℝ^n) →ₗ[ℝ] ((ℝ^n) →ᵇ ℝ) where
  toFun := cutoffBoundedRepresentative hn hm ψ
  map_add' U V := by
    apply DFunLike.coe_injective
    apply map_add_of_continuous_ae_eq
      (fun W ↦ (cutoffBoundedRepresentative hn hm ψ W).continuous)
      (cutoffBoundedRepresentative_ae hn hm ψ)
    have hbase := baseRepresentative_add_ae U V
    simp only [domainMeasure, Measure.restrict_univ] at hbase
    filter_upwards [hbase] with x hx
    rw [hx, mul_add]
  map_smul' c U := by
    apply DFunLike.coe_injective
    apply map_smul_of_continuous_ae_eq
      (fun W ↦ (cutoffBoundedRepresentative hn hm ψ W).continuous)
      (cutoffBoundedRepresentative_ae hn hm ψ)
    have hbase := baseRepresentative_smul_ae c U
    simp only [domainMeasure, Measure.restrict_univ] at hbase
    filter_upwards [hbase] with x hx
    rw [hx]
    exact mul_left_comm _ _ _

private theorem cutoffBoundedRepresentativeLinearMap_seqClosedGraph
    (hn : 0 < n) (hm : 1 + n / 2 ≤ m)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (u : ℕ → W^{m,2}(ℝ^n)) (U : W^{m,2}(ℝ^n)) (F : (ℝ^n) →ᵇ ℝ)
    (hu : Tendsto u atTop (𝓝 U))
    (hF : Tendsto (cutoffBoundedRepresentativeLinearMap hn hm ψ ∘ u)
      atTop (𝓝 F)) :
    F = cutoffBoundedRepresentativeLinearMap hn hm ψ U := by
  have hbase : TendstoInMeasure volume (fun j ↦ baseRepresentative (u j))
      atTop (baseRepresentative U) := by
    simpa [baseRepresentative, domainMeasure] using tendstoInMeasure_of_tendsto_Lp
      (((wkpBaseCoordinateCLM (n := n) (m := m) (p := 2)
        (Ω := univ)).continuous.tendsto U).comp hu)
  obtain ⟨σ, hσ, hlim⟩ := hbase.exists_seq_tendsto_ae
  have hrows : ∀ᵐ x ∂volume, ∀ j : ℕ,
      cutoffBoundedRepresentative hn hm ψ (u j) x =
        ψ.toFun x * baseRepresentative (u j) x :=
    ae_all_iff.mpr (fun j ↦ cutoffBoundedRepresentative_ae hn hm ψ (u j))
  apply DFunLike.coe_injective
  apply Measure.eq_of_ae_eq (μ := volume) _ F.continuous (BoundedContinuousFunction.continuous _)
  filter_upwards [hlim, hrows, cutoffBoundedRepresentative_ae hn hm ψ U]
    with x hx hrowsx hUx
  have hFx : Tendsto (fun j ↦ cutoffBoundedRepresentative hn hm ψ (u (σ j)) x)
      atTop (𝓝 (F x)) :=
    (((BoundedContinuousFunction.evalCLM ℝ x).continuous.tendsto F).comp hF).comp
      hσ.tendsto_atTop
  have hmul : Tendsto (fun j ↦ ψ.toFun x * baseRepresentative (u (σ j)) x)
      atTop (𝓝 (ψ.toFun x * baseRepresentative U x)) := tendsto_const_nhds.mul hx
  have heq : F x = ψ.toFun x * baseRepresentative U x := by
    apply tendsto_nhds_unique hFx
    exact hmul.congr (fun j ↦ (hrowsx (σ j)).symm)
  exact heq.trans hUx.symm

/-- Smooth localization above the continuity threshold admits a bounded linear
choice of continuous representatives. -/
theorem exists_cutoffContinuousEmbedding
    (hn : 0 < n) (hm : 1 + n / 2 ≤ m)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    ∃ L : W^{m,2}(ℝ^n) →L[ℝ] ((ℝ^n) →ᵇ ℝ), ∀ U,
      (L U : ℝ^n → ℝ) =ᵐ[volume] fun x ↦ ψ.toFun x * baseRepresentative U x :=
  ⟨ContinuousLinearMap.ofSeqClosedGraph
    (cutoffBoundedRepresentativeLinearMap_seqClosedGraph hn hm ψ),
    cutoffBoundedRepresentative_ae hn hm ψ⟩

/-- The continuous representative of a smooth localization, with continuity in
the supremum norm derived from the closed graph theorem. -/
def cutoffContinuousEmbedding
    (hn : 0 < n) (hm : 1 + n / 2 ≤ m)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) :
    W^{m,2}(ℝ^n) →L[ℝ] ((ℝ^n) →ᵇ ℝ) :=
  (exists_cutoffContinuousEmbedding hn hm ψ).choose

/-- The localized continuous representative agrees almost everywhere with the
cutoff times the original Sobolev base coordinate. -/
theorem cutoffContinuousEmbedding_ae
    (hn : 0 < n) (hm : 1 + n / 2 ≤ m)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : W^{m,2}(ℝ^n)) :
    (cutoffContinuousEmbedding hn hm ψ U : ℝ^n → ℝ) =ᵐ[volume]
      fun x ↦ ψ.toFun x * baseRepresentative U x :=
  (exists_cutoffContinuousEmbedding hn hm ψ).choose_spec U

/-- For a continuous representative, localization agrees at every point,
including points lying in a null set for the original Sobolev representative. -/
theorem cutoffContinuousEmbedding_eq
    (hn : 0 < n) (hm : 1 + n / 2 ≤ m)
    (ψ : 𝓓((⊤ : Opens (ℝ^n)), ℝ)) (U : W^{m,2}(ℝ^n))
    {g : ℝ^n → ℝ} (hg : Continuous g) (hrep : g =ᵐ[volume] baseRepresentative U) :
    (cutoffContinuousEmbedding hn hm ψ U : ℝ^n → ℝ) =
      fun x ↦ ψ.toFun x * g x := by
  apply Measure.eq_of_ae_eq (μ := volume) _
    (BoundedContinuousFunction.continuous _) (ψ.continuous.mul hg)
  filter_upwards [cutoffContinuousEmbedding_ae hn hm ψ U, hrep] with x hx hgx
  change cutoffContinuousEmbedding hn hm ψ U x = ψ.toFun x * g x
  rw [hx, hgx]

/-- Evaluation of the continuous Sobolev representative is a bounded linear
functional above the continuity threshold. A cutoff equal to one at the chosen
point constructs it without assigning values to arbitrary L² representatives. -/
theorem exists_pointEvaluation
    (hn : 0 < n) (hm : 1 + n / 2 ≤ m)
    (x : ℝ^n) :
    ∃ L : W^{m,2}(ℝ^n) →L[ℝ] ℝ, ∀ U (g : ℝ^n → ℝ),
      Continuous g → g =ᵐ[volume] baseRepresentative U → L U = g x := by
  obtain ⟨ψ, _, hψ, _, _⟩ := TestFunction.exists_eq_one_on_compact
    isOpen_univ (isCompact_singleton (x := x)) (subset_univ _)
  refine ⟨(BoundedContinuousFunction.evalCLM ℝ x).comp
    (cutoffContinuousEmbedding hn hm ψ), ?_⟩
  intro U g hg hrep
  change cutoffContinuousEmbedding hn hm ψ U x = g x
  rw [congrFun (cutoffContinuousEmbedding_eq hn hm ψ U hg hrep) x,
    hψ x (mem_singleton x), one_mul]

end SobolevSpace.GraphSpace
