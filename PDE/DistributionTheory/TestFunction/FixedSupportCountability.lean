/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Countability of fixed-support test spaces

The topology on a fixed-support test space is determined by the sup norms of its
derivatives. Restriction to the common compact support preserves these norms.
For a finite-dimensional source and a second-countable target, the restricted
derivatives belong to second-countable continuous-map spaces.
-/

@[expose] public section

noncomputable section

open Filter Set TopologicalSpace Topology
open scoped BoundedContinuousFunction Distributions ContDiff Topology

namespace BoundedContinuousFunction

/-- Restriction to the common compact support preserves the sup distance. -/
theorem isometry_restrict_zero_on_compl
    {E F : Type*} [TopologicalSpace E] [MetricSpace F] [Zero F] (K : Compacts E) :
    Isometry (fun f : {f : E →ᵇ F // EqOn f 0 (K : Set E)ᶜ} ↦
      f.val.toContinuousMap.restrict (K : Set E)) := by
  apply Isometry.of_dist_eq
  intro f g
  apply le_antisymm
  · exact (ContinuousMap.dist_le dist_nonneg).2 fun x ↦
      dist_coe_le_dist (f := f.val) (g := g.val) x.val
  · change dist f.val g.val ≤ _
    refine (dist_le dist_nonneg).2 fun x ↦ ?_
    by_cases hx : x ∈ K
    · exact ContinuousMap.dist_apply_le_dist
        (f := f.val.toContinuousMap.restrict (K : Set E))
        (g := g.val.toContinuousMap.restrict (K : Set E)) ⟨x, hx⟩
    · simp [f.property hx, g.property hx]

end BoundedContinuousFunction

namespace ContDiffMapSupportedIn

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Fixed-support test spaces are second countable in their derivative topology.
The differentiability order may be finite or infinite. -/
instance instSecondCountableTopology [FiniteDimensional ℝ E] [SecondCountableTopology F]
    (n : ℕ∞) (K : Compacts E) : SecondCountableTopology 𝓓^{n}_{K}(E, F) := by
  have hjet (i : ℕ) : SecondCountableTopology (E [×i]→L[ℝ] F) := by
    induction i with
    | zero =>
      exact (continuousMultilinearCurryFin0 ℝ E F).isometry.isEmbedding.secondCountableTopology
    | succ i hi =>
      let := hi
      exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) ↦ E) F).isometry
        |>.isEmbedding.secondCountableTopology
  let S (i : ℕ) : Type _ :=
    {f : E →ᵇ (E [×i]→L[ℝ] F) // EqOn f 0 (K : Set E)ᶜ}
  have hS (i : ℕ) : SecondCountableTopology (S i) := by
    let := hjet i
    exact (BoundedContinuousFunction.isometry_restrict_zero_on_compl
      (F := E [×i]→L[ℝ] F) K).isEmbedding.secondCountableTopology
  let J : 𝓓^{n}_{K}(E, F) → ∀ i, S i := fun f i ↦
    ⟨structureMapCLM ℝ n i f, by
      intro x hx
      change (structureMapCLM ℝ n i f : E → (E [×i]→L[ℝ] F)) x = 0
      rw [structureMapCLM_apply]
      split_ifs
      · exact f.iteratedFDeriv_zero_on_compl hx
      · rfl⟩
  let V : (∀ i, S i) → ∀ i, E →ᵇ (E [×i]→L[ℝ] F) := fun f i ↦ (f i).val
  have hV : IsInducing V := IsInducing.piMap fun _ ↦ IsInducing.subtypeVal
  have hJ : IsInducing J := hV.of_comp_iff.mp
    (isUniformEmbedding_pi_structureMapCLM
      (E := E) (F := F) (K := K) (n := n) ℝ).isEmbedding.isInducing
  let : ∀ i, SecondCountableTopology (S i) := hS
  exact hJ.secondCountableTopology

/-- A single countable collection approximates every constrained fixed-support test
in every available derivative, uniformly on the whole source space. Constraints are
encoded by a submodule, so the approximants retain them exactly. -/
theorem exists_dense_sequence_uniform_derivatives
    [FiniteDimensional ℝ E] [SecondCountableTopology F]
    {ι : Type*} [Countable ι] (n : ℕ∞) (K : Compacts E)
    (D : Submodule ℝ (ι → 𝓓^{n}_{K}(E, F))) :
    ∃ d : ℕ → D, DenseRange d ∧ ∀ f : D, ∃ a : ℕ → ℕ,
      Tendsto (fun m ↦ d (a m)) atTop (𝓝 f) ∧
      ∀ (j : ι) (i : ℕ), i ≤ n →
        TendstoUniformly (fun m ↦ iteratedFDeriv ℝ i ((d (a m)).val j))
          (iteratedFDeriv ℝ i (f.val j)) atTop := by
  classical
  have : SecondCountableTopology D :=
    (IsEmbedding.subtypeVal :
      IsEmbedding (fun f : D ↦ (f : ι → 𝓓^{n}_{K}(E, F)))).secondCountableTopology
  let d := denseSeq D
  have hd : DenseRange d := denseRange_denseSeq D
  refine ⟨d, hd, fun f ↦ ?_⟩
  obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp (hd f)
  choose a ha using hu
  have hseq : Tendsto (fun m ↦ d (a m)) atTop (𝓝 f) := by
    simpa only [ha] using ht
  refine ⟨a, hseq, fun j i hi ↦ ?_⟩
  have hrow : Tendsto (fun m ↦ (d (a m)).val j) atTop (𝓝 (f.val j)) :=
    ((continuous_apply j).comp continuous_subtype_val).tendsto f |>.comp hseq
  have hderiv := (structureMapCLM ℝ n i).continuous.tendsto (f.val j) |>.comp hrow
  simpa only [Function.comp_def, structureMapCLM_apply, ite_eq_left hi] using
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hderiv)

end ContDiffMapSupportedIn
