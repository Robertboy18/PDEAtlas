/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.VectorValued.Embedding
public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.Extension

/-!
# Banach-valued Morrey representatives on bounded graph domains

The Sobolev extension theorem for bounded `C¹` graph domains, followed by the
whole-space Morrey embedding, gives a bounded linear choice of global Hölder representatives.
The representatives agree with the original class on the domain. The target is the usual
space of bounded continuous functions, and no extension operator is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev BoundedContinuousFunction

namespace SobolevSpace.VectorValued

open GraphSpace

/-- On a bounded open set with `C¹` graph boundary, every finite-exponent supercritical
Banach-valued Sobolev class has a global Hölder representative, chosen by a bounded linear
injection. The bound is uniform in the input function; empty domains and dimension zero
are included by the extension theorem. -/
theorem exists_morreyEmbeddingOn
    {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (hp : (n : ℝ≥0∞) < p) (hfinite : p ≠ ∞)
    (hbounded : Bornology.IsBounded (Ω : Set ℝ^n))
    (hgraph : Boundary.HasContDiffGraphBoundary 1 (Ω : Set ℝ^n)) :
    ∃ T : W^{1,p}(Ω; F) →L[ℝ] (ℝ^n →ᵇ F), Function.Injective T ∧
      ∃ C : ℝ, 0 ≤ C ∧ ‖T‖ ≤ C ∧ ∀ U,
        ((T U : ℝ^n → F) =ᵐ[domainMeasure n Ω] (U.val (baseIndex n 1) : ℝ^n → F)) ∧
        HolderWith (C * ‖U‖).toNNReal (morreyExponent n p).toNNReal (T U) := by
  obtain ⟨E, _, _, _, hrestrict⟩ :=
    GeometricExtension.exists_extension_with_Lp_base (F := F) (p := p) hbounded hgraph
  let T := (morreyEmbedding hp hfinite).comp E
  have hae (U : W^{1,p}(Ω; F)) :
      (T U : ℝ^n → F) =ᵐ[domainMeasure n Ω] (U.val (baseIndex n 1) : ℝ^n → F) := by
    have hrep : (T U : ℝ^n → F) =ᵐ[domainMeasure n Ω]
        ((E U).val (baseIndex n 1) : ℝ^n → F) :=
      ae_mono Measure.restrict_le_self (morreyEmbedding_ae hp hfinite (E U))
    have h := restrictCLM_apply_ae (le_top : Ω ≤ ⊤) (E U) (baseIndex n 1)
    rw [hrestrict U] at h
    exact hrep.trans h.symm
  refine ⟨T, ?_, morreyConstant n p hp * ‖E‖,
    mul_nonneg (morreyConstant_nonneg hp) (norm_nonneg E), ?_, ?_⟩
  · intro U V h
    apply WkpSpaceOn.ext_of_base_ae
    exact (hae U).symm.trans
      ((Filter.EventuallyEq.of_eq (congrArg DFunLike.coe h)).trans (hae V))
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_morreyEmbedding_le hp hfinite) (norm_nonneg E))
  · intro U
    refine ⟨hae U, (holderWith_morreyEmbedding hp hfinite (E U)).mono ?_⟩
    apply Real.toNNReal_mono
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (E.le_opNorm U) (morreyConstant_nonneg hp)

end SobolevSpace.VectorValued
