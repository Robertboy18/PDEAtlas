/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.Geometric.Extension
public import PDE.Spaces.Sobolev.Inequalities.Morrey.VectorValued.Boundary.Representative

/-!
# Banach-valued W¹,∞ representatives on C¹ domains

The finite-atlas extension, with its interior cutoff and reflected chart pieces,
gives a bounded linear embedding into continuous functions on the closure. The sum of the
norms of the extension pieces is an explicit atlas-dependent bound.
Different atlases give the same closure values, although their extension norms may differ.

The geometric existence theorem also covers dimension zero and empty domains, through the
trivial-domain extensions. Smooth functions need not be norm-dense at exponent infinity, and
the argument does not use such density.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal NNReal Sobolev BoundedContinuousFunction

namespace SobolevSpace.VectorValued

open GraphSpace GeometricExtension

variable {n : ℕ} {Ω : Opens ℝ^n} {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

section Atlas

variable [Fact (0 < n)] [hΩ : Boundary.C1ExtensionAtlas n (Ω : Set ℝ^n)]

/-- Sum of the operator norms of the interior and reflected boundary terms
in the first-order, infinite-exponent extension for this atlas and Banach codomain. -/
def c1ExtensionBound (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] : ℝ≥0 :=
  ‖(interMultiplier (F := F) (k := 1) (p := ∞) (Ω := ⊤) (V := Ω)
    hΩ.interiorCutoff hΩ.interiorCutoff_support).comp
      (restrictCLM (inf_le_left : Ω ⊓ ⊤ ≤ Ω))‖₊ +
    ∑ i : Fin hΩ.N, ‖boundaryExtensionSobolev (F := F) (p := ∞)
      (by decide : 0 < 1) hΩ.chart_contDiff hΩ.chart_symm_contDiff i‖₊

/-- The norm of the assembled extension is at most the finite sum of its piece norms. -/
theorem nnnorm_extensionSobolev_one_le :
    ‖extensionSobolev (F := F) (p := ∞) (by decide : 0 < 1)
      hΩ.chart_contDiff hΩ.chart_symm_contDiff‖₊ ≤ c1ExtensionBound (Ω := Ω) F := by
  let I : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F) :=
    (interMultiplier (Ω := ⊤) (V := Ω)
      hΩ.interiorCutoff hΩ.interiorCutoff_support).comp
        (restrictCLM (inf_le_left : Ω ⊓ ⊤ ≤ Ω))
  let B (i : Fin hΩ.N) : W^{1,∞}(Ω; F) →L[ℝ] W^{1,∞}(ℝ^n; F) :=
    boundaryExtensionSobolev (by decide) hΩ.chart_contDiff hΩ.chart_symm_contDiff i
  change ‖I + ∑ i, B i‖₊ ≤ ‖I‖₊ + ∑ i, ‖B i‖₊
  have hsum : ‖∑ i, B i‖₊ ≤ ∑ i, ‖B i‖₊ := nnnorm_sum_le Finset.univ B
  exact (nnnorm_add_le I (∑ i, B i)).trans (add_le_add le_rfl hsum)

/-- Apply the C¹ atlas extension and restrict its Lipschitz representative to the
closure. This is a continuous linear map on the Banach-valued Sobolev graph. -/
def c1ClosureLipschitzEmbedding :
    W^{1,∞}(Ω; F) →L[ℝ] (closure (Ω : Set ℝ^n) →ᵇ F) :=
  closureLipschitzEmbedding
    (extensionSobolev (by decide) hΩ.chart_contDiff hΩ.chart_symm_contDiff)

/-- Evaluation is the whole-space endpoint representative of the C¹ extension. -/
@[simp] theorem c1ClosureLipschitzEmbedding_apply
    (U : W^{1,∞}(Ω; F)) (x : closure (Ω : Set ℝ^n)) :
    c1ClosureLipschitzEmbedding U x =
      lipschitzRepresentative
        (extensionSobolev (by decide) hΩ.chart_contDiff hΩ.chart_symm_contDiff U) x := rfl

/-- The C¹ construction represents the physical base almost everywhere on the domain. -/
theorem c1ClosureLipschitzEmbedding_ae (U : W^{1,∞}(Ω; F)) :
    ∀ᵐ x ∂domainMeasure n Ω, ∀ hx : x ∈ closure (Ω : Set ℝ^n),
      c1ClosureLipschitzEmbedding U ⟨x, hx⟩ = U.val (baseIndex n 1) x :=
  closureLipschitzEmbedding_ae _
    (restrict_extensionSobolev (by decide) hΩ.chart_contDiff hΩ.chart_symm_contDiff) U

/-- The Euclidean Lipschitz bound keeps the finite-atlas extension constant. -/
theorem lipschitzWith_c1ClosureLipschitzEmbedding (U : W^{1,∞}(Ω; F)) :
    LipschitzWith (n * c1ExtensionBound (Ω := Ω) F * ‖U‖₊)
      (c1ClosureLipschitzEmbedding U) := by
  apply (lipschitzWith_closureLipschitzEmbedding_norm _ U).weaken
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left nnnorm_extensionSobolev_one_le zero_le) zero_le

/-- The same finite sum bounds the norm of the closure embedding. -/
theorem nnnorm_c1ClosureLipschitzEmbedding_le :
    ‖c1ClosureLipschitzEmbedding (Ω := Ω) (F := F)‖₊ ≤ c1ExtensionBound (Ω := Ω) F :=
  (show ‖c1ClosureLipschitzEmbedding (Ω := Ω) (F := F)‖₊ ≤
      ‖extensionSobolev (F := F) (p := ∞) (by decide : 0 < 1)
        hΩ.chart_contDiff hΩ.chart_symm_contDiff‖₊ from
    norm_closureLipschitzEmbedding_le _).trans nnnorm_extensionSobolev_one_le

/-- The closure values determine every derivative coordinate of the class. -/
theorem c1ClosureLipschitzEmbedding_injective :
    Function.Injective (c1ClosureLipschitzEmbedding (Ω := Ω) (F := F)) :=
  closureLipschitzEmbedding_injective _
    (restrict_extensionSobolev (by decide) hΩ.chart_contDiff hΩ.chart_symm_contDiff)

end Atlas

/-- Changing the finite C¹ atlas changes the ambient extension but preserves the closure
embedding, including when the domain is empty or disconnected. -/
theorem c1ClosureLipschitzEmbedding_eq [Fact (0 < n)]
    (A B : Boundary.C1ExtensionAtlas n (Ω : Set ℝ^n)) :
    c1ClosureLipschitzEmbedding (F := F) (hΩ := A) =
      c1ClosureLipschitzEmbedding (F := F) (hΩ := B) :=
  closureLipschitzEmbedding_eq _ _
    (restrict_extensionSobolev (hΩ := A) (by decide) A.chart_contDiff A.chart_symm_contDiff)
    (restrict_extensionSobolev (hΩ := B) (by decide) B.chart_contDiff B.chart_symm_contDiff)

/-- Bounded open C¹ graph domains admit bounded linear Lipschitz representatives
on their closure. The constant is the norm of the geometric extension. Empty
domains and dimension zero are included; no Banach-space Radon–Nikodym property is assumed. -/
theorem exists_closureLipschitzEmbedding
    (hbounded : Bornology.IsBounded (Ω : Set ℝ^n))
    (hgraph : Boundary.HasContDiffGraphBoundary 1 (Ω : Set ℝ^n)) :
    ∃ T : W^{1,∞}(Ω; F) →L[ℝ] (closure (Ω : Set ℝ^n) →ᵇ F),
      Function.Injective T ∧ ∃ C : ℝ≥0, ‖T‖₊ ≤ C ∧ ∀ U,
        LipschitzWith (n * C * ‖U‖₊) (T U) ∧
        ∀ᵐ x ∂domainMeasure n Ω, ∀ hx : x ∈ closure (Ω : Set ℝ^n),
          T U ⟨x, hx⟩ = U.val (baseIndex n 1) x := by
  obtain ⟨E, _, _, _, hE⟩ :=
    exists_extension_with_Lp_base (k := 1) (p := ∞) (F := F) hbounded hgraph
  exact ⟨closureLipschitzEmbedding E, closureLipschitzEmbedding_injective E hE,
    ‖E‖₊, norm_closureLipschitzEmbedding_le E, fun U ↦
      ⟨lipschitzWith_closureLipschitzEmbedding_norm E U,
        closureLipschitzEmbedding_ae E hE U⟩⟩

end SobolevSpace.VectorValued
