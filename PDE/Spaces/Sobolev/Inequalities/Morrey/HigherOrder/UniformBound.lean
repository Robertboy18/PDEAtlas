/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.CutoffEmbedding
import PDE.Spaces.Sobolev.Compactness.Translation.H1
import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.Interior

/-!
# A uniform bound for continuous representatives of planar H² functions

Translate the function to bring the evaluation point to the origin. Reassembling
its translated H¹ value and gradient gives a bound independent of the translation,
so one continuous evaluation functional controls every point of the plane.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace

open MeasureTheory GraphSpace

private theorem exists_h2_translate_bound (U : W^{2,2}(ℝ^2)) (x : ℝ^2) :
    ∃ V : W^{2,2}(ℝ^2),
      baseRepresentative V =ᵐ[volume] (fun y ↦ baseRepresentative U (y + x)) ∧
      ‖V‖ ≤ (3 * succOrderAssemblyNormBound 2 1) * ‖U‖ := by
  let B : W^{1,2}(ℝ^2) := translateH1 x (lowerOrderCLM (by norm_num : 1 ≤ 2) U)
  let D (i : Fin 2) : W^{1,2}(ℝ^2) :=
    translateH1 x (derivativeWordCLM [i] (by simp : [i].length + 1 ≤ 2) U)
  have hD (i : Fin 2) :
      (D i : WkpAmbientOn 2 1 2 Set.univ) (baseIndex 2 1) =
        (B : WkpAmbientOn 2 1 2 Set.univ) (firstDerivIndex 2 1 (by norm_num) i) := by
    simp only [D, B, translateH1_apply, derivativeWordCLM_apply,
      derivativeWordIndex_singleton_baseIndex, lowerOrderCLM_apply,
      DerivIndex.castOrder_firstDerivIndex]
  obtain ⟨V, hv, hn⟩ := exists_succOrder_of_firstDerivatives_with_norm
    (by norm_num : 0 < 1) B D hD
  have hb : baseRepresentative B =ᵐ[volume]
      (fun y ↦ baseRepresentative U (y + x)) := by
    simpa only [baseRepresentative, B, translateH1_apply, lowerOrderCLM_apply,
      DerivIndex.castOrder_baseIndex, domainMeasure, Measure.restrict_univ] using
      Rellich.translateLp_apply_ae 2 x
        ((U : WkpAmbientOn 2 2 2 Set.univ) (baseIndex 2 2))
  refine ⟨V, ?_, hn.trans ?_⟩
  · exact (show baseRepresentative V =ᵐ[volume] baseRepresentative B by
      simpa only [baseRepresentative, domainMeasure, Measure.restrict_univ] using hv).trans hb
  · have hbn : ‖B‖ ≤ ‖U‖ := by
      rw [show B = translateH1 x (lowerOrderCLM (by norm_num : 1 ≤ 2) U) from rfl,
        norm_translateH1]
      exact norm_lowerOrderCLM_apply_le _ U
    have hdn (i : Fin 2) : ‖D i‖ ≤ ‖U‖ := by
      dsimp only [D]
      rw [norm_translateH1]
      exact norm_derivativeWordCLM_apply_le _ _ U
    have hsum : ∑ i, ‖D i‖ ≤ 2 * ‖U‖ := by
      simpa only [Fin.sum_univ_two, two_mul] using add_le_add (hdn 0) (hdn 1)
    calc
      _ ≤ succOrderAssemblyNormBound 2 1 * (‖U‖ + 2 * ‖U‖) :=
        mul_le_mul_of_nonneg_left (add_le_add hbn hsum) succOrderAssemblyNormBound_nonneg
      _ = _ := by ring

/-- Continuous representatives of planar H² states have a uniform pointwise bound.
The constant is independent of both the state and the evaluation point. -/
theorem exists_h2_continuous_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : W^{2,2}(ℝ^2)) (g : ℝ^2 → ℝ),
      Continuous g → baseRepresentative U =ᵐ[volume] g →
      ∀ x, ‖g x‖ ≤ C * ‖U‖ := by
  obtain ⟨L, hL⟩ := exists_pointEvaluation (n := 2) (m := 2)
    (by norm_num)  (by norm_num) 0
  refine ⟨‖L‖ * (3 * succOrderAssemblyNormBound 2 1),
    mul_nonneg (norm_nonneg L)
      (mul_nonneg (by norm_num) succOrderAssemblyNormBound_nonneg), ?_⟩
  intro U g hg hrep x
  obtain ⟨V, hv, hn⟩ := exists_h2_translate_bound U x
  have hshift : (fun y ↦ baseRepresentative U (y + x)) =ᵐ[volume]
      (fun y ↦ g (y + x)) := by
    have hpres : MeasurePreserving (Rellich.translationContinuousMap x) volume volume := by
      simpa only [domainMeasure, Measure.restrict_univ] using
        Rellich.translationMeasurePreserving x
    exact hpres.quasiMeasurePreserving.ae_eq_comp hrep
  have heval : L V = g x := by
    simpa only [zero_add] using
      hL V (fun y ↦ g (y + x)) (hg.comp (continuous_id.add continuous_const))
        (hv.trans hshift).symm
  calc
    ‖g x‖ = ‖L V‖ := congrArg norm heval.symm
    _ ≤ ‖L‖ * ‖V‖ := L.le_opNorm V
    _ ≤ ‖L‖ * ((3 * succOrderAssemblyNormBound 2 1) * ‖U‖) :=
      mul_le_mul_of_nonneg_left hn (norm_nonneg L)
    _ = _ := by ring

/-- Every planar Hᵐ graph with `m ≥ 2` has an essentially bounded base coordinate.
One constant works for all orders: restriction to H² does not increase the norm. -/
theorem exists_hk_base_ae_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ), 2 ≤ m →
      ∀ U : W^{m,2}(ℝ^2), ∀ᵐ x ∂volume,
        ‖baseRepresentative U x‖ ≤ C * ‖U‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_h2_continuous_uniform_bound
  refine ⟨C, hC, ?_⟩
  intro m hm U
  let U₂ : W^{2,2}(ℝ^2) := lowerOrderCLM hm U
  obtain ⟨u, hu, hrep⟩ :=
    exists_contDiffAt_representative_of_order (n := 2) (k := 0) (m := 2)
      (by norm_num)  isOpen_univ U₂ (by norm_num)
  have hucont : Continuous u :=
    continuous_iff_continuousAt.mpr fun y ↦ (hu y (Set.mem_univ y)).continuousAt
  have hrep' : u =ᵐ[volume] baseRepresentative U₂ := by
    simpa only [domainMeasure, Measure.restrict_univ] using hrep
  have hbase : baseRepresentative U₂ = baseRepresentative U :=
    baseRepresentative_lowerOrderCLM hm U
  filter_upwards [hrep'] with x hx
  rw [← hbase, ← hx]
  exact (hbound U₂ u hucont hrep'.symm x).trans
    (mul_le_mul_of_nonneg_left (norm_lowerOrderCLM_apply_le hm U) hC)

end SobolevSpace
