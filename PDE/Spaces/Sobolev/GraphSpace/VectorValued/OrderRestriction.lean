/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.OrderRestriction
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Notation
import PDE.Analysis.Normed.PiLp.Coordinatewise

/-!
# Lowering the order of a Banach-valued Sobolev function

The inclusion `W^{m,p}(Ω; F) → W^{k,p}(Ω; F)` for `k ≤ m` forgets the higher
derivative coordinates. It is a contraction in the graph norm, and its remaining
coordinates represent exactly the same weak derivatives.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k m r : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Forget derivative coordinates above order `k`. -/
def lowerOrderAmbientCLM (hkm : k ≤ m) :
    WkpAmbientOn n m p Ω F →L[ℝ] WkpAmbientOn n k p Ω F :=
  (PiLp.continuousLinearEquiv p ℝ
    (fun _ : DerivIndex n k ↦ Lp F p (domainMeasure n Ω))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦
      PiLp.proj p (fun _ : DerivIndex n m ↦ Lp F p (domainMeasure n Ω)) (a.castOrder hkm))

omit [CompleteSpace F] in
/-- Lowering the order preserves each retained derivative coordinate. -/
@[simp] theorem lowerOrderAmbientCLM_apply (hkm : k ≤ m)
    (U : WkpAmbientOn n m p Ω F) (a : DerivIndex n k) :
    lowerOrderAmbientCLM hkm U a = U (a.castOrder hkm) :=
  rfl

/-- The canonical inclusion of a higher-order Sobolev space into a lower-order one. -/
def lowerOrderCLM (hkm : k ≤ m) : W^{m,p}(Ω; F) →L[ℝ] W^{k,p}(Ω; F) :=
  ((lowerOrderAmbientCLM hkm).comp (wkpSubmoduleOn n m p Ω F).subtypeL).codRestrict
    (wkpSubmoduleOn n k p Ω F) fun U a ↦ by
      simpa only [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
        lowerOrderAmbientCLM_apply, DerivIndex.castOrder_baseIndex,
        DerivIndex.castOrder_toList] using U.property (a.castOrder hkm)

/-- Each retained coordinate is the original `Lp` class. -/
@[simp] theorem lowerOrderCLM_apply (hkm : k ≤ m)
    (U : W^{m,p}(Ω; F)) (a : DerivIndex n k) :
    (lowerOrderCLM hkm U).val a = U.val (a.castOrder hkm) :=
  rfl

/-- Lowering the order does not increase the Sobolev norm. -/
theorem norm_lowerOrderCLM_apply_le (hkm : k ≤ m) (U : W^{m,p}(Ω; F)) :
    ‖lowerOrderCLM hkm U‖ ≤ ‖U‖ :=
  PiLp.norm_mono_of_injective
    (DerivIndex.castOrder hkm) (DerivIndex.castOrder_injective hkm) _ _ fun _ ↦ le_rfl

/-- The order inclusion has operator norm at most one. -/
theorem norm_lowerOrderCLM_le (hkm : k ≤ m) :
    ‖lowerOrderCLM (F := F) (n := n) (p := p) (Ω := Ω) hkm‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro U
  simpa only [one_mul] using norm_lowerOrderCLM_apply_le hkm U

/-- Keeping the same derivative order is the identity map. -/
@[simp] theorem lowerOrderCLM_refl :
    lowerOrderCLM (F := F) (n := n) (p := p) (Ω := Ω) (le_refl k) =
      ContinuousLinearMap.id ℝ W^{k,p}(Ω; F) := by
  ext U : 1
  apply WkpSpaceOn.ext_of_base_ae
  simp only [lowerOrderCLM_apply, DerivIndex.castOrder_baseIndex,
    ContinuousLinearMap.id_apply]
  exact Filter.EventuallyEq.rfl

/-- Lowering the order twice agrees with the direct inclusion. -/
theorem lowerOrderCLM_trans (hkm : k ≤ m) (hmr : m ≤ r) :
    (lowerOrderCLM (F := F) (n := n) (p := p) (Ω := Ω) hkm).comp (lowerOrderCLM hmr) =
      lowerOrderCLM (hkm.trans hmr) := by
  ext U : 1
  apply WkpSpaceOn.ext_of_base_ae
  simp only [ContinuousLinearMap.comp_apply, lowerOrderCLM_apply,
    DerivIndex.castOrder_baseIndex]
  exact Filter.EventuallyEq.rfl

end SobolevSpace.VectorValued
