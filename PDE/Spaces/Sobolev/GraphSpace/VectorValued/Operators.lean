/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Notation
import PDE.Analysis.Normed.PiLp.Coordinatewise

/-!
# Continuous linear maps on Banach-valued Sobolev spaces

A continuous linear map of codomains acts on every derivative coordinate through Mathlib's
`ContinuousLinearMap.compLpL`. The weak derivative transport theorem ensures that this
coordinatewise map preserves the Sobolev graph.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n k : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω : Opens ℝ^n}
  {F G H : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

/-- Apply a continuous linear map to all `Lp` derivative coordinates. -/
def ambientMapCLM (L : F →L[ℝ] G) :
    WkpAmbientOn n k p Ω F →L[ℝ] WkpAmbientOn n k p Ω G :=
  (PiLp.continuousLinearEquiv p ℝ
    (fun _ : DerivIndex n k ↦ Lp G p (domainMeasure n Ω))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a ↦
      (L.compLpL p (domainMeasure n Ω)).comp
        (PiLp.proj p (fun _ : DerivIndex n k ↦ Lp F p (domainMeasure n Ω)) a))

omit [CompleteSpace F] [CompleteSpace G] in
/-- Each mapped coordinate is Mathlib's map on `Lp`. -/
@[simp] theorem ambientMapCLM_apply (L : F →L[ℝ] G)
    (U : WkpAmbientOn n k p Ω F) (a : DerivIndex n k) :
    ambientMapCLM L U a = L.compLpL p (domainMeasure n Ω) (U a) :=
  rfl

/-- Continuous linear codomain maps preserve every weak derivative constraint. -/
theorem IsWkpOn.ambientMapCLM {U : WkpAmbientOn n k p Ω F}
    (hU : IsWkpOn U) (L : F →L[ℝ] G) : IsWkpOn (ambientMapCLM L U) := by
  intro a
  exact ((hU a).map L).congr_ae (L.coeFn_compLpL (U (baseIndex n k))).symm
    (L.coeFn_compLpL (U a)).symm

/-- A continuous linear codomain map induces a continuous linear map of Sobolev spaces. -/
def mapCLM (L : F →L[ℝ] G) : W^{k,p}(Ω; F) →L[ℝ] W^{k,p}(Ω; G) :=
  ((ambientMapCLM L).comp (wkpSubmoduleOn n k p Ω F).subtypeL).codRestrict
    (wkpSubmoduleOn n k p Ω G) (fun U ↦ U.property.ambientMapCLM L)

/-- Codomain transport commutes exactly with each derivative coordinate. -/
@[simp] theorem mapCLM_apply (L : F →L[ℝ] G)
    (U : W^{k,p}(Ω; F)) (a : DerivIndex n k) :
    (mapCLM L U).val a = L.compLpL p (domainMeasure n Ω) (U.val a) :=
  rfl

/-- A mapped derivative representative is almost everywhere the original one composed with `L`. -/
theorem mapCLM_apply_ae (L : F →L[ℝ] G) (U : W^{k,p}(Ω; F))
    (a : DerivIndex n k) :
    ((mapCLM L U).val a : ℝ^n → G) =ᵐ[domainMeasure n Ω] fun x ↦ L (U.val a x) :=
  L.coeFn_compLpL (U.val a)

/-- A codomain map has the same norm bound on Sobolev functions as on point values. -/
theorem norm_mapCLM_apply_le (L : F →L[ℝ] G) (U : W^{k,p}(Ω; F)) :
    ‖mapCLM L U‖ ≤ ‖L‖ * ‖U‖ :=
  PiLp.norm_le_mul_of_norm_apply_le _ _ (norm_nonneg L) fun _ ↦
    L.norm_compLp_le _

/-- Passing to Sobolev spaces does not increase the norm of a linear codomain map. -/
theorem norm_mapCLM_le (L : F →L[ℝ] G) :
    ‖mapCLM (n := n) (k := k) (p := p) (Ω := Ω) L‖ ≤ ‖L‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L) (norm_mapCLM_apply_le L)

/-- The identity on the codomain leaves the Sobolev bundle unchanged. -/
@[simp] theorem mapCLM_id (U : W^{k,p}(Ω; F)) :
    mapCLM (ContinuousLinearMap.id ℝ F) U = U := by
  apply WkpSpaceOn.ext_of_base_ae
  exact mapCLM_apply_ae _ U (baseIndex n k)

/-- Successive codomain maps agree with their composition. -/
@[simp] theorem mapCLM_comp (L : F →L[ℝ] G) (M : G →L[ℝ] H)
    (U : W^{k,p}(Ω; F)) :
    mapCLM (M.comp L) U = mapCLM M (mapCLM L U) := by
  apply WkpSpaceOn.ext_of_base_ae
  exact (mapCLM_apply_ae (M.comp L) U (baseIndex n k)).trans
    (((mapCLM_apply_ae L U (baseIndex n k)).fun_comp M).symm.trans
      (mapCLM_apply_ae M (mapCLM L U) (baseIndex n k)).symm)

end SobolevSpace.VectorValued
