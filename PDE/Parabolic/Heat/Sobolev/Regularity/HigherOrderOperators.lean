/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Sobolev.Regularity.HigherOrder
import PDE.Analysis.MeasureTheory.Lp.Composition.LinearMap

/-!
# Spatial differentiation of the higher-order heat response

The base and first derivative graphs solve heat equations, with
their differentiated forcing and continuous traces. Every commutation
identity is an equality of the native Sobolev operators.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Heat

open MeasureTheory Set
open PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Laplacian Sobolev

variable {n : ℕ} {ε a b : ℝ}

/-- The base graph and each first derivative of an H³/H¹ heat solution
satisfy the H²/L² heat equation, with their differentiated forcing
and continuous H¹ trace. -/
theorem heat_solution_derivativeWord
    (α : List (Fin n)) (hα : α.length ≤ 1)
    (U : Lp (W^{3,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (G F : Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (heq : G =
      (ε • (higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) :
        W^{3,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n))).compLpL
          2 (volume.restrict (Ioc a b)) U + F)
    (hweak : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ lowerOrderCLM (by decide : 1 ≤ 3) (U t)) (fun t ↦ G t))
    (z : ℝ → W^{2,2}(ℝ^n)) (hz : ContinuousOn z (Icc a b))
    (hzU : z =ᵐ[volume.restrict (Ioc a b)]
      (fun t ↦ lowerOrderCLM (by decide : 2 ≤ 3) (U t))) :
    let D : W^{3,2}(ℝ^n) →L[ℝ] W^{2,2}(ℝ^n) := derivativeWordCLM α (by omega)
    let Q : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ :=
      wkpCoordinateCLM (derivIndexOfList α hα)
    let R : W^{2,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := derivativeWordCLM α (by omega)
    Q.compLpL 2 (volume.restrict (Ioc a b)) G =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) (D.compLpL 2 (volume.restrict (Ioc a b)) U) +
      Q.compLpL 2 (volume.restrict (Ioc a b)) F ∧
    HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (D.compLpL 2 (volume.restrict (Ioc a b)) U t))
      (fun t ↦ Q.compLpL 2 (volume.restrict (Ioc a b)) G t) ∧
    ContinuousOn (fun t ↦ R (z t)) (Icc a b) ∧
    (fun t ↦ R (z t)) =ᵐ[volume.restrict (Ioc a b)]
      (fun t ↦ lowerOrderCLM (by decide : 1 ≤ 2)
        (D.compLpL 2 (volume.restrict (Ioc a b)) U t)) := by
  dsimp only
  let ν := volume.restrict (Ioc a b)
  let D : W^{3,2}(ℝ^n) →L[ℝ] W^{2,2}(ℝ^n) := derivativeWordCLM α (by omega)
  let Q : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ :=
    wkpCoordinateCLM (derivIndexOfList α hα)
  let R : W^{2,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := derivativeWordCLM α (by omega)
  let A : W^{3,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := ε • higherOrderLaplacianCLM (by decide)
  let A₂ : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := ε • wkpLaplacianCLM
  have hlap (V : W^{3,2}(ℝ^n)) :
      Q (higherOrderLaplacianCLM (by decide : 1 + 2 ≤ 3) V) =
        Δ (D V) := by
    have hh := congrArg wkpBaseCoordinateCLM
      (derivativeWordCLM_higherOrderLaplacianCLM (s := 0) α (by omega)
        (by decide : 1 + 2 ≤ 3) V)
    rw [higherOrderLaplacianCLM_base, lowerOrderCLM_derivativeWordCLM_apply] at hh
    simpa only [laplacian_eq_wkpLaplacianCLM, wkpBaseCoordinateCLM_apply, derivativeWordCLM_apply,
      derivativeWordIndex_baseIndex, higherOrderLaplacianCLM_base,
      lowerOrderCLM_derivativeWordCLM_apply, Q, D, wkpCoordinateCLM_apply] using hh
  have hQA : Q.comp A = A₂.comp D := by
    simp only [laplacian_eq_wkpLaplacianCLM] at hlap
    ext1 V
    simp only [ContinuousLinearMap.comp_apply, A, A₂, smul_apply, map_smul, hlap]
  have hs : (fun t ↦ Q (lowerOrderCLM (by decide : 1 ≤ 3) (U t))) =ᵐ[ν]
      fun t ↦ wkpBaseCoordinateCLM (D.compLpL 2 ν U t) := by
    filter_upwards [D.coeFn_compLpL U] with t ht
    rw [ht]
    simp only [Q, D, wkpCoordinateCLM_apply, lowerOrderCLM_apply,
      wkpBaseCoordinateCLM_apply, derivativeWordCLM_apply, derivativeWordIndex_baseIndex]
    rfl
  refine ⟨?_, ?_, R.continuous.comp_continuousOn hz, ?_⟩
  · rw [heq, map_add]
    congr 1
    change (Q.compLpL 2 ν).comp (A.compLpL 2 ν) U =
      (A₂.compLpL 2 ν).comp (D.compLpL 2 ν) U
    rw [← ContinuousLinearMap.comp_compLpL, ← ContinuousLinearMap.comp_compLpL, hQA]
  · exact (hweak.map Q).congr_ae_restrict measurableSet_Ioo
      (hs.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
      ((Q.coeFn_compLpL G).symm.filter_mono
        (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
  · filter_upwards [hzU, D.coeFn_compLpL U] with t hzt hDt
    change R (z t) = lowerOrderCLM (by decide : 1 ≤ 2) (D.compLpL 2 ν U t)
    rw [hzt, hDt]
    simp only [R, D, derivativeWordCLM_lowerOrderCLM_apply,
      lowerOrderCLM_derivativeWordCLM_apply]

end PDE.Parabolic.Heat
