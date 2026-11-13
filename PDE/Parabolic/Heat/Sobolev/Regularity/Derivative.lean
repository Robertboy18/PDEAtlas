/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Sobolev.Energy.Estimates
public import PDE.Parabolic.Heat.Sobolev.Regularity.SpatialOperators
public import PDE.Spaces.Sobolev.Approximation.Mollification.BochnerRegularity
public import PDE.Spaces.Sobolev.GraphSpace.Norms.FirstDerivatives
import PDE.Analysis.MeasureTheory.Lp.Composition.LinearMap

/-!
# Spatial regularity of the heat evolution

For H² initial data and H¹ forcing, solve the heat equation for each first
spatial derivative. Differentiated mollification and heat uniqueness identify
those solutions with the derivatives of the original state. Their H² bounds
then recover a measurable H³ state by weak compactness.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Heat

open Filter MeasureTheory Set
open PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped ENNReal Laplacian Topology Sobolev

variable {n : ℕ} {ε a b : ℝ}

/-- Each first derivative of a heat trajectory has an H² Bochner graph
after identification through every positive-scale mollifier. The
derivative graph comes from heat existence and is not a hypothesis. -/
theorem exists_heat_firstDerivative_mollification
    (hε : 0 < ε) (hab : a < b)
    (q : W^{2,2}(ℝ^n))
    (F : Lp (W^{1,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (u : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (g : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (heq : g =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) u +
      (wkpBaseCoordinateCLM : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ).compLpL
        2 (volume.restrict (Ioc a b)) F)
    (hweak : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (u t)) (fun t ↦ g t))
    (z : ℝ → W^{1,2}(ℝ^n)) (hz : ContinuousOn z (Icc a b))
    (hzu : z =ᵐ[volume.restrict (Ioc a b)] fun t ↦ lowerOrderCLM (by decide : 1 ≤ 2) (u t))
    (hinit : z a = lowerOrderCLM (by decide : 1 ≤ 2) q) (i : Fin n) :
    ∃ v : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)),
      ∀ (δ : ℝ) (hδ : 0 < δ),
        ((mollifierSmoothingCLM 2 (standardMollifier n) hδ).comp
          (wkpCoordinateCLM (derivIndexOfList [i] (by simp : [i].length ≤ 2)) :
            W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
            2 (volume.restrict (Ioc a b)) u =
        (mollifierHkCLM (k := 2) (standardMollifier n) hδ).compLpL
          2 (volume.restrict (Ioc a b)) v := by
  let ν := volume.restrict (Ioc a b)
  let P : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := wkpBaseCoordinateCLM
  let D : W^{1,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ :=
    wkpCoordinateCLM (derivIndexOfList [i] (by simp))
  let Dq : W^{2,2}(ℝ^n) →L[ℝ] W^{1,2}(ℝ^n) := partialDerivCLM i
  let F₁ : Lp (DerivLp n 2 univ) 2 ν := D.compLpL 2 ν F
  obtain ⟨v, h, w, heqv, _, hweakv, hw, hwv, hwinit, _⟩ :=
    exists_heat_solution hε hab F₁ (Dq q)
  refine ⟨v, fun δ hδ ↦ ?_⟩
  let μ := standardMollifier n
  let Q : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ :=
    wkpCoordinateCLM (derivIndexOfList [i] (by simp))
  let T : W^{2,2}(ℝ^n) →L[ℝ] W^{2,2}(ℝ^n) :=
    (mollifierSmoothingCLM 2 μ hδ).comp Q
  let R := differentiatedMollifierCLM [i] μ hδ
  let J := mollifierRowCLM μ hδ
  let K := mollifierHkCLM (k := 2) μ hδ
  have hTbase (U : W^{2,2}(ℝ^n)) :
      wkpBaseCoordinateCLM (T U) = R (wkpBaseCoordinateCLM U) := by
    exact (mollifierSmoothingCLM_base 2 μ hδ (Q U)).trans
      (differentiatedMollifierCLM_baseCoordinate [i] (by simp) μ hδ U).symm
  have hTlap (U : W^{2,2}(ℝ^n)) :
      Δ (T U) = R (Δ U) :=
    (differentiatedMollifierCLM_laplacian i μ hδ U).symm
  have hKbase (U : W^{2,2}(ℝ^n)) :
      wkpBaseCoordinateCLM (K U) = J (wkpBaseCoordinateCLM U) := rfl
  have hKlap (U : W^{2,2}(ℝ^n)) :
      Δ (K U) = J (Δ U) := by
    simp only [laplacian_eq_wkpLaplacianCLM, K, J, wkpLaplacianCLM_apply,
      mollifierHkCLM_coordinate, map_sum]
  obtain ⟨heqT, hweakT⟩ := heat_solution_map T R hTbase hTlap u g
    (P.compLpL 2 ν F) heq hweak
  obtain ⟨heqK, hweakK⟩ := heat_solution_map K J hKbase hKlap v h F₁ heqv hweakv
  have hRD : R.comp P = J.comp D := by
    ext1 U
    exact differentiatedMollifierCLM_baseCoordinate [i] (by simp) μ hδ U
  have hforcing : R.compLpL 2 ν (P.compLpL 2 ν F) = J.compLpL 2 ν F₁ := by
    change (R.compLpL 2 ν).comp (P.compLpL 2 ν) F =
      (J.compLpL 2 ν).comp (D.compLpL 2 ν) F
    rw [← ContinuousLinearMap.comp_compLpL, ← ContinuousLinearMap.comp_compLpL, hRD]
  rw [← hforcing] at heqK
  let zT (t : ℝ) := R (P (z t))
  let zK (t : ℝ) := J (P (w t))
  have hzT : ContinuousOn zT (Icc a b) :=
    R.continuous.comp_continuousOn (P.continuous.comp_continuousOn hz)
  have hzK : ContinuousOn zK (Icc a b) :=
    J.continuous.comp_continuousOn (P.continuous.comp_continuousOn hw)
  have hzTu : zT =ᵐ[ν] fun t ↦ wkpBaseCoordinateCLM (T.compLpL 2 ν u t) := by
    filter_upwards [hzu, T.coeFn_compLpL u] with t ht hTt
    rw [hTt, hTbase]
    change R (P (z t)) = _
    rw [ht]
    rfl
  have hzKv : zK =ᵐ[ν] fun t ↦ wkpBaseCoordinateCLM (K.compLpL 2 ν v t) := by
    filter_upwards [hwv, K.coeFn_compLpL v] with t ht hKt
    rw [hKt, hKbase]
    change J (P (w t)) = _
    rw [ht]
    rfl
  have hzinit : zT a = zK a := by
    change R (P (z a)) = J (P (w a))
    rw [hinit, hwinit]
    change R (wkpBaseCoordinateCLM q) = J (P (Dq q))
    rw [differentiatedMollifierCLM_baseCoordinate [i] (by simp)]
    simp only [J, P, Dq, partialDerivCLM, wkpBaseCoordinateCLM_apply, derivativeWordCLM_apply,
      derivativeWordIndex_baseIndex, wkpCoordinateCLM_apply]
  exact (heat_solution_unique hε.le (T.compLpL 2 ν u) (K.compLpL 2 ν v)
    (R.compLpL 2 ν g) (J.compLpL 2 ν h) (R.compLpL 2 ν (P.compLpL 2 ν F))
    hweakT hweakK heqT heqK zT zK hzT hzK hzTu hzKv hzinit).1

end PDE.Parabolic.Heat
