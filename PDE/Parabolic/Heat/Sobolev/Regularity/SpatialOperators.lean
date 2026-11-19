/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Sobolev.Uniqueness
public import PDE.Spaces.Sobolev.Approximation.Mollification.Differentiated
import PDE.Analysis.MeasureTheory.Lp.Composition.LinearMap

/-!
# Spatial operators acting on heat trajectories

Bounded maps which commute with the native base coordinate and Laplacian
preserve the heat equation and its weak time derivative. Applying
this to mollification and to differentiated mollification identifies spatial
derivatives through heat uniqueness.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.Heat

open MeasureTheory Set
open PDE.Analysis.Evolution
open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Approximation
open scoped ENNReal Laplacian Sobolev

variable {n : ℕ} {ε a b : ℝ}

/-- A compatible bounded spatial operator preserves the heat equation
and weak time derivative on the open time interval. -/
theorem heat_solution_map
    (T : W^{2,2}(ℝ^n) →L[ℝ] W^{2,2}(ℝ^n))
    (R : DerivLp n 2 univ →L[ℝ] DerivLp n 2 univ)
    (hbase : ∀ U, wkpBaseCoordinateCLM (T U) = R (wkpBaseCoordinateCLM U))
    (hlap : ∀ U, Δ (T U) = R (Δ U))
    (u : Lp (W^{2,2}(ℝ^n)) 2 (volume.restrict (Ioc a b)))
    (g F : Lp (DerivLp n 2 univ) 2 (volume.restrict (Ioc a b)))
    (heq : g =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b)) u + F)
    (hweak : HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (u t)) (fun t ↦ g t)) :
    R.compLpL 2 (volume.restrict (Ioc a b)) g =
      (ε • (wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ)).compLpL
        2 (volume.restrict (Ioc a b))
        (T.compLpL 2 (volume.restrict (Ioc a b)) u) +
      R.compLpL 2 (volume.restrict (Ioc a b)) F ∧
    HasWeakTimeDerivativeOn (Ioo a b)
      (fun t ↦ wkpBaseCoordinateCLM (T.compLpL 2 (volume.restrict (Ioc a b)) u t))
      (fun t ↦ R.compLpL 2 (volume.restrict (Ioc a b)) g t) := by
  simp only [laplacian_eq_wkpLaplacianCLM] at hlap
  let ν := volume.restrict (Ioc a b)
  let A : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ := ε • wkpLaplacianCLM
  have hRA : R.comp A = A.comp T := by
    ext1 U
    simp only [ContinuousLinearMap.comp_apply, A, smul_apply, map_smul, hlap]
  constructor
  · rw [heq, map_add]
    congr 1
    change (R.compLpL 2 ν).comp (A.compLpL 2 ν) u =
      (A.compLpL 2 ν).comp (T.compLpL 2 ν) u
    rw [← ContinuousLinearMap.comp_compLpL, ← ContinuousLinearMap.comp_compLpL, hRA]
  · have hstate : (fun t ↦ R (wkpBaseCoordinateCLM (u t))) =ᵐ[ν]
        fun t ↦ wkpBaseCoordinateCLM (T.compLpL 2 ν u t) := by
      filter_upwards [T.coeFn_compLpL u] with t ht
      rw [ht, hbase]
    exact (hweak.map R).congr_ae_restrict measurableSet_Ioo
      (hstate.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))
      ((R.coeFn_compLpL g).symm.filter_mono
        (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self)))

end PDE.Parabolic.Heat
