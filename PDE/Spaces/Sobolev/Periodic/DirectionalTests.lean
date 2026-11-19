/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Periodic.LoadedFluxProducts
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Coordinate directions and smooth Sobolev tests

The canonical gradient of a compactly supported smooth test decomposes into
scalar derivative cutoffs times constant coordinate directions. Constant
adjoint pairings then identify directional limits with a constant-coefficient
weak flux.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set TopologicalSpace SobolevSpace.GraphSpace
open scoped ENNReal InnerProductSpace Sobolev Distributions

namespace SobolevSpace.Periodic

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The derivative test represents the derivative cutoff coefficient. -/
theorem testFunctionLpTop_partial (φ : TestFunctionOn n Ω) (i : Fin n) :
    testFunctionLpTop (Ω := Ω) (φ.iteratedPartialDeriv [i]).1 =
      partialTestFunctionLpTop (Ω := Ω) φ.1 i := by
  apply Lp.ext
  filter_upwards [testFunctionLpTop_apply_ae (Ω := Ω) (φ.iteratedPartialDeriv [i]).1,
    partialTestFunctionLpTop_apply_ae (Ω := Ω) φ.1 i] with x hx hy
  exact hx.trans hy.symm

variable [IsFiniteMeasure (volume.restrict Ω)]

/-- The weak gradient of a smooth test is the sum of its scalar derivative
cutoffs times constant coordinate directions. -/
theorem gradient_testFunction_eq_sum (φ : TestFunctionOn n Ω) :
    GraphSpace.gradientCLM (testFunctionToH10 φ) =
      ∑ i : Fin n, partialTestFunctionLpTop (Ω := Ω) φ.1 i •
        Lp.const 2 (volume.restrict Ω) (EuclideanSpace.single i (1 : ℝ)) := by
  classical
  apply Lp.ext
  filter_upwards [GraphSpace.gradientCLM_apply_ae (testFunctionToH10 φ),
    ae_all_iff.mpr (fun i ↦ derivCoordCLM_testFunction_apply_ae i φ),
    Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin n ↦
      partialTestFunctionLpTop (Ω := Ω) φ.1 i •
        Lp.const 2 (volume.restrict Ω) (EuclideanSpace.single i (1 : ℝ))),
    ae_all_iff.mpr (fun i : Fin n ↦ Lp.coeFn_lpSMul (r := 2)
      (partialTestFunctionLpTop (Ω := Ω) φ.1 i)
      (Lp.const 2 (volume.restrict Ω) (EuclideanSpace.single i (1 : ℝ)))),
    ae_all_iff.mpr (fun i : Fin n ↦ Lp.coeFn_const 2 (volume.restrict Ω)
      (EuclideanSpace.single i (1 : ℝ))),
    ae_all_iff.mpr (fun i ↦ partialTestFunctionLpTop_apply_ae (Ω := Ω) φ.1 i)]
    with x hg hd hs hm hc hφ
  change ∀ i : Fin n, (GraphSpace.gradientCLM (testFunctionToH10 φ) x) i = _ at hg
  rw [hs]
  simp only [hm, Pi.smul_apply', hc, hφ]
  apply PiLp.ext
  intro i
  rw [hg i, hd i]
  simp [Pi.single_apply, iteratedPartialDeriv]

/-- Constant adjoint flux pairings equal the corresponding constant-coefficient
flux pairing with a weighted direction. -/
theorem inner_const_adjoint_weighted (B : (ℝ^n) →L[ℝ] (ℝ^n))
    (ξ : ℝ^n) (κ : 𝓓((⊤ : Opens (ℝ^n)), ℝ))
    (v : Lp (ℝ^n) 2 (volume.restrict Ω)) :
    ⟪Lp.const 2 (volume.restrict Ω) (B.adjoint ξ), testFunctionLpTop (Ω := Ω) κ • v⟫_ℝ =
      ⟪B.compLp v, testFunctionLpTop (Ω := Ω) κ •
        Lp.const 2 (volume.restrict Ω) ξ⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 (volume.restrict Ω) (B.adjoint ξ),
    Lp.coeFn_const 2 (volume.restrict Ω) ξ, B.coeFn_compLp v,
    Lp.coeFn_lpSMul (r := 2) (testFunctionLpTop (Ω := Ω) κ) v,
    Lp.coeFn_lpSMul (r := 2) (testFunctionLpTop (Ω := Ω) κ)
      (Lp.const 2 (volume.restrict Ω) ξ)] with x ha hξ hv hm hn
  rw [ha, hm, hn, Pi.smul_apply', Pi.smul_apply', hξ, hv]
  simp only [Function.const_apply]
  rw [real_inner_smul_right, real_inner_smul_right,
    ContinuousLinearMap.adjoint_inner_left, real_inner_comm]

end SobolevSpace.Periodic
