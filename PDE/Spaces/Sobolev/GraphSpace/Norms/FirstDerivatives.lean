/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Slicing.FirstOrderAssembly
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivatives
import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Sobolev graph norms from first derivative graphs

The graph counts each symmetric multi-index once. Its norm is
controlled by the base L² norm and the graph norms of all first derivatives.
This comparison, also for Bochner curves, does not identify that norm with
an ordered derivative tensor norm.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

variable {n k : ℕ} {Ω : Set ℝ^n}

/-- The graph norm of order `k+1` is controlled by the base norm and the
order-`k` graphs of the first derivatives, on any open domain. -/
theorem norm_le_base_add_firstDerivatives (hΩ : IsOpen Ω)
    (U : W^{k + 1,2}(Ω)) :
    ‖U‖ ≤ succOrderAssemblyNormBound n k *
      (‖wkpBaseCoordinateCLM U‖ +
        ∑ i : Fin n, ‖∂[i] U‖) := by
  let V (i : Fin n) : W^{k,2}(Ω) :=
    ∂[i] U
  have hV (i : Fin n) :
      HasWeakDerivativeOn Ω [i] (baseRepresentative U) (baseRepresentative (V i)) := by
    dsimp only [V]
    rw [partialDerivCLM, baseRepresentative_derivativeWordCLM]
    exact U.property.hasWeakDerivativeOn_list [i] (by simp)
  obtain ⟨W, hW, hb⟩ := exists_succOrder_of_memLp_of_firstDerivatives
    (baseRepresentative U) (Lp.memLp _) V hV
  have hWU : W = U := wkpBaseCoordinateCLM_injective hΩ (Lp.ext hW)
  subst W
  exact hb

/-- The same comparison holds for the Bochner L² norm. In particular,
uniform first-derivative graph bounds control the whole higher graph. -/
theorem norm_Lp_le_base_add_firstDerivatives
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (hΩ : IsOpen Ω) (u : Lp (W^{k + 1,2}(Ω)) 2 μ) :
    ‖u‖ ≤ succOrderAssemblyNormBound n k *
      (‖(wkpBaseCoordinateCLM : W^{k + 1,2}(Ω) →L[ℝ] DerivLp n 2 Ω).compLpL
          2 μ u‖ +
        ∑ i : Fin n, ‖(partialDerivCLM i :
          W^{k + 1,2}(Ω) →L[ℝ] W^{k,2}(Ω)).compLpL 2 μ u‖) := by
  classical
  let P : W^{k + 1,2}(Ω) →L[ℝ] DerivLp n 2 Ω := wkpBaseCoordinateCLM
  let D (i : Fin n) : W^{k + 1,2}(Ω) →L[ℝ] W^{k,2}(Ω) :=
    partialDerivCLM i
  let C := succOrderAssemblyNormBound n k
  have hC : 0 ≤ C := by unfold C succOrderAssemblyNormBound; positivity
  have hP : MemLp (fun x ↦ ‖P (u x)‖) 2 μ := (P.comp_memLp u).norm
  have hD (i : Fin n) : MemLp (fun x ↦ ‖D i (u x)‖) 2 μ := ((D i).comp_memLp u).norm
  have hsum : MemLp (fun x ↦ ∑ i, ‖D i (u x)‖) 2 μ :=
    memLp_finsetSum Finset.univ fun i _ ↦ hD i
  have hb := hP.add hsum
  have hnormP : lpNorm (fun x ↦ ‖P (u x)‖) 2 μ = ‖P.compLpL 2 μ u‖ := by
    rw [lpNorm_norm (f := fun x ↦ P (u x)) (P.comp_memLp u).aestronglyMeasurable]
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae (P.coeFn_compLpL u).symm)
  have hnormD (i : Fin n) :
      lpNorm (fun x ↦ ‖D i (u x)‖) 2 μ = ‖(D i).compLpL 2 μ u‖ := by
    rw [lpNorm_norm (f := fun x ↦ D i (u x)) ((D i).comp_memLp u).aestronglyMeasurable]
    exact congrArg ENNReal.toReal (eLpNorm_congr_ae ((D i).coeFn_compLpL u).symm)
  change lpNorm u 2 μ ≤ _
  calc
    _ ≤ lpNorm (fun x ↦ C * (‖P (u x)‖ + ∑ i, ‖D i (u x)‖)) 2 μ :=
      lpNorm_mono_real (hb.const_mul C) (fun x ↦ norm_le_base_add_firstDerivatives hΩ (u x))
    _ = C * lpNorm (fun x ↦ ‖P (u x)‖ + ∑ i, ‖D i (u x)‖) 2 μ := by
      simpa only [Pi.smul_def, smul_eq_mul, coe_nnnorm, Real.norm_of_nonneg hC] using
        lpNorm_const_smul C (fun x ↦ ‖P (u x)‖ + ∑ i, ‖D i (u x)‖) μ (p := 2)
    _ ≤ C * (lpNorm (fun x ↦ ‖P (u x)‖) 2 μ +
        lpNorm (fun x ↦ ∑ i, ‖D i (u x)‖) 2 μ) :=
      mul_le_mul_of_nonneg_left (lpNorm_add_le hP (by norm_num)) hC
    _ ≤ C * (‖P.compLpL 2 μ u‖ + ∑ i, ‖(D i).compLpL 2 μ u‖) := by
      apply mul_le_mul_of_nonneg_left _ hC
      rw [hnormP]
      apply add_le_add_right
      have hh := lpNorm_sum_le (fun i (_ : i ∈ Finset.univ) ↦ hD i) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      simpa only [Finset.sum_fn, hnormD] using hh

end SobolevSpace.GraphSpace
