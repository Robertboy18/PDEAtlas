/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.MultiIndex.CoordinateJet
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Linear operations on coordinate derivatives and normal data

Finite differentiability at the evaluation point suffices for addition and
subtraction of mixed coordinate derivatives, and for addition of the
normal Cauchy data.
-/

@[expose] public section

namespace PDE.Analysis.MultiIndex

variable {n j : ℕ} {u v : ℝ^n → ℝ} {x : ℝ^n}

/-- A mixed derivative distributes over addition under the corresponding
finite differentiability hypotheses. -/
theorem coordinateDeriv_add (α : Sym (Fin n) j)
    (hu : ContDiffAt ℝ j u x) (hv : ContDiffAt ℝ j v x) :
    coordinateDeriv α (u + v) x = coordinateDeriv α u x + coordinateDeriv α v x := by
  unfold coordinateDeriv
  rw [iteratedFDeriv_add_apply hu hv, add_apply]

/-- A mixed derivative distributes over subtraction under the corresponding
finite differentiability hypotheses. -/
theorem coordinateDeriv_sub (α : Sym (Fin n) j)
    (hu : ContDiffAt ℝ j u x) (hv : ContDiffAt ℝ j v x) :
    coordinateDeriv α (u - v) x = coordinateDeriv α u x - coordinateDeriv α v x := by
  unfold coordinateDeriv
  rw [iteratedFDeriv_sub_apply hu hv, sub_apply]

/-- Normal data distribute over addition under finite differentiability
at the evaluation point. -/
theorem normalData_add (hu : ContDiffAt ℝ j u x) (hv : ContDiffAt ℝ j v x) (ν : ℝ^n) :
    normalData j (u + v) ν x = normalData j u ν x + normalData j v ν x := by
  unfold normalData
  rw [iteratedFDeriv_add_apply hu hv, add_apply]

/-- Scaling the normal scales the datum of order `j` by the `j`th power. -/
theorem normalData_smul (u : ℝ^n → ℝ) (r : ℝ) (ν x : ℝ^n) :
    normalData j u (r • ν) x = r ^ j * normalData j u ν x := by
  simp only [normalData, ContinuousMultilinearMap.map_smul_univ,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end PDE.Analysis.MultiIndex
