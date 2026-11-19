/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.Affine.IteratedDerivative
public import PDE.Analysis.Calculus.Jet.CoordinateChange
public import PDE.Analysis.Calculus.LocalExtension

/-!
# Ordinary normal derivatives and coordinate expansion

The normal derivative is the ordinary derivative of the restriction to the
normal line. At an analytic germ, its coordinate expansion sums over ordered
coordinate tuples. Thus mixed partials occur with their multinomial multiplicity;
no change to the coefficients of a differential operator is involved.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace PDE.Analysis.MultiIndex

variable {n j : ℕ} {u : ℝ^n → ℝ} {x : ℝ^n}

/-- Finite differentiability at the base point suffices to identify normal
data with the ordinary derivative along the fixed normal line. -/
theorem normalData_eq_iteratedDeriv (hu : ContDiffAt ℝ j u x) (ν : ℝ^n) :
    normalData j u ν x = iteratedDeriv j (fun t : ℝ ↦ u (x + t • ν)) 0 := by
  obtain ⟨v, hv, -, heq⟩ := hu.exists_contDiff_compactSupport_eventuallyEq
  have hline : (fun t : ℝ ↦ u (x + t • ν)) =ᶠ[𝓝 0]
      (fun t : ℝ ↦ v (x + t • ν)) :=
    heq.comp_tendsto (by
      have hc : ContinuousAt (fun t : ℝ ↦ x + t • ν) 0 := by fun_prop
      simpa only [zero_smul, add_zero] using hc.tendsto)
  rw [(hline.iteratedDeriv j).self_of_nhds]
  have hvline := iteratedDeriv_comp_affine_line hv x ν 0 le_rfl (r := j)
  simp only [zero_smul, add_zero] at hvline
  rw [hvline]
  exact congrArg (fun A ↦ A (fun _ : Fin j ↦ ν))
    ((heq.iteratedFDeriv ℝ j).self_of_nhds)

/-- Each ordered coordinate tuple contributes once to the normal derivative.
Tuples with the same multiindex give the usual multinomial weight. -/
theorem normalData_eq_sum_coordinateDeriv (hu : AnalyticAt ℝ u x) (ν : ℝ^n) :
    normalData j u ν x =
      ∑ a : Fin j → Fin n,
        coordinateDeriv (Sym.ofVector (List.Vector.ofFn a)) u x * ∏ i, ν (a i) := by
  rw [normalData, ← multilinearFromCoordinates_coordinateDeriv hu j,
    multilinearFromCoordinates_apply]

end PDE.Analysis.MultiIndex
