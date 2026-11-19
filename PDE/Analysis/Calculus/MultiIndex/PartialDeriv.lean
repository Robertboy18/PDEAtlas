/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.MultiIndex.CoordinateJet
public import PDE.FDeriv.PartialDeriv

/-!
# Pure multiindices and coordinate derivative words

A pure multiindex evaluates the ordinary jet on repeated copies of one basis
vector. The coordinate-derivative theorem identifies this value with
the corresponding repeated partial, under local finite-order regularity.
-/

@[expose] public noncomputable section

namespace PDE.Analysis.MultiIndex

/-- A pure multiindex agrees with the repeated coordinate partial. -/
theorem coordinateDeriv_replicate {n j : ℕ} (i : Fin n)
    {u : ℝ^n → ℝ} {x : ℝ^n} (hu : ContDiffAt ℝ j u x) :
    coordinateDeriv (Sym.replicate j i) u x = ((partialDeriv i)^[j] u) x := by
  have hd : directions (Sym.replicate j i) =
      fun _ : Fin j ↦ EuclideanSpace.single i (1 : ℝ) := by
    funext a
    change EuclideanSpace.basisFun (Fin n) ℝ ((Sym.replicate j i).sortedTuple a) = _
    rw [Sym.sortedTuple_replicate, EuclideanSpace.basisFun_apply]
  rw [coordinateDeriv, hd]
  exact (iterate_partialDeriv_eq_iteratedFDeriv_single i j hu).symm

end PDE.Analysis.MultiIndex
