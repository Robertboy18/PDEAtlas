/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.EllipticDomain

/-!
# The real whole-space H² resolvent

The operator `1 - Δ` is a continuous linear equivalence from H² to L².
Riesz representation first constructs its H¹ variational solution.
Whole-space elliptic regularity gives H², and the open mapping theorem gives
continuity of the inverse. Thus a continuous L² elliptic load produces a
continuous H² solution without an assumed second-derivative bound.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Laplacian InnerProductSpace

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open PDE.Analysis.Evolution

variable {n : ℕ}

/-- The real whole-space massive Laplacian is bijective from H² onto L². -/
theorem bijective_massiveLaplacian :
    Function.Bijective
      (wkpBaseCoordinateCLM - wkpLaplacianCLM : W^{2,2}(ℝ^n) →L[ℝ] DerivLp n 2 univ) := by
  constructor
  · intro U V h
    have hm :
        massForm n (lowerOrderCLM (by decide : 1 ≤ 2) U) =
          massForm n (lowerOrderCLM (by decide : 1 ≤ 2) V) := by
      rw [massForm_h2, massForm_h2]
      exact congrArg (energyTriple n).pivotToDual h
    have hl := (InnerProductSpace.toDual ℝ H¹(ℝ^n)).injective hm
    apply wkpBaseCoordinateCLM_injective isOpen_univ
    exact congrArg (energyTriple n).inclusion hl
  · intro g
    let u : H¹(ℝ^n) := (InnerProductSpace.toDual ℝ H¹(ℝ^n)).symm ((energyTriple n).pivotToDual g)
    have hm : massForm n u = (energyTriple n).pivotToDual g :=
      (InnerProductSpace.toDual ℝ H¹(ℝ^n)).apply_symm_apply _
    have hg : gradientForm n u =
        -(energyTriple n).pivotToDual ((energyTriple n).inclusion u - g) := by
      change massForm n u - (energyTriple n).energyToDual u = _
      rw [hm, map_sub]
      change (energyTriple n).pivotToDual g -
        (energyTriple n).pivotToDual ((energyTriple n).inclusion u) = _
      abel
    obtain ⟨U, hlow, hΔ⟩ := exists_h2_of_gradientForm_eq u ((energyTriple n).inclusion u - g) hg
    refine ⟨U, ?_⟩
    change wkpBaseCoordinateCLM U - Δ U = g
    have hbase : wkpBaseCoordinateCLM U = (energyTriple n).inclusion u :=
      congrArg (energyTriple n).inclusion hlow
    rw [hbase, hΔ]
    abel

/-- The `1 - Δ` operator and its continuous inverse between real H²
and L². The inverse is constructed from variational solvability and Fourier
elliptic regularity. -/
def massiveLaplacianEquiv (n : ℕ) : W^{2,2}(ℝ^n) ≃L[ℝ] DerivLp n 2 univ :=
  ContinuousLinearEquiv.ofBijective (wkpBaseCoordinateCLM - wkpLaplacianCLM)
    (LinearMap.ker_eq_bot.mpr bijective_massiveLaplacian.injective)
    (LinearMap.range_eq_top.mpr bijective_massiveLaplacian.surjective)

/-- The equivalence acts by the Sobolev base row minus the Laplacian row. -/
theorem massiveLaplacianEquiv_apply (u : W^{2,2}(ℝ^n)) :
    massiveLaplacianEquiv n u = wkpBaseCoordinateCLM u - Δ u := rfl

/-- The inverse of the massive Laplacian recovers any H¹ variational solution
as an H² bundle. -/
theorem lowerOrder_massiveLaplacianEquiv_symm
    (u : H¹(ℝ^n)) (g : DerivLp n 2 univ)
    (h : massForm n u = (energyTriple n).pivotToDual g) :
    lowerOrderCLM (by decide : 1 ≤ 2) ((massiveLaplacianEquiv n).symm g) = u := by
  apply (InnerProductSpace.toDual ℝ H¹(ℝ^n)).injective
  change massForm n _ = massForm n u
  rw [massForm_h2, h, ← massiveLaplacianEquiv_apply, ContinuousLinearEquiv.apply_symm_apply]

end PDE.Hyperbolic.NonlinearWave.Cauchy
