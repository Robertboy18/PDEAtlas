/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Divergence.FirstOrder
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Divergence

/-!
# The physical L² value of vector-valued weak divergence

The positive divergence `∇· u` is a scalar Sobolev graph of order zero.
Its base coordinate is the negative of `negativeDivergence` applied to the
scalar components of `u`. This identity relates the vector-valued operator
to the L² flux used in variational problems without imposing a zero trace
on the field or its components.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued

open GraphSpace

variable {n : ℕ} {Ω : Opens ℝ^n}

/-- The physical L² value of positive weak divergence has the opposite sign
to the variational negative divergence of its unrestricted H¹ components. -/
theorem divergence_baseCoordinate_eq_neg_negativeDivergence (U : W^{1,2}(Ω; ℝ^n)) :
    wkpBaseCoordinateCLM (∇· U) =
      -negativeDivergence (fun i ↦ componentCLM i U) := by
  rw [negativeDivergence, neg_neg]
  apply Lp.ext
  have hdiv :
      (wkpBaseCoordinateCLM (∇· U) : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
        fun x ↦ ∑ i : Fin n, U.val (singleDerivIndex n i) x i := by
    simpa only [wkpBaseCoordinateCLM_apply, derivativeWordIndex, baseIndex_toList,
      List.append_nil, singleDerivIndex] using
      divergence_coordinate_ae U (baseIndex n 0)
  have hrows := ae_all_iff.mpr fun i : Fin n ↦
    componentCLM_apply_ae i U (singleDerivIndex n i)
  filter_upwards [hdiv, hrows, Lp.coeFn_fun_finsetSum Finset.univ
    (fun i ↦ wkpCoordinateCLM (singleDerivIndex n i) (componentCLM i U))]
    with x hx hrow hsum
  exact hx.trans ((Finset.sum_congr rfl fun i _ ↦ (hrow i).symm).trans hsum.symm)

/-- Assembling an arbitrary H¹ family preserves its physical divergence,
with the sign convention used by the variational L² operator. -/
theorem divergence_ofComponentsCLM_baseCoordinate (Q : Fin n → H¹(Ω)) :
    wkpBaseCoordinateCLM (∇· (ofComponentsCLM Q)) = -negativeDivergence Q := by
  simpa only [componentCLM_ofComponentsCLM] using
    divergence_baseCoordinate_eq_neg_negativeDivergence (ofComponentsCLM Q)

end SobolevSpace.VectorValued
