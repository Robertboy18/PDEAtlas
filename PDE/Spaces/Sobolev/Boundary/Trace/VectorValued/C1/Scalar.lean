/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.FiniteExponentOperator
public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.C1.Operator

/-!
# Scalar compatibility of the Banach-valued C¹ trace

The scalar identification preserves all Sobolev coordinates and the graph norm.
Both trace operators give literal boundary restriction on ambient smooth test functions.
Density of this core for finite exponents therefore identifies the continuous operators.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.C1

open GraphSpace

variable {m : ℕ} {Ω : Opens ℝ^(m + 1)}
  [Boundary.C1ExtensionAtlas (m + 1) (Ω : Set ℝ^(m + 1))]
  {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- Transporting the Banach-valued trace through the scalar isometry gives the scalar
surface trace as an equality of continuous linear operators. -/
theorem traceLp_comp_scalarEquiv_symm (hp : 1 ≤ p) :
    (traceLp (Ω := Ω) (F := ℝ) p hp).comp
        scalarEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap =
      SobolevSpace.Trace.C1.traceLp (Ω := (Ω : Set ℝ^(m + 1))) p := by
  let lhs := (traceLp (Ω := Ω) (F := ℝ) p hp).comp
    scalarEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let rhs := SobolevSpace.Trace.C1.traceLp (Ω := (Ω : Set ℝ^(m + 1))) p
  have hcore : (lhs : _ → _) ∘
      SobolevSpace.Trace.C1.globalTestFunctionToDomainW1pLinear
        (Ω := (Ω : Set ℝ^(m + 1))) (ENNReal.ofReal p) =
      (rhs : _ → _) ∘
      SobolevSpace.Trace.C1.globalTestFunctionToDomainW1pLinear
        (Ω := (Ω : Set ℝ^(m + 1))) (ENNReal.ofReal p) := by
    funext φ
    change traceLp p hp
      (scalarEquiv.symm (SobolevSpace.Trace.C1.globalTestFunctionToDomainW1pLinear
        (Ω := (Ω : Set ℝ^(m + 1))) (ENNReal.ofReal p) φ)) =
      SobolevSpace.Trace.C1.traceLp p
        (SobolevSpace.Trace.C1.globalTestFunctionToDomainW1pLinear
          (Ω := (Ω : Set ℝ^(m + 1))) (ENNReal.ofReal p) φ)
    rw [SobolevSpace.Trace.C1.traceLp_classical]
    apply Lp.ext
    have hbase :
        ((scalarEquiv.symm
          (SobolevSpace.Trace.C1.globalTestFunctionToDomainW1pLinear
            (Ω := (Ω : Set ℝ^(m + 1))) (ENNReal.ofReal p) φ)).val
          (baseIndex (m + 1) 1) : ℝ^(m + 1) → ℝ)
          =ᵐ[domainMeasure (m + 1) Ω] φ.1.toFun := by
      rw [scalarEquiv_symm_coordinate,
        SobolevSpace.Trace.C1.globalTestFunctionToDomainW1pLinear_eq_mk]
      simpa only [baseIndex_toList, iteratedPartialDeriv] using
        mkWkpSpaceOnOfContDiff_apply_ae (k := 1) (p := ENNReal.ofReal p)
          (Ω := (Ω : Set ℝ^(m + 1))) φ.1.toFun φ.1.contDiff φ.1.hasCompactSupport
          (baseIndex (m + 1) 1)
    exact (traceLp_coeFn_ae hp _ (φ.1.contDiff.of_le (by simp)) hbase).trans
      (SobolevSpace.Trace.C1.globalTestFunctionBoundaryLpLinear_apply_ae
        (Ω := (Ω : Set ℝ^(m + 1))) (ENNReal.ofReal p) φ).symm
  have hfun :=
    (SobolevSpace.Trace.C1.denseRange_globalTestFunctionToDomainW1pLinear
      (Ω := (Ω : Set ℝ^(m + 1))) (ENNReal.ofReal p) ENNReal.ofReal_ne_top).equalizer
      lhs.continuous rhs.continuous hcore
  apply ContinuousLinearMap.ext
  intro U
  exact congrFun hfun U

/-- The physical trace at real codomain agrees with the scalar trace under the
coordinate-preserving scalar identification. -/
theorem traceLp_eq_scalar_traceLp (hp : 1 ≤ p) (U : W^{1,ENNReal.ofReal p}(Ω; ℝ)) :
    traceLp p hp U = SobolevSpace.Trace.C1.traceLp p (scalarEquiv U) := by
  have h := congrArg (fun T ↦ T (scalarEquiv U))
    (traceLp_comp_scalarEquiv_symm (Ω := Ω) hp)
  change traceLp p hp (scalarEquiv.symm (scalarEquiv U)) = _ at h
  simpa only [LinearIsometryEquiv.symm_apply_apply] using h

end SobolevSpace.VectorValued.Trace.C1
