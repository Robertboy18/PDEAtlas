/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Operator
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Scalar
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.FiniteExponentCompactSupport
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Density

/-!
# Compatibility with the scalar half-space trace

At real codomain the Banach-valued trace is the scalar trace under the
canonical graph isometry. Both operators agree with boundary evaluation on compact
`C¹` representatives, and compact smooth density identifies their completions.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory Set TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.HalfSpace

open GraphSpace

variable {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

variable (n p) in
/-- The canonical isometry between the Banach-valued Sobolev graph at `F := ℝ` and the
real Sobolev graph on the upper half-space. Its coordinates are unchanged. -/
abbrev upperScalarEquiv :
    W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; ℝ)
      ≃ₗᵢ[ℝ] W^{1,ENNReal.ofReal p}(ℝ^(n + 1)₊) :=
  scalarEquiv (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
    (Ω := ⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩)

/-- Real specialization of the Banach trace equals the scalar
trace after the canonical isometric identification of their Sobolev graphs. -/
theorem traceLp_eq_scalar_traceLp (hp : 1 ≤ p)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; ℝ)) :
    traceLp n p hp U = SobolevSpace.Trace.HalfSpace.traceLp n p hp (scalarEquiv U) := by
  let e := scalarEquiv (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
    (Ω := ⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩)
  refine (dense_compact_smooth (n := n) (F := ℝ) (p := ENNReal.ofReal p)
    ENNReal.ofReal_ne_top).induction ?_
    (isClosed_eq (traceLp (F := ℝ) n p hp).continuous
      ((SobolevSpace.Trace.HalfSpace.traceLp n p hp).continuous.comp e.continuous)) U
  rintro V ⟨f, hf, hfc, hbase⟩
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  let φ : SobolevSpace.Trace.HalfSpace.CompactSupport.c1CompactSubmodule n := ⟨f, hf1, hfc⟩
  have hφ : ((SobolevSpace.Trace.HalfSpace.CompactSupport.toUpperW1p p φ).val
      (baseIndex (n + 1) 1) : ℝ^(n + 1) → ℝ) =ᵐ[volume.restrict ℝ^(n + 1)₊] f := by
    simpa only [baseIndex_toList, iteratedPartialDeriv, domainMeasure] using
      SobolevSpace.Trace.HalfSpace.CompactSupport.toUpperW1p_coordinate_ae p φ (baseIndex (n + 1) 1)
  have he : e.symm (SobolevSpace.Trace.HalfSpace.CompactSupport.toUpperW1p p φ) = V := by
    apply WkpSpaceOn.ext_of_base_ae
    exact hφ.trans hbase.symm
  have he' : scalarEquiv V = SobolevSpace.Trace.HalfSpace.CompactSupport.toUpperW1p p φ := by
    rw [← he, LinearIsometryEquiv.apply_symm_apply]
  rw [traceLp_c1 hp V hf1 hfc hbase, he',
    SobolevSpace.Trace.HalfSpace.CompactSupport.traceLp_c1 p hp φ]
  apply Lp.ext
  exact (smoothBoundaryLp_coeFn_ae hf1.continuous hfc).trans
    (SobolevSpace.Trace.HalfSpace.CompactSupport.boundaryLpLinear_apply_ae p φ).symm

/-- The Banach-valued trace of the Banach-valued copy of a real Sobolev function is its
scalar trace. -/
theorem traceLp_upperScalarEquiv_symm (hp : 1 ≤ p) (u : W^{1,ENNReal.ofReal p}(ℝ^(n + 1)₊)) :
    traceLp n p hp ((upperScalarEquiv n p).symm u) =
      SobolevSpace.Trace.HalfSpace.traceLp n p hp u := by
  rw [traceLp_eq_scalar_traceLp, LinearIsometryEquiv.apply_symm_apply]

end SobolevSpace.VectorValued.Trace.HalfSpace
