/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Operator
public import PDE.Spaces.Sobolev.GraphSpace.VectorValued.Operators
import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Density

/-!
# Naturality of the Banach-valued half-space trace

Continuous linear maps of the codomain commute with the Sobolev trace.
The identity follows from literal boundary evaluation on compact smooth representatives
and continuity of the two operators on the full graph.
-/

@[expose] public noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.HalfSpace

open GraphSpace SobolevSpace.Trace.HalfSpace

variable {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Applying a continuous linear map to a Sobolev function commutes with taking
its trace, without finite-dimensionality assumptions on either Banach space. -/
theorem traceLp_mapCLM (hp : 1 ≤ p) (L : F →L[ℝ] G)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)) :
    traceLp n p hp (mapCLM L U) = L.compLpL (ENNReal.ofReal p) volume (traceLp n p hp U) := by
  refine (dense_compact_smooth ENNReal.ofReal_ne_top).induction ?_
    (isClosed_eq ((traceLp n p hp).continuous.comp (mapCLM L).continuous)
      ((L.compLpL (ENNReal.ofReal p) volume).continuous.comp (traceLp n p hp).continuous)) U
  rintro V ⟨f, hf, hfc, hbase⟩
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by simp)
  have hLf : ContDiff ℝ 1 (L ∘ f) := L.contDiff.comp hf1
  have hLc : HasCompactSupport (L ∘ f) := hfc.comp_left L.map_zero
  have hLbase := (mapCLM_apply_ae L V (baseIndex (n + 1) 1)).trans (hbase.fun_comp L)
  rw [traceLp_c1 hp (mapCLM L V) hLf hLc hLbase, traceLp_c1 hp V hf1 hfc hbase]
  apply Lp.ext
  exact (smoothBoundaryLp_coeFn_ae hLf.continuous hLc).trans
    (((smoothBoundaryLp_coeFn_ae hf1.continuous hfc).fun_comp L).symm.trans
      (L.coeFn_compLpL _).symm)

end SobolevSpace.VectorValued.Trace.HalfSpace
