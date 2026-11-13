/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Atlas.Construction
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Fractional.Classical
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.SurfaceRepresentation

/-!
# Surface norm bounds assembled over a finite boundary cover

The smooth partition constructed from a finite boundary cover has values in `[0,1]`.
Its boundary pieces reconstruct every smooth trace, and multiplication by a partition
piece contracts the surface L² norm. Thus bounds on tests supported in the individual
partition supports give a bound on the whole intrinsic trace space.

The finite cover need not be the operational atlas defining the trace: agreement
with classical boundary values identifies the two constructions.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open Set MeasureTheory TopologicalSpace
open scoped Distributions Sobolev

namespace SobolevSpace.Boundary.FiniteBoundaryCover

variable {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n}

/-- The constructed boundary partition takes values between zero and one. -/
theorem boundaryCutoff_mem_Icc (cover : FiniteBoundaryCover n Ω)
    (i : Fin cover.N) (x : ℝ^n) :
    cover.boundaryCutoff i x ∈ Icc (0 : ℝ) 1 :=
  ⟨(smoothPartition cover).nonneg i.castSucc x,
    (smoothPartition cover).le_one i.castSucc x⟩

/-- The interior partition vanishes on the frontier, leaving the boundary sum equal to one. -/
theorem sum_boundaryCutoff_eq_one_on_frontier (cover : FiniteBoundaryCover n Ω)
    {x : ℝ^n} (hx : x ∈ frontier Ω) :
    ∑ i, cover.boundaryCutoff i x = 1 := by
  have hsum := (smoothPartition cover).sum_eq_one (frontier_subset_closure hx)
  rw [finsum_eq_sum_of_fintype, Fin.sum_univ_castSucc] at hsum
  have hzero : cover.interiorCutoff x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact (cover.isOpen.frontier_eq ▸ hx).2 (cover.interiorCutoff_support h)
  change (∑ i, cover.boundaryCutoff i x) + cover.interiorCutoff x = 1 at hsum
  simpa only [hzero, add_zero] using hsum

end SobolevSpace.Boundary.FiniteBoundaryCover

namespace SobolevSpace.Trace.C1

open GraphSpace Boundary.Geometry.SurfaceMeasure

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
  [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The canonical Sobolev realization of an ambient test has its literal boundary values. -/
theorem trace_globalTestFunctionToWkpOn_apply_ae
    (φ : 𝓓((⊤ : Opens ℝ^(m + 1)), ℝ)) :
    (trace (Ω := Ω) (globalTestFunctionToWkpOn φ) : ℝ^(m + 1) → ℝ) =ᵐ[surfaceMeasure Ω]
      φ := by
  apply Fractional.trace_apply_ae_of_contDiff _ (φ.contDiff.of_le (by simp))
  simpa only [baseRepresentative, baseIndex_toList, iteratedPartialDeriv,
    TestFunction.toFun_eq_coe] using
    globalTestFunctionToWkpOn_coordinate_ae (Ω := Ω) (k := 1) (p := 2)
      φ (baseIndex (m + 1) 1)

/-- Multiplication by a constructed boundary partition piece contracts the surface L² norm. -/
theorem norm_trace_mul_boundaryCutoff_le
    (cover : Boundary.FiniteBoundaryCover (m + 1) Ω) (i : Fin cover.N)
    (φ : 𝓓((⊤ : Opens ℝ^(m + 1)), ℝ)) :
    ‖trace (Ω := Ω) (globalTestFunctionToWkpOn (TestFunction.mul
      (cover.boundaryCutoff i) φ))‖ ≤ ‖trace (Ω := Ω) (globalTestFunctionToWkpOn φ)‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [trace_globalTestFunctionToWkpOn_apply_ae (Ω := Ω)
      (TestFunction.mul (cover.boundaryCutoff i) φ),
    trace_globalTestFunctionToWkpOn_apply_ae (Ω := Ω) φ] with x hmul hφ
  rw [hmul, hφ, TestFunction.mul_apply, norm_mul]
  have hψ := cover.boundaryCutoff_mem_Icc i x
  rw [Real.norm_eq_abs, abs_of_nonneg hψ.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hψ.2

/-- Boundary partition pieces reconstruct the class of an ambient smooth test. -/
theorem traceClass_eq_sum_boundaryCutoff
    (cover : Boundary.FiniteBoundaryCover (m + 1) Ω)
    (φ : 𝓓((⊤ : Opens ℝ^(m + 1)), ℝ)) :
    traceClass (Ω := Ω) (globalTestFunctionToWkpOn φ) =
      ∑ i, traceClass (Ω := Ω) (globalTestFunctionToWkpOn
        (TestFunction.mul (cover.boundaryCutoff i) φ)) := by
  classical
  rw [← map_sum]
  change Submodule.Quotient.mk _ = (Submodule.Quotient.mk _ : HilbertTraceSpace (Ω := Ω))
  rw [Submodule.Quotient.eq]
  change trace _ = 0
  rw [map_sub, sub_eq_zero, map_sum]
  apply Lp.ext
  filter_upwards [trace_globalTestFunctionToWkpOn_apply_ae (Ω := Ω) φ,
    ae_all_iff.mpr (fun i ↦ trace_globalTestFunctionToWkpOn_apply_ae (Ω := Ω)
      (TestFunction.mul (cover.boundaryCutoff i) φ)),
    Lp.coeFn_finsetSum Finset.univ (fun i ↦ trace (Ω := Ω)
      (globalTestFunctionToWkpOn (TestFunction.mul (cover.boundaryCutoff i) φ))),
    ae_restrict_mem isClosed_frontier.measurableSet] with x hφ hlocal hsum hx
  rw [hφ, hsum]
  simp_rw [Finset.sum_apply, hlocal, TestFunction.mul_apply]
  rw [← Finset.sum_mul, cover.sum_boundaryCutoff_eq_one_on_frontier hx, one_mul]

/-- Bounds on smooth tests in the fixed partition supports give a bound on every trace class.
The sum of the local constants is independent of the test and of its Sobolev lifting. -/
theorem norm_le_of_finiteBoundaryCover_bound
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (cover : Boundary.FiniteBoundaryCover (m + 1) Ω)
    (N : HilbertTraceSpace (Ω := Ω) →L[ℝ] ℝ)
    (C : Fin cover.N → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hbound : ∀ i, ∀ φ : 𝓓((⊤ : Opens ℝ^(m + 1)), ℝ),
      tsupport φ ⊆ tsupport (cover.boundaryCutoff i) →
      ‖N (traceClass (globalTestFunctionToWkpOn φ))‖ ≤
        C i * ‖trace (Ω := Ω) (globalTestFunctionToWkpOn φ)‖)
    (q : HilbertTraceSpace (Ω := Ω)) :
    ‖N q‖ ≤ (∑ i, C i) * ‖boundaryValue q‖ := by
  apply norm_le_of_smoothTestFunction_bound hgraph N _ q
  intro φ
  rw [traceClass_eq_sum_boundaryCutoff cover φ, map_sum]
  calc
    ‖∑ i, N (traceClass (globalTestFunctionToWkpOn
        (TestFunction.mul (cover.boundaryCutoff i) φ)))‖ ≤
        ∑ i, ‖N (traceClass (globalTestFunctionToWkpOn
          (TestFunction.mul (cover.boundaryCutoff i) φ)))‖ := norm_sum_le _ _
    _ ≤ ∑ i, C i * ‖trace (Ω := Ω) (globalTestFunctionToWkpOn φ)‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (hbound i _ (by
        change tsupport (fun x ↦ cover.boundaryCutoff i x * φ x) ⊆ _
        exact tsupport_mul_subset_left)).trans
          (mul_le_mul_of_nonneg_left (norm_trace_mul_boundaryCutoff_le cover i φ) (hC i))
    _ = (∑ i, C i) * ‖trace (Ω := Ω) (globalTestFunctionToWkpOn φ)‖ :=
      (Finset.sum_mul ..).symm

end SobolevSpace.Trace.C1
