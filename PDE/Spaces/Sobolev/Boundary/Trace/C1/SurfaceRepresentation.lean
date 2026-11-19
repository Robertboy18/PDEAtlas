/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.InnerProductSpace.FactorThrough
public import PDE.Spaces.Sobolev.Approximation.Density.UpToBoundary
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.TraceSpace

/-!
# Surface densities of bounded trace functionals

A bound in the surface L² norm turns a functional on the intrinsic trace
space into integration against an L² boundary function. The construction
uses Hahn–Banach and Riesz representation through a general linear
factorization lemma.

The estimate in the surface norm is a hypothesis here. Continuity in the
stronger intrinsic trace norm alone does not supply that estimate.
It is enough to prove the estimate on ambient smooth test functions:
their restrictions are dense in H¹ on a bounded C¹ domain.
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open MeasureTheory Set TopologicalSpace GraphSpace Boundary.Geometry.SurfaceMeasure
open scoped Distributions Sobolev

variable {m : ℕ} {Ω : Set ℝ^(m + 1)}
  [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- A trace functional bounded in the physical surface L² norm is integration
against a surface L² density with the same norm bound. -/
theorem exists_surfaceDensity_of_norm_le
    (N : HilbertTraceSpace (Ω := Ω) →L[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z, ‖N z‖ ≤ C * ‖boundaryValue z‖) :
    ∃ q : BoundaryL2 (Ω := Ω), ‖q‖ ≤ C ∧
      ∀ z, N z = ∫ y, q y * (boundaryValue z) y ∂surfaceMeasure Ω := by
  obtain ⟨q, hq, hpair⟩ :=
    LinearMap.exists_norm_le_inner_apply_eq_of_bound
      boundaryValue.toLinearMap N.toLinearMap hC hbound
  refine ⟨q, hq, ?_⟩
  intro z
  calc
    N z = inner ℝ q (boundaryValue z) := (hpair z).symm
    _ = ∫ y, q y * (boundaryValue z) y ∂surfaceMeasure Ω := by
      rw [L2.inner_def]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y ↦ by
        simp only [RCLike.inner_apply, conj_trivial, mul_comm]

/-- A surface norm bound on ambient smooth test traces extends to every trace
class. Both sides are continuous in H¹, so Sobolev density preserves the bound. -/
theorem norm_le_of_smoothTestFunction_bound
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (N : HilbertTraceSpace (Ω := Ω) →L[ℝ] ℝ) {C : ℝ}
    (hbound : ∀ φ : 𝓓((⊤ : Opens ℝ^(m + 1)), ℝ),
      ‖N (traceClass (globalTestFunctionToWkpOn φ))‖ ≤
        C * ‖trace (Ω := Ω) (globalTestFunctionToWkpOn φ)‖)
    (z : HilbertTraceSpace (Ω := Ω)) :
    ‖N z‖ ≤ C * ‖boundaryValue z‖ := by
  obtain ⟨v, rfl⟩ := (trace (Ω := Ω)).ker.mkQ_surjective z
  change ‖N (traceClass v)‖ ≤ C * ‖trace v‖
  have hdense := Approximation.UpToBoundary.denseRange_globalTestFunctionToWkpOn
    (k := 1) (p := 2) hΩ.isOpen hΩ.bounded
    (Boundary.hasC1Boundary_of_local_graph hgraph) (by norm_num)
  exact hdense.induction_on v
    (isClosed_le (N.continuous.comp traceClass.continuous).norm
      (continuous_const.mul trace.continuous.norm)) hbound

/-- A surface estimate proved only for smooth test traces already supplies an
L² density for the whole boundary functional. -/
theorem exists_surfaceDensity_of_smoothTestFunction_bound
    (hgraph : Boundary.HasC1GraphBoundary Ω)
    (N : HilbertTraceSpace (Ω := Ω) →L[ℝ] ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ φ : 𝓓((⊤ : Opens ℝ^(m + 1)), ℝ),
      ‖N (traceClass (globalTestFunctionToWkpOn φ))‖ ≤
        C * ‖trace (Ω := Ω) (globalTestFunctionToWkpOn φ)‖) :
    ∃ q : BoundaryL2 (Ω := Ω), ‖q‖ ≤ C ∧
      ∀ z, N z = ∫ y, q y * (boundaryValue z) y ∂surfaceMeasure Ω :=
  exists_surfaceDensity_of_norm_le N hC
    (norm_le_of_smoothTestFunction_bound hgraph N hbound)

end SobolevSpace.Trace.C1
