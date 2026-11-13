/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.LocalExtension.Zero
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.Regularization
import PDE.Elliptic.PotentialTheory.FundamentalSolution.Similarity
import PDE.FDeriv.Laplacian.Congruence

/-!
# The interior source of a regularized Green pole

The smooth lifting agrees locally with the fundamental solution at each boundary
point. Its Laplacian therefore vanishes in a boundary neighbourhood. Extending
its negative Laplacian by zero gives a smooth source whose closed support
stays inside the domain. In the bounded-domain application this support is compact.
This retains the source needed to represent the corrector by volume and boundary
potentials.
-/

@[expose] public noncomputable section

namespace PotentialTheory.GreenFunction.Domain

open Filter Function MeasureTheory Metric Set
open PDE (laplacian)
open scoped Topology

/-- The negative Laplacian of a regularized pole, extended by zero, has closed support
inside the domain. Agreement with the fundamental solution is required only near
the boundary; no global support property of the lifting is needed. -/
theorem tsupport_indicator_neg_laplacian_subset
    {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n} (hΩ : IsOpen Ω)
    {x : ℝ^n} (hx : x ∈ Ω)
    {A : ℝ^n → ℝ}
    (hreg : ∀ z ∈ frontier Ω,
      A =ᶠ[𝓝 z] fun y ↦ fundamentalSolution n (y - x)) :
    tsupport (Ω.indicator (fun y ↦ -laplacian A y)) ⊆ Ω := by
  classical
  intro z hz
  by_contra hzΩ
  apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hz
  by_cases hzc : z ∈ closure Ω
  · have hzf : z ∈ frontier Ω := by
      simpa only [hΩ.frontier_eq, Set.mem_sdiff] using And.intro hzc hzΩ
    have hzx : z ≠ x := by
      intro he
      exact hzΩ (he.symm ▸ hx)
    have hlap : (fun y ↦ laplacian A y) =ᶠ[𝓝 z] fun _ ↦ 0 := by
      filter_upwards [(hreg z hzf).eventually_nhds,
        isClosed_singleton.isOpen_compl.mem_nhds hzx] with y hAy hy
      rw [EuclideanLaplacian.laplacian_congr_nhds hAy]
      simpa only [one_smul] using
        laplacian_fundamentalSolution_smul_sub_eq_zero n zero_lt_one x y hy
    filter_upwards [hlap] with y hy
    by_cases hyΩ : y ∈ Ω
    · rw [indicator_of_mem hyΩ, hy, neg_zero, Pi.zero_apply]
    · exact indicator_of_notMem hyΩ _
  · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hzc] with y hy
    exact indicator_of_notMem (fun hyΩ ↦ hy (subset_closure hyΩ)) _

/-- The source of a regularized Green pole is smooth across the boundary. It is the
explicit zero extension of `-ΔA`, so later potential formulas use the source of the
original corrector. -/
theorem contDiff_indicator_neg_laplacian
    {n : ℕ} [Fact (0 < n)] {Ω : Set ℝ^n} (hΩ : IsOpen Ω)
    {x : ℝ^n} (hx : x ∈ Ω) {A : ℝ^n → ℝ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hreg : ∀ z ∈ frontier Ω,
      A =ᶠ[𝓝 z] fun y ↦ fundamentalSolution n (y - x)) :
    ContDiff ℝ (⊤ : ℕ∞) (Ω.indicator (fun y ↦ -laplacian A y)) := by
  have hs := tsupport_indicator_neg_laplacian_subset hΩ hx hreg
  have hlap : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ -laplacian A y) := by
    apply ContDiff.neg
    unfold laplacian
    exact ContDiff.sum fun i _ ↦ (hA.partialDeriv i).partialDeriv i
  exact hlap.contDiffOn.indicator_of_tsupport_subset hΩ hs

end PotentialTheory.GreenFunction.Domain
