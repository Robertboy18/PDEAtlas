/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution.Similarity
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Gradient

/-!
# The interior gradient trace of the Green kernel

The fundamental kernel is smooth near the boundary, and the corrector's first
derivatives have their continuous completion. Their difference is the
gradient away from the pole and its limit from the domain at the boundary.
The signed normal derivative in the Green formula uses this trace.
-/

@[expose] public noncomputable section

namespace PotentialTheory.GreenFunction.Domain

open Filter Set SobolevSpace
open scoped Topology Gradient

/-- Subtracting a classical corrector gives the gradient off the pole. -/
theorem gradient_sub_corrector
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} (hopen : IsOpen Ω)
    {φ : ℝ^n → ℝ} (hφ : ContDiffUpToBoundary 1 φ Ω)
    {x z : ℝ^n} (hz : z ∈ Ω) (hzx : z ≠ x) :
    ∇ (fun w ↦ fundamentalSolution n (w - x) - φ w) z =
      ∇ (fun w ↦ fundamentalSolution n (w - x)) z - hφ.completedGradient z := by
  have hk : ContDiffAt ℝ (⊤ : ℕ∞) (fun w ↦ fundamentalSolution n (w - x)) z := by
    simpa only [one_smul] using
      contDiffAt_fundamentalSolution_smul_sub n zero_lt_one x z hzx
  have hp := (hφ.contDiffOn.contDiffAt (hopen.mem_nhds hz)).differentiableAt one_ne_zero
  rw [hφ.completedGradient_eq_gradient hz]
  simp only [gradient, fderiv_fun_sub (hk.differentiableAt (by simp)) hp, map_sub]

/-- The gradient used in the normal boundary integral is the limit of the
Green-kernel gradient from inside the domain. -/
theorem tendsto_gradient_sub_corrector
    {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} (hopen : IsOpen Ω)
    {φ : ℝ^n → ℝ} (hφ : ContDiffUpToBoundary 1 φ Ω)
    {x z : ℝ^n} (hx : x ∈ Ω) (hz : z ∈ frontier Ω) :
    Tendsto (∇ (fun w ↦ fundamentalSolution n (w - x) - φ w)) (𝓝[Ω] z)
      (𝓝 (∇ (fun w ↦ fundamentalSolution n (w - x)) z -
        hφ.completedGradient z)) := by
  have hzx : z ≠ x := by
    rintro rfl
    exact (mem_interior_iff_notMem_frontier hx).mp
      (by simpa only [hopen.interior_eq] using hx) hz
  have hk : ContDiffAt ℝ (⊤ : ℕ∞) (fun w ↦ fundamentalSolution n (w - x)) z := by
    simpa only [one_smul] using
      contDiffAt_fundamentalSolution_smul_sub n zero_lt_one x z hzx
  have hkg : ContinuousAt (∇ (fun w ↦ fundamentalSolution n (w - x))) z :=
    (InnerProductSpace.toDual ℝ (ℝ^n)).symm.continuous.continuousAt.comp
      (hk.continuousAt_fderiv (by simp))
  have ht := (hkg.sub hφ.continuous_completedGradient.continuousAt).tendsto.mono_left
    (nhdsWithin_le_nhds (s := Ω))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    Eventually.filter_mono nhdsWithin_le_nhds (isOpen_ne.mem_nhds hzx)] with w hw hwx
  exact (gradient_sub_corrector hopen hφ hw hwx).symm

end PotentialTheory.GreenFunction.Domain
