/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.FundamentalSolution
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.PointwiseBoundary
public import PDE.Spaces.Sobolev.Variational.Spaces.ZeroBoundaryCoordinates
import PDE.Analysis.Calculus.LocalExtension.Punctured

/-!
# Regularized affine classes for harmonic correctors

Regularizing the fundamental pole inside an interior ball preserves its
boundary values. Trace identification therefore places the difference between
a corrector and this regularization in H¹₀. This allows ordinary weak
energy tests without assigning H¹ regularity to the singular Green kernel.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open scoped Sobolev

namespace PotentialTheory.GreenFunction.Domain

open Filter MeasureTheory Metric Set SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.Boundary SobolevSpace.Approximation.UpToBoundary
open scoped ENNReal Topology

/-- A continuous corrector differs from a smooth regularized pole by a
member of the closure-defined H¹₀ space. -/
theorem exists_regularized_corrector
    {m : ℕ} {Ω : Set ℝ^(m + 1)} [H : C1ExtensionAtlas (m + 1) Ω]
    (P : InwardPartition Ω) (hbounded : Bornology.IsBounded Ω)
    {x : ℝ^(m + 1)} {r : ℝ} (hr : 0 < r) (hball : ball x r ⊆ Ω)
    (U : H¹(Ω)) {φ : ℝ^(m + 1) → ℝ}
    (hφ : ContinuousOn φ (closure Ω))
    (hU : baseRepresentative U =ᵐ[domainMeasure (m + 1) Ω] φ)
    (hb : EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω)) :
    ∃ A : ℝ^(m + 1) → ℝ, ∃ hA : ContDiff ℝ (⊤ : ℕ∞) A,
      ∃ hAc : HasCompactSupport A, ∃ w : H¹₀(Ω),
        (w : H¹(Ω)) = U - mkWkpSpaceOnOfContDiff A hA hAc ∧
        (baseCoordCLM w : ℝ^(m + 1) → ℝ) =ᵐ[domainMeasure (m + 1) Ω]
          (fun z ↦ φ z - A z) ∧
        ∀ z ∈ closure Ω, r ≤ ‖z - x‖ →
          A =ᶠ[𝓝 z] fun y ↦ fundamentalSolution (m + 1) (y - x) := by
  have hkernel : ContDiffOn ℝ (⊤ : ℕ∞) (fundamentalSolution (m + 1)) {0}ᶜ :=
    fun y hy ↦ (contDiffAt_fundamentalSolution (m + 1) y hy).contDiffWithinAt
  obtain ⟨A, hA, hAc, hreg⟩ :=
    hkernel.exists_contDiff_compactSupport_eq_away_pole hbounded x hr
  let G : H¹(Ω) := mkWkpSpaceOnOfContDiff A hA hAc
  have hG : baseRepresentative G =ᵐ[domainMeasure (m + 1) Ω] A := by
    simpa only [baseRepresentative, baseIndex_toList, iteratedPartialDeriv] using
      mkWkpSpaceOnOfContDiff_apply_ae (k := 1) (p := 2) (Ω := Ω)
        A hA hAc (baseIndex (m + 1) 1)
  have heq : EqOn φ A (frontier Ω) := by
    intro y hy
    rw [hb hy]
    symm
    apply (hreg y (frontier_subset_closure hy) ?_).eq_of_nhds
    by_contra! hnear
    have hyΩ : y ∈ Ω := hball (by simpa only [mem_ball, dist_eq_norm] using hnear)
    exact (mem_interior_iff_notMem_frontier hyΩ).mp
      (by simpa only [H.isOpen.interior_eq] using hyΩ) hy
  let w : H¹₀(Ω) :=
    ⟨U - G, Trace.C1.sub_mem_H10_of_eqOn_frontier P U G hφ
      hA.continuous.continuousOn hU hG heq⟩
  refine ⟨A, hA, hAc, w, rfl, ?_, hreg⟩
  filter_upwards [baseRepresentative_sub_ae U G, hU, hG] with z hz huz hgz
  change baseRepresentative (U - G) z = φ z - A z
  simpa only [huz, hgz] using hz

end PotentialTheory.GreenFunction.Domain
