/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.NormalLimit

/-!
# Dirichlet data in the Green representation

On a bounded open domain with C¹ graph boundary,
`exists_dirichlet_representation_with_normal_derivative_of_local_graph` gives, for each pole `x`, a
harmonic corrector `φ` with boundary values `Φ(y - x)` and an `L²` boundary density `ρ` that is
almost everywhere the one-sided derivative at `s = 0`, from `s ≤ 0`, of `s ↦ G(y + s ν(y))`, where
`G = greenKernel x φ` vanishes on the boundary and `ν` is the outward unit normal. Both are chosen
before the solution: every `u` of class `C²` up to the boundary with `-Δu = f` in `Ω` and `u = g` on
`∂Ω` satisfies `u(x) = -∫ g ρ dS + ∫ G f`, with both integrands integrable. This is Evans's
representation formula (30), §2.2.4(a), Theorem 12, with `ρ` in place of `∂G/∂ν`; Evans assumes that
Green's function exists, while here the corrector comes from
`exists_green_representation_with_normal_derivative_of_local_graph`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(a), the boundary-value problem (29), p. 34, and
  Theorem 12 (Representation formula using Green's function), (30), p. 35.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PotentialTheory.GreenFunction.Domain

open Filter MeasureTheory Set SobolevSpace SobolevSpace.Boundary
open SobolevSpace.Trace.C1 SobolevSpace.Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Sobolev Topology

/-- On a bounded open C¹ graph domain, a single Green kernel represents every
classical Dirichlet solution by its source and boundary data. Its outward
one-sided normal derivative agrees almost everywhere with an L² function,
and both integrands are integrable. -/
theorem exists_dirichlet_representation_with_normal_derivative_of_local_graph
    {m : ℕ} (hn : 2 ≤ m + 1) {Ω : Set ℝ^(m + 1)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω) {x : ℝ^(m + 1)} (hx : x ∈ Ω) :
    letI : C1ExtensionAtlas (m + 1) Ω := hgraph.c1ExtensionAtlas hopen hbounded
    ∃ φ ρ : ℝ^(m + 1) → ℝ,
      LaplacianEquation.IsHarmonicPDE (m + 1) φ Ω ∧
      ContinuousOn φ (closure Ω) ∧
      EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω) ∧
      ContinuousOn (greenKernel x φ) (closure Ω \ {x}) ∧
      EqOn (greenKernel x φ) 0 (frontier Ω) ∧
      MemLp ρ 2 (surfaceMeasure Ω) ∧
      (∀ᵐ y ∂surfaceMeasure Ω, ∀ hy : y ∈ frontier Ω,
        HasDerivWithinAt
          (fun s : ℝ ↦ greenKernel x φ (y + s • outwardUnitNormal ⟨y, hy⟩))
          (ρ y) (Iic 0) 0) ∧
      ∀ (u f g : ℝ^(m + 1) → ℝ) (hu : ContDiffUpToBoundary 2 u Ω),
        ContinuousOn u (closure Ω) →
        EqOn (fun y ↦ -PDE.laplacian u y) f Ω →
        EqOn u g (frontier Ω) →
        Integrable (fun y ↦ g y * ρ y) (surfaceMeasure Ω) ∧
        IntegrableOn (fun y ↦ greenKernel x φ y * f y) Ω ∧
        u x = -(∫ y, g y * ρ y ∂surfaceMeasure Ω) +
          ∫ y in Ω, greenKernel x φ y * f y := by
  let : C1ExtensionAtlas (m + 1) Ω := hgraph.c1ExtensionAtlas hopen hbounded
  obtain ⟨φ, q, hh, hc, hb, hcG, hzero, hformula, hnormal⟩ :=
    exists_green_representation_with_normal_derivative_of_local_graph
      hn hopen hbounded hgraph hx
  refine ⟨φ, fun y ↦ -q y, hh, hc, hb, hcG, hzero, (Lp.memLp q).neg, ?_, ?_⟩
  · filter_upwards [hnormal] with y hy
    intro hyfront
    exact (hy hyfront).2
  · intro u f g hu hcu hf hg
    obtain ⟨hboundary, hvolume, heq⟩ := hformula u hu hcu
    have hv : (fun y ↦ greenKernel x φ y * PDE.laplacian u y) =ᵐ[volume.restrict Ω]
        fun y ↦ -(greenKernel x φ y * f y) := by
      filter_upwards [ae_restrict_mem hopen.measurableSet] with y hy
      rw [← hf hy]
      simp only [mul_neg, neg_neg]
    have hbg : (fun y ↦ q y * u y) =ᵐ[surfaceMeasure Ω]
        fun y ↦ -(g y * (-q y)) := by
      filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with y hy
      rw [hg hy]
      simp only [mul_neg, neg_neg, mul_comm]
    refine ⟨integrable_fun_neg_iff.mp (hboundary.congr hbg),
      integrable_fun_neg_iff.mp (hvolume.congr hv), ?_⟩
    rw [integral_congr_ae hbg, integral_congr_ae hv, integral_neg, integral_neg,
      sub_neg_eq_add] at heq
    exact heq

end PotentialTheory.GreenFunction.Domain
