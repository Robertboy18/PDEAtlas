/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Symmetry

/-!
# The classical Green formulas from domain geometry

On a bounded open domain with C¹ graph boundary we prove Evans's representation formula using
Green's function and the symmetry of Green's function, §2.2.4(a), Theorems 12 and 13, in every
dimension `n ≥ 2`. The extension atlas and its outward normal are built from the graph boundary
(`SobolevSpace.Boundary.HasC1GraphBoundary.c1ExtensionAtlas`), so no atlas or Green formula is
assumed. The harmonic corrector of Evans's problem (26) remains a hypothesis, with classical
regularity up to the boundary; correctors are constructed in `Domain.Corrector`.

## Main results

* `dirichlet_representation`: if `u` is `C²` up to the boundary, `-Δu = f` in `Ω` and `u = g` on
  `∂Ω`, then `u(x) = -∫ g ∂G/∂ν dS + ∫ f G`, with both integrands integrable; this is Evans's (30).
* `symmetry_of_raw_graph`: `G(x, y) = G(y, x)` for all `x, y ∈ Ω`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(a), the standing assumptions on `U`, p. 33, the
  corrector problem (26), p. 34, and Theorem 12 (Representation formula using Green's function),
  (30), and Theorem 13 (Symmetry of Green's function), p. 35.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian)

namespace PotentialTheory.GreenFunction.Domain

open Filter Set MeasureTheory SobolevSpace SobolevSpace.Boundary
open SobolevSpace.Trace.C1 Geometry.SurfaceMeasure

/-- The general-domain Dirichlet Green formula in every dimension at least two.
The source and boundary data are substituted using the PDE and boundary
values; integrability and the signed representation are derived. -/
theorem dirichlet_representation
    {m : ℕ} (hn : 2 ≤ m + 1) {Ω : Set (ℝ^(m + 1))}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω) {u φ f g : ℝ^(m + 1) → ℝ}
    (hu : ContDiffUpToBoundary 2 u Ω) (hcu : ContinuousOn u (closure Ω))
    {x : ℝ^(m + 1)} (hx : x ∈ Ω)
    (hφ : ContDiffUpToBoundary 2 φ Ω) (hcφ : ContinuousOn φ (closure Ω))
    (hhar : ∀ y ∈ Ω, laplacian φ y = 0)
    (hcorrector : EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω))
    (hpde : ∀ y ∈ Ω, -laplacian u y = f y)
    (hboundary : EqOn u g (frontier Ω)) :
    letI atlas := hgraph.c1ExtensionAtlas hopen hbounded
    IntegrableOn (fun y ↦ f y * greenKernel x φ y) Ω ∧
      Integrable (fun y ↦ g y * normalFlux (Ω := Ω)
        (greenKernelGradient x (hφ.of_le (show 1 ≤ 2 by omega))) y) (surfaceMeasure Ω) ∧
      u x = -(∫ y, g y * normalFlux (Ω := Ω)
        (greenKernelGradient x (hφ.of_le (show 1 ≤ 2 by omega))) y ∂surfaceMeasure Ω) +
        ∫ y in Ω, f y * greenKernel x φ y := by
  let := hgraph.c1ExtensionAtlas hopen hbounded
  let G := greenKernel x φ
  let DG := greenKernelGradient x (hφ.of_le (show 1 ≤ 2 by omega))
  obtain ⟨hi, hb, he⟩ :=
    representation_of_corrector hn hgraph hu hcu hx hφ hcφ hhar hcorrector
  have hv : (fun y ↦ G y * laplacian u y) =ᵐ[volume.restrict Ω]
      fun y ↦ -(f y * G y) := by
    filter_upwards [ae_restrict_mem hopen.measurableSet] with y hy
    rw [← hpde y hy]
    ring
  have hbg : (fun y ↦ u y * normalFlux (Ω := Ω) DG y) =ᵐ[surfaceMeasure Ω]
      fun y ↦ g y * normalFlux (Ω := Ω) DG y := by
    filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with y hy
    rw [hboundary hy]
  refine ⟨integrable_fun_neg_iff.mp (hi.congr hv), hb.congr hbg, ?_⟩
  rw [integral_congr_ae hv, integral_neg, integral_congr_ae hbg, sub_neg_eq_add] at he
  exact he

/-- Bounded open C¹ graph geometry and two classical correctors suffice for
symmetry. No atlas, Green formula, or boundary limit is assumed. -/
theorem symmetry_of_raw_graph
    {n : ℕ} (hn : 2 ≤ n) {Ω : Set (ℝ^n)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω)
    {x y : ℝ^n} (hx : x ∈ Ω) (hy : y ∈ Ω)
    {φx φy : ℝ^n → ℝ}
    (hφx : ContDiffUpToBoundary 2 φx Ω) (hcx : ContinuousOn φx (closure Ω))
    (hφy : ContDiffUpToBoundary 2 φy Ω) (hcy : ContinuousOn φy (closure Ω))
    (hhx : ∀ z ∈ Ω, laplacian φx z = 0)
    (hhy : ∀ z ∈ Ω, laplacian φy z = 0)
    (hbx : EqOn φx (fun z ↦ fundamentalSolution n (z - x)) (frontier Ω))
    (hby : EqOn φy (fun z ↦ fundamentalSolution n (z - y)) (frontier Ω)) :
    fundamentalSolution n (y - x) - φx y =
      fundamentalSolution n (x - y) - φy x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let := hgraph.c1ExtensionAtlas hopen hbounded
  exact symmetry_of_correctors hn hgraph hx hy hφx hcx hφy hcy hhx hhy hbx hby

end PotentialTheory.GreenFunction.Domain
