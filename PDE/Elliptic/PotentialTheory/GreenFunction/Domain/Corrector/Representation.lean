/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.ClassicalBoundary
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Dirichlet

/-!
# Green representation with a constructed corrector

On a bounded open domain in `ℝⁿ` with `Cⁿ⁺³` graph boundary,
`exists_corrector_dirichlet_representation_of_higher_graph` constructs the harmonic corrector with
boundary values `Φ(y - x)` and `C²` regularity up to the boundary
(`exists_classical_harmonic_corrector_of_higher_graph`) and substitutes it into
`dirichlet_representation`. Every `u` of class `C²` up to the boundary with `-Δu = f` in the domain
and `u = g` on the boundary then satisfies `u(x) = -∫ g ∂G/∂ν dS + ∫ f G`, with both integrands
integrable. This is Evans's §2.2.4(a), Theorem 12, with Green's function constructed rather than
assumed.

The boundary order `n + 3` is a sufficient condition for the `C²` regularity of the corrector up to
the boundary; on C¹ domains `Corrector.Reciprocity` constructs correctors that are continuous on the
closure and proves reciprocity weakly.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(a), the corrector problem (26), p. 34, and Theorem 12
  (Representation formula using Green's function), (30), p. 35.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian)

namespace PotentialTheory.GreenFunction.Domain

open Set MeasureTheory SobolevSpace SobolevSpace.Boundary
open SobolevSpace.Trace.C1 Geometry.SurfaceMeasure

/-- A Green formula whose harmonic corrector and classical boundary jets are
constructed from Cⁿ⁺³ graph geometry. Both integrability clauses are derived. -/
theorem exists_corrector_dirichlet_representation_of_higher_graph
    {m : ℕ} (hn : 2 ≤ m + 1) {Ω : Set ℝ^(m + 1)}
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasContDiffGraphBoundary (m + 1 + 3) Ω)
    {u f g : ℝ^(m + 1) → ℝ}
    (hu : ContDiffUpToBoundary 2 u Ω) (hcu : ContinuousOn u (closure Ω))
    {x : ℝ^(m + 1)} (hx : x ∈ Ω)
    (hpde : ∀ y ∈ Ω, -laplacian u y = f y)
    (hboundary : EqOn u g (frontier Ω)) :
    ∃ φ : ℝ^(m + 1) → ℝ, ∃ hφ : ContDiffUpToBoundary 2 φ Ω,
      ContinuousOn φ (closure Ω) ∧
      LaplacianEquation.IsHarmonicPDE (m + 1) φ Ω ∧
      EqOn φ (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω) ∧
      letI atlas := (hgraph.hasC1GraphBoundary
        (by exact_mod_cast (by omega : 1 ≤ m + 1 + 3))).c1ExtensionAtlas hopen hbounded
      IntegrableOn (fun y ↦ f y * greenKernel x φ y) Ω ∧
        Integrable (fun y ↦ g y * normalFlux (Ω := Ω)
          (greenKernelGradient x (hφ.of_le (show 1 ≤ 2 by omega))) y) (surfaceMeasure Ω) ∧
        u x = -(∫ y, g y * normalFlux (Ω := Ω)
          (greenKernelGradient x (hφ.of_le (show 1 ≤ 2 by omega))) y ∂surfaceMeasure Ω) +
          ∫ y in Ω, f y * greenKernel x φ y := by
  obtain ⟨φ, hφ, hcφ, hh, hb⟩ :=
    exists_classical_harmonic_corrector_of_higher_graph hn hopen hbounded hgraph hx
  exact ⟨φ, hφ, hcφ, hh, hb, dirichlet_representation hn hopen hbounded
    (hgraph.hasC1GraphBoundary (by exact_mod_cast (by omega : 1 ≤ m + 1 + 3)))
    hu hcu hx hφ hcφ hh.2 hb hpde hboundary⟩

end PotentialTheory.GreenFunction.Domain
