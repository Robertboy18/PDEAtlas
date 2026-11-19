/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.BoundaryUniqueness
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.Existence
public import PDE.Elliptic.PotentialTheory.GreenFunction.Domain.Corrector.WeakReciprocity

/-!
# Constructed reciprocal Green kernels on C¹ domains

On a bounded open domain with C¹ graph boundary,
`exists_reciprocal_harmonic_correctors_of_local_graph` constructs a family of correctors `φ x`,
indexed by the points `x` of the domain, and proves the symmetry `G(x, y) = G(y, x)` of the
resulting Green kernel, Evans's §2.2.4(a), Theorem 13. Each corrector has an `H¹` representative, is
harmonic in the domain and takes the values `Φ(· - x)` continuously on the boundary. The symmetry
comes from weak Dirichlet pairings (`green_eq_swap_of_native_correctors`), so no hypothesis on
boundary gradients enters. By uniqueness on the closure, `green_eq_swap_of_classical_correctors`
gives the same symmetry for any harmonic correctors that are continuous on the closure with these
boundary values.

Indexing the family by the points of the domain keeps the statement meaningful for the empty domain,
and connectedness is not needed.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.4(a), the corrector problem (26) and the definition of
  Green's function for the region `U`, p. 34, and Theorem 13 (Symmetry of Green's function), p. 35.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace PotentialTheory.GreenFunction.Domain

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Boundary
open scoped ENNReal InnerProductSpace

/-- Bounded open C¹ graph geometry in dimension at least two gives a
family of harmonic correctors and a reciprocal Green kernel. -/
theorem exists_reciprocal_harmonic_correctors_of_local_graph
    {m : ℕ} {Ω : Set ℝ^(m + 1)} (hn : 2 ≤ m + 1)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω) :
    ∃ U : Ω → H¹(Ω), ∃ φ : Ω → ℝ^(m + 1) → ℝ,
      (∀ x : Ω,
        baseRepresentative (U x) =ᵐ[domainMeasure (m + 1) Ω] φ x ∧
        LaplacianEquation.IsHarmonicPDE (m + 1) (φ x) Ω ∧
        ContinuousOn (φ x) (closure Ω) ∧
        EqOn (φ x) (fun y ↦ fundamentalSolution (m + 1) (y - x)) (frontier Ω) ∧
        ∀ t : H¹₀(Ω),
          (∑ i, ⟪wkpCoordinateCLM (singleDerivIndex (m + 1) i) (U x),
            derivCoordCLM i t⟫_ℝ) = 0) ∧
      ∀ x y : Ω,
        fundamentalSolution (m + 1) (y - x) - φ x y =
          fundamentalSolution (m + 1) (x - y) - φ y x := by
  classical
  choose U φ hU hφ hc hb hw using fun x : Ω ↦
    exists_harmonic_corrector_of_local_graph hn hopen hbounded hgraph x.property
  refine ⟨U, φ, fun x ↦ ⟨hU x, hφ x, hc x, hb x, hw x⟩, ?_⟩
  intro x y
  by_cases hxy : x = y
  · subst y
    rfl
  · exact green_eq_swap_of_native_correctors hn hopen hbounded hgraph
      x.property y.property (fun h ↦ hxy (Subtype.ext h))
      (U x) (U y) (hU x) (hU y) (hφ x) (hφ y) (hc x) (hc y)
      (hb x) (hb y) (hw x) (hw y)

/-- Classical harmonic correctors with the fundamental boundary values give a
symmetric Green kernel on a bounded open C¹ domain. Closure uniqueness identifies
them with the constructed weak correctors, so no Sobolev representation or
classical boundary gradient is needed as an input. -/
theorem green_eq_swap_of_classical_correctors
    {m : ℕ} {Ω : Set ℝ^(m + 1)} (hn : 2 ≤ m + 1)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : HasC1GraphBoundary Ω)
    {x y : ℝ^(m + 1)} (hx : x ∈ Ω) (hy : y ∈ Ω)
    {φx φy : ℝ^(m + 1) → ℝ}
    (hφx : LaplacianEquation.IsHarmonicPDE (m + 1) φx Ω)
    (hφy : LaplacianEquation.IsHarmonicPDE (m + 1) φy Ω)
    (hcx : ContinuousOn φx (closure Ω)) (hcy : ContinuousOn φy (closure Ω))
    (hbx : EqOn φx (fun z ↦ fundamentalSolution (m + 1) (z - x)) (frontier Ω))
    (hby : EqOn φy (fun z ↦ fundamentalSolution (m + 1) (z - y)) (frontier Ω)) :
    fundamentalSolution (m + 1) (y - x) - φx y =
      fundamentalSolution (m + 1) (x - y) - φy x := by
  obtain ⟨_, φ, hφ, hsym⟩ :=
    exists_reciprocal_harmonic_correctors_of_local_graph hn hopen hbounded hgraph
  let xΩ : Ω := ⟨x, hx⟩
  let yΩ : Ω := ⟨y, hy⟩
  have hex := hφx.eqOn_closure_of_boundary_eq (hφ xΩ).2.1
    hopen hbounded hcx (hφ xΩ).2.2.1
    (fun z hz ↦ (hbx hz).trans ((hφ xΩ).2.2.2.1 hz).symm)
  have hey := hφy.eqOn_closure_of_boundary_eq (hφ yΩ).2.1
    hopen hbounded hcy (hφ yΩ).2.2.1
    (fun z hz ↦ (hby hz).trans ((hφ yΩ).2.2.2.1 hz).symm)
  rw [hex (subset_closure hy), hey (subset_closure hx)]
  exact hsym xΩ yΩ

end PotentialTheory.GreenFunction.Domain
