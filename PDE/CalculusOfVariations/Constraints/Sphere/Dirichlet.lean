/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Constraints.Sphere.EulerLagrange

/-!
# Sphere-constrained minimizers with prescribed boundary values

For a bounded open domain with C¹ boundary, a sphere-valued minimizer of the
Dirichlet integral satisfies the weak harmonic-map equation. The admissible
class lives in the Sobolev space: `U - g ∈ H¹₀` fixes the
boundary values, and `|U| = 1` holds almost everywhere.

This is Evans, §8.4.3, Theorem 5 (the weak form (33) of `-ΔU = |DU|² U`), for domains in
`ℝ^(n+1)` with C¹ graph boundary and any number `m` of components. Existence of a minimizer is
`exists_sphere_dirichlet_minimizer`. The equation follows from minimality alone, without a
first-variation formula or a differentiable representative among the hypotheses.

## Main results

* `integral_inner_derivatives_eq_of_sphere_minimizer_of_local_graph`: the weak harmonic-map
  equation for every test field in `H¹₀ ∩ L∞`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.4.3, Theorem 5.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.CalculusOfVariations

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open FiniteProductComposition
open scoped ENNReal NNReal Topology InnerProductSpace Sobolev

/-- On a bounded open C¹ domain, every sphere-valued Dirichlet minimizer
with prescribed Sobolev boundary data satisfies the weak harmonic-map
equation for all test fields in `H¹₀ ∩ L∞`. -/
theorem integral_inner_derivatives_eq_of_sphere_minimizer_of_local_graph
    {n m : ℕ} {Ω : Set ℝ^(n + 1)} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hgraph : Boundary.HasC1GraphBoundary Ω)
    (g U : Fin m → H¹(Ω))
    (hunit : ∀ᵐ x ∂domainMeasure (n + 1) Ω, ‖values U x‖ = 1)
    (hboundary : ∀ j,
      U j - g j ∈ (h10SubmoduleOn (n := n + 1) (Ω := Ω)).toSubmodule)
    (hmin : ∀ W : Fin m → H¹(Ω),
      (∀ᵐ x ∂domainMeasure (n + 1) Ω, ‖values W x‖ = 1) →
      (∀ j, W j - g j ∈ (h10SubmoduleOn (n := n + 1) (Ω := Ω)).toSubmodule) →
      vectorDirichletEnergy U ≤ vectorDirichletEnergy W)
    (V : Fin m → H¹₀(Ω))
    (hV : MemLp (values (fun j ↦ (V j : H¹(Ω)))) ∞
      (domainMeasure (n + 1) Ω)) :
    (∫ x, ∑ i : Fin (n + 1),
      ⟪derivatives U i x,
        derivatives (fun j ↦ (V j : H¹(Ω))) i x⟫_ℝ
        ∂domainMeasure (n + 1) Ω) =
      ∫ x, (∑ i : Fin (n + 1), ‖derivatives U i x‖ ^ 2) *
        ⟪values U x, values (fun j ↦ (V j : H¹(Ω))) x⟫_ℝ
        ∂domainMeasure (n + 1) Ω := by
  let := hgraph.c1ExtensionAtlas hΩ hb
  obtain ⟨P⟩ := Approximation.UpToBoundary.exists_inwardPartition hΩ hb
    (Boundary.hasC1Boundary_of_local_graph hgraph)
  obtain ⟨M, hM⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp
    (show eLpNormEssSup
      (values (fun j ↦ (V j : H¹(Ω))))
      (domainMeasure (n + 1) Ω) < ⊤ by
      simpa only [eLpNorm_exponent_top hV.aestronglyMeasurable] using hV.eLpNorm_lt_top)
  apply integral_inner_derivatives_eq_of_sphere_minimizer P
    (Extension.C1.operator (n := n + 1) (p := 2) (Ω := Ω)) U hunit
    (fun W hW hWU ↦ hmin W hW (fun j ↦ ?_)) V
    (M := M) (hM.mono (fun _ hx ↦ hx))
  simpa only [sub_add_sub_cancel] using
    (h10SubmoduleOn (n := n + 1) (Ω := Ω)).toSubmodule.add_mem (hWU j) (hboundary j)

end PDE.CalculusOfVariations
