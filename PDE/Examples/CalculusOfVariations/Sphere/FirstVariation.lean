/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Constraints.Sphere.Dirichlet
import CAS.ExactTactic

/-!
# The radial correction in the sphere-constrained energy

For a circle-valued map, a variation can have a radial component even though
the map's spatial derivative is tangent. For the variation in
`circle_normalized_energy_hasDerivAt` the first variation is `3 - 1 = 2`, where `-1`
comes from the constraint term.

For the zero-dimensional sphere `{−1,1}`, tangency forces every weak
derivative to vanish. Such maps have zero Dirichlet energy and are therefore
constrained minimizers, also on disconnected domains where their values differ
between components. The first-variation equation applies to them
(`scalar_sphere_minimizer_weak_equation`).
-/

@[expose] public noncomputable section

namespace PDE.Examples.CalculusOfVariations.Sphere

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open FiniteProductComposition PDE.CalculusOfVariations
open scoped ENNReal NNReal Topology InnerProductSpace Sobolev

/-- The normalized energy along the variation `(1,0) + t(1,1)`, with derivative direction
`(0,1) + t(2,3)`, has derivative `2` at `t = 0`. -/
theorem circle_normalized_energy_hasDerivAt :
    HasDerivAt
      (fun t : ℝ ↦
        ‖fderiv ℝ (NormedSpace.normalize : ℝ^2 → ℝ^2)
          (!₂[1, 0] + t • !₂[1, 1]) (!₂[0, 1] + t • !₂[2, 3])‖ ^ 2 / 2)
      2 0 := by
  have h := NormedSpace.hasDerivAt_normalized_energy
    (u := (!₂[1, 0] : ℝ^2)) (by norm_num [EuclideanSpace.norm_eq])
    (!₂[1, 1] : ℝ^2) (!₂[0, 1] : ℝ^2) (!₂[2, 3] : ℝ^2)
    (by norm_num [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two])
  apply h.congr_deriv
  norm_num [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_two, EuclideanSpace.norm_eq]

/-- Every `H¹` map with values in `{−1,1}` has zero Dirichlet energy, on every domain
with a `C¹` extension atlas. -/
theorem vectorDirichletEnergy_eq_zero_of_scalar_norm_eq_one
    {n : ℕ} {Ω : Set ℝ^(n + 1)} [H : Boundary.C1ExtensionAtlas (n + 1) Ω]
    (E : Extension.GraphSpace.Operator (n + 1) 1 2 Ω)
    (U : Fin 1 → H¹(Ω))
    (hunit : ∀ᵐ x ∂domainMeasure (n + 1) Ω, ‖values U x‖ = 1) :
    vectorDirichletEnergy U = 0 := by
  have hgrad (i : Fin (n + 1)) :
      ∀ᵐ x ∂domainMeasure (n + 1) Ω, derivatives U i x = 0 := by
    filter_upwards [hunit,
      inner_values_derivatives_eq_zero_ae_of_norm_eq_one H.isOpen E
        (by norm_num) U hunit i] with x hx ht
    have hu : values U x 0 ≠ 0 := by
      intro hz
      have hz' : values U x = 0 := by
        ext j
        fin_cases j
        exact hz
      simp [hz'] at hx
    have hp : derivatives U i x 0 * values U x 0 = 0 := by
      simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_one] using ht
    ext j
    fin_cases j
    exact (mul_eq_zero.mp hp).resolve_right hu
  unfold vectorDirichletEnergy
  apply integral_eq_zero_of_ae
  filter_upwards [ae_all_iff.mpr hgrad] with x hx
  simp [hx]

/-- A scalar `H¹` map with values in `{−1,1}` satisfies the weak equation of
sphere-constrained minimizers. -/
theorem scalar_sphere_minimizer_weak_equation
    {n : ℕ} {Ω : Set ℝ^(n + 1)} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hgraph : Boundary.HasC1GraphBoundary Ω)
    (U : Fin 1 → H¹(Ω))
    (hunit : ∀ᵐ x ∂domainMeasure (n + 1) Ω, ‖values U x‖ = 1)
    (V : Fin 1 → H¹₀(Ω))
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
  apply integral_inner_derivatives_eq_of_sphere_minimizer_of_local_graph
    hΩ hb hgraph U U hunit (fun j ↦ by simp) ?_ V hV
  intro W _ _
  rw [vectorDirichletEnergy_eq_zero_of_scalar_norm_eq_one
    (Extension.C1.operator (n := n + 1) (p := 2) (Ω := Ω)) U hunit]
  exact vectorDirichletEnergy_nonneg W

end PDE.Examples.CalculusOfVariations.Sphere
