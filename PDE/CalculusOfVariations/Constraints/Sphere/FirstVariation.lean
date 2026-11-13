/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Constraints.Sphere.Variation
public import PDE.CalculusOfVariations.DirichletEnergy.FiniteProduct
public import PDE.Analysis.InnerProductSpace.Calculus.Normalization.Integral

/-!
# First variation of the sphere-constrained Dirichlet energy

The weak derivatives of a sphere-valued map are tangent to the sphere.
Differentiating the normalized variation therefore gives the usual gradient
pairing minus the radial correction `|DU|² (U · V)`.

The integral differentiation theorem supplies an integrable bound from the
`L²` weak derivatives and the `L∞` bound on the variation. The variation is
the Sobolev composition itself, and its energy is the Dirichlet integral.

The computation is step 2 of the proof of Evans, §8.4.3, Theorem 5, equations (36)-(37).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §8.4.3, proof of Theorem 5.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.CalculusOfVariations

open Filter MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open FiniteProductComposition
open scoped ENNReal NNReal Topology InnerProductSpace Sobolev

variable {n m : ℕ} {Ω : Set ℝ^(n + 1)}
  [H : Boundary.C1ExtensionAtlas (n + 1) Ω]

/-- The normalized variation has the expected first variation of
Dirichlet energy for every bounded `H¹` direction. Boundary conditions enter
only when applying minimality, so they are not needed here. -/
theorem hasDerivAt_vectorDirichletEnergy_normalizedVariation
    (E : Extension.GraphSpace.Operator (n + 1) 1 2 Ω)
    {G : ℝ^m → ℝ^m} {C K M : ℝ≥0}
    (hG : ContDiff ℝ 1 G) (hbound : ∀ z, ‖fderiv ℝ G z‖ ≤ C)
    (hLip : LipschitzWith K (fderiv ℝ G))
    (heq : ∀ z, 1 / 2 ≤ ‖z‖ → ‖z‖ ≤ 2 → G z = NormedSpace.normalize z)
    (U V : Fin m → H¹(Ω))
    (hunit : ∀ᵐ x ∂domainMeasure (n + 1) Ω, ‖values U x‖ = 1)
    (hV : ∀ᵐ x ∂domainMeasure (n + 1) Ω, ‖values V x‖ ≤ M) :
    HasDerivAt
      (fun t : ℝ ↦ vectorDirichletEnergy
        (vectorCompositionOnOfExtension H.isOpen E (by norm_num) hG hbound
          (fun j ↦ U j + t • V j)))
      (∫ x, ∑ i : Fin (n + 1),
        (⟪derivatives U i x, derivatives V i x⟫_ℝ -
          ‖derivatives U i x‖ ^ 2 * ⟪values U x, values V x⟫_ℝ)
        ∂domainMeasure (n + 1) Ω) 0 := by
  have hcol (i : Fin (n + 1)) :=
    NormedSpace.hasDerivAt_integral_normalized_energy hbound hLip heq
      (memLp_values U).aestronglyMeasurable (memLp_values V).aestronglyMeasurable
      (memLp_derivatives U i) (memLp_derivatives V i) hunit hV
      (inner_values_derivatives_eq_zero_ae_of_norm_eq_one H.isOpen E (by norm_num) U hunit i)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ (hcol i).2)
  rw [← integral_finsetSum _ (fun i _ ↦ (hcol i).1)] at hsum
  apply HasDerivAt.congr_of_eventuallyEq hsum
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [vectorDirichletEnergy_eq_sum_integral]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [vectorCompositionOnOfExtension_derivatives_ae H.isOpen E
    (by norm_num) hG hbound (fun j ↦ U j + t • V j) i,
    values_add_smul_ae U V t, derivatives_add_smul_ae U V t i] with x hx hu hv
  rw [hx, hu, hv]

end PDE.CalculusOfVariations
