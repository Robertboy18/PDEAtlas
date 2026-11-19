/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.Constraints.Sphere.FirstVariation

/-!
# The weak equation for a sphere-constrained minimizer

A minimizer can be compared with normalized zero-boundary variations.
Their first variation gives `-ΔU = |DU|² U` in the weak sense. The test
field belongs to `H¹₀ ∩ L∞`: its boundedness keeps normalization away from
zero and makes the radial term integrable.

No regularity of the minimizer beyond `H¹` is required: the chain rule and
differentiation under the integral are proved for the Sobolev map itself.

We follow the proof of Evans, §8.4.3, Theorem 5, which compares the minimizer with
`(U + τV) / |U + τV|` and differentiates at `τ = 0`. The part Evans leaves implicit, and that we
prove, is that this normalized map lies in `H¹` with the right boundary values: we write it as a
Sobolev composition with a smooth map that agrees with normalization near the sphere.

## Main results

* `integral_inner_derivatives_eq_of_sphere_minimizer`: the weak harmonic-map equation against
  every bounded zero-boundary test field, given a `C¹` extension atlas, an inward partition and
  an extension operator for the domain.

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

variable {n m : ℕ} {Ω : Set ℝ^(n + 1)}
  [H : Boundary.C1ExtensionAtlas (n + 1) Ω]

/-- A sphere-valued Dirichlet minimizer satisfies the weak harmonic-map
equation against every bounded zero-boundary Sobolev field. -/
theorem integral_inner_derivatives_eq_of_sphere_minimizer
    (P : Approximation.UpToBoundary.InwardPartition Ω)
    (E : Extension.GraphSpace.Operator (n + 1) 1 2 Ω)
    (U : Fin m → H¹(Ω))
    (hunit : ∀ᵐ x ∂domainMeasure (n + 1) Ω, ‖values U x‖ = 1)
    (hmin : ∀ W : Fin m → H¹(Ω),
      (∀ᵐ x ∂domainMeasure (n + 1) Ω, ‖values W x‖ = 1) →
      (∀ j, W j - U j ∈ (h10SubmoduleOn (n := n + 1) (Ω := Ω)).toSubmodule) →
      vectorDirichletEnergy U ≤ vectorDirichletEnergy W)
    (V : Fin m → H¹₀(Ω)) {M : ℝ≥0}
    (hV : ∀ᵐ x ∂domainMeasure (n + 1) Ω,
      ‖values (fun j ↦ (V j : H¹(Ω))) x‖ ≤ M) :
    (∫ x, ∑ i : Fin (n + 1),
      ⟪derivatives U i x,
        derivatives (fun j ↦ (V j : H¹(Ω))) i x⟫_ℝ
        ∂domainMeasure (n + 1) Ω) =
      ∫ x, (∑ i : Fin (n + 1), ‖derivatives U i x‖ ^ 2) *
        ⟪values U x, values (fun j ↦ (V j : H¹(Ω))) x⟫_ℝ
        ∂domainMeasure (n + 1) Ω := by
  classical
  let V' : Fin m → H¹(Ω) := fun j ↦ V j
  obtain ⟨G, hG, hcompact, heq, C₀, hC₀⟩ :=
    NormedSpace.exists_contDiff_compactSupport_eqOn_normalize
      (E := ℝ^m) (a := 1 / 2) (b := 2) (by norm_num) (by norm_num)
  let C : ℝ≥0 := ⟨max C₀ 0, le_max_right _ _⟩
  have hbound (z : ℝ^m) : ‖fderiv ℝ G z‖ ≤ C :=
    (hC₀ z).trans (le_max_left _ _)
  have hG₁ : ContDiff ℝ 1 G := hG.of_le (by simp)
  have hDG : ContDiff ℝ 1 (fderiv ℝ G) := hG.fderiv_right (by simp)
  obtain ⟨K, hLip⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport (hcompact.fderiv ℝ) hDG (by norm_num)
  let W (t : ℝ) := vectorCompositionOnOfExtension H.isOpen E
    (by norm_num) hG₁ hbound (fun j ↦ U j + t • V' j)
  have hzero : W 0 = U := by
    simpa only [W, zero_smul, add_zero] using
      vectorComposition_eq_self_of_norm_values_eq_one E hG₁ hbound heq U hunit
  have hsmall : ∀ᶠ t : ℝ in 𝓝 0, |t| * (M : ℝ) < 1 / 2 :=
    (continuous_abs.mul_const (M : ℝ)).continuousAt.eventually
      (gt_mem_nhds (by norm_num))
  have hlocal : IsLocalMin (fun t ↦ vectorDirichletEnergy (W t)) 0 := by
    filter_upwards [hsmall] with t ht
    rw [hzero]
    exact hmin (W t)
      (normalizedVariation_norm_values_eq_one_ae E hG₁ hbound heq U V' hunit hV ht)
      (normalizedVariation_sub_mem_H10 P E hG₁ hbound heq U hunit V t)
  have hz := hlocal.hasDerivAt_eq_zero
    (hasDerivAt_vectorDirichletEnergy_normalizedVariation
      E hG₁ hbound hLip heq U V' hunit hV)
  have hinner (i : Fin (n + 1)) : Integrable
      (fun x ↦ ⟪derivatives U i x, derivatives V' i x⟫_ℝ)
      (domainMeasure (n + 1) Ω) := by
    apply ((memLp_derivatives U i).norm.integrable_mul
      (memLp_derivatives V' i).norm).mono'
      ((memLp_derivatives U i).aestronglyMeasurable.inner
        (memLp_derivatives V' i).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun x ↦ norm_inner_le_norm _ _)
  have hradial (i : Fin (n + 1)) : Integrable
      (fun x ↦ ‖derivatives U i x‖ ^ 2 * ⟪values U x, values V' x⟫_ℝ)
      (domainMeasure (n + 1) Ω) := by
    apply (memLp_derivatives U i).norm.integrable_sq.mul_bdd (c := (M : ℝ))
      ((memLp_values U).aestronglyMeasurable.inner
        (memLp_values V').aestronglyMeasurable)
    filter_upwards [hunit, hV] with x hx hv
    exact (norm_inner_le_norm _ _).trans (by simpa [hx] using hv)
  have hs : (fun x ↦ ∑ i : Fin (n + 1),
      (⟪derivatives U i x, derivatives V' i x⟫_ℝ -
        ‖derivatives U i x‖ ^ 2 * ⟪values U x, values V' x⟫_ℝ)) =
      (fun x ↦ (∑ i : Fin (n + 1), ⟪derivatives U i x, derivatives V' i x⟫_ℝ) -
        ∑ i : Fin (n + 1),
          ‖derivatives U i x‖ ^ 2 * ⟪values U x, values V' x⟫_ℝ) := by
    funext x
    simp only [Finset.sum_sub_distrib]
  rw [hs, integral_sub (integrable_finsetSum _ (fun i _ ↦ hinner i))
    (integrable_finsetSum _ (fun i _ ↦ hradial i)), sub_eq_zero] at hz
  simpa only [Finset.sum_mul, V'] using hz

end PDE.CalculusOfVariations
