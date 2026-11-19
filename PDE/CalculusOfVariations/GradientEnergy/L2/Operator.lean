/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.CalculusOfVariations.GradientEnergy.L2.Domain

/-!
# The Hessian formula for the ambient gradient-energy operator

The chain rule for the nonlinear flux identifies its negative
divergence with the contraction of the density Hessian and the weak
second derivatives. Both derivative indices come from the same H² field.
This gives the almost-everywhere formula for the operator in
Evans, §9.6.3, Theorem 4 (iii), with the divergence expanded by the
chain rule.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.6.3, Theorem 4 (iii).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace PDE.CalculusOfVariations

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace Analysis.Convex
open scoped ENNReal NNReal RealInnerProductSpace Sobolev

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)} {L : ℝ^n → ℝ}

/-- On H² Dirichlet fields, membership in the L² subdifferential
is exactly the negative Hessian contraction formula.
No pointwise classical differentiability of the Sobolev field is assumed. -/
theorem mem_subdifferential_l2DirichletGradientEnergy_iff_hessian
    (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hgraph : Boundary.HasContDiffGraphBoundary 2 Ω)
    (hL : ContDiff ℝ 2 L) {θ : ℝ} (hθ : 0 < θ) {C : ℝ≥0}
    (hlower : ∀ x v, θ * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ L) x v v)
    (hupper : ∀ x, ‖fderiv ℝ (fderiv ℝ L) x‖ ≤ C)
    (W : W^{2,2}(Ω)) (u : H¹₀(Ω))
    (hu : lowerOrderCLM (by omega : 1 ≤ 2) W = u.val) (f : DerivLp n 2 Ω) :
    f ∈ subdifferential (l2DirichletGradientEnergy L) (baseCoordCLM u) ↔
      (f : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
        -∑ i, fderiv ℝ (fderiv ℝ L)
          (FiniteProductComposition.values (h2FirstDerivativeFamily W) x)
          (FiniteProductComposition.derivatives (h2FirstDerivativeFamily W) i x)
          (EuclideanSpace.single i 1) := by
  obtain ⟨Q, _, hDQ, hQ⟩ :=
    exists_flux_subdifferential_l2DirichletGradientEnergy_eq_singleton
      hΩ hbounded hgraph hL hθ hlower hupper W u hu
  have hformula : (negativeDivergence Q : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] fun x ↦
      -∑ i, fderiv ℝ (fderiv ℝ L)
        (FiniteProductComposition.values (h2FirstDerivativeFamily W) x)
        (FiniteProductComposition.derivatives (h2FirstDerivativeFamily W) i x)
        (EuclideanSpace.single i 1) := by
    filter_upwards [negativeDivergence_ae Q, hDQ] with x hx hd
    rw [hx]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hd i i]
    simpa only [EuclideanSpace.inner_single_right, one_mul, RCLike.conj_to_real] using
      Analysis.inner_fderiv_gradient_at hL.contDiffAt
        (FiniteProductComposition.derivatives (h2FirstDerivativeFamily W) i x)
        (EuclideanSpace.single i 1)
  rw [hQ, mem_singleton_iff]
  constructor
  · rintro rfl
    exact hformula
  · intro hf
    exact Lp.ext (hf.trans hformula.symm)

end PDE.CalculusOfVariations
