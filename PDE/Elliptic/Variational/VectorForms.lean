/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.VectorZeroBoundary
public import PDE.Elliptic.Variational.PrincipalForms

/-!
# The vector Dirichlet form

Summing the scalar forms gives the weak vector Laplacian. Its pairing is the
integral of the full matrix-gradient inner product. The full `H¹` norm gives Gårding
constants one without boundary assumptions; on bounded sets in positive spatial dimension,
the scalar Poincaré theorem also gives coercivity.
-/

@[expose] public noncomputable section

open SobolevSpace.GraphSpace.ZeroBoundaryVectorSpace
open scoped Sobolev

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped InnerProductSpace

variable {n m : ℕ} {Ω : Set (ℝ^n)}

local notation "μ" => domainMeasure n Ω

/-- The vector Dirichlet form is the sum of the scalar forms over all components. -/
def vectorDirichletForm : H¹₀(Ω; ℝ^m) →L[ℝ] StrongDual ℝ H¹₀(Ω; ℝ^m) :=
  ∑ i : Fin m, dirichletForm.bilinearComp (PiLp.proj 2 _ i) (PiLp.proj 2 _ i)

/-- The vector form evaluates as a sum of scalar Dirichlet pairings. -/
theorem vectorDirichletForm_apply (u v : H¹₀(Ω; ℝ^m)) :
    vectorDirichletForm u v = ∑ i, dirichletForm (u i) (v i) := by
  simp [vectorDirichletForm, ContinuousLinearMap.bilinearComp_apply]

/-- The vector Dirichlet form pairs the full weak gradients. -/
theorem vectorDirichletForm_eq_inner_gradient (u v : H¹₀(Ω; ℝ^m)) :
    vectorDirichletForm u v = ⟪∇ u, ∇ v⟫_ℝ := by
  rw [gradient_eq_euclideanTuple, gradient_eq_euclideanTuple,
    Lp.inner_euclideanTuple, ← Equiv.sum_comp finProdFinEquiv]
  simp [vectorDirichletForm_apply, dirichletForm_apply, Fintype.sum_prod_type]

/-- The weak vector Laplacian uses every entry of the Frobenius gradient pairing. -/
theorem vectorDirichletForm_eq_integral (u v : H¹₀(Ω; ℝ^m)) :
    vectorDirichletForm u v =
      ∫ x, ∑ i : Fin m, ∑ j : Fin n,
        (∇ u) x (finProdFinEquiv (i, j)) * (∇ v) x (finProdFinEquiv (i, j)) ∂μ := by
  exact (vectorDirichletForm_eq_inner_gradient u v).trans
    (Lp.inner_eq_integral_prod_sum (∇ u) (∇ v))

/-- Smooth compactly supported vector tests give the distributional Laplacian pairing. -/
theorem vectorDirichletForm_testFunction_eq_integral
    (u : H¹₀(Ω; ℝ^m)) (φ : Fin m → TestFunctionOn n Ω) :
    vectorDirichletForm u (ofTestFunction φ) =
      ∫ x, ∑ i : Fin m, ∑ j : Fin n,
        (∇ u) x (finProdFinEquiv (i, j)) *
          (∂[j] (φ i).1.toFun) x ∂μ := by
  rw [vectorDirichletForm_eq_integral]
  apply integral_congr_ae
  filter_upwards [gradient_ofTestFunction_apply_ae φ] with x hx
  simp only [hx]

/-- The vector Dirichlet energy is the squared full matrix-gradient norm. -/
theorem vectorDirichletForm_self (u : H¹₀(Ω; ℝ^m)) :
    vectorDirichletForm u u = ‖∇ u‖ ^ 2 := by
  rw [vectorDirichletForm_eq_inner_gradient, real_inner_self_eq_norm_sq]

/-- The full Sobolev norm gives the exact Gårding identity with both constants one. -/
theorem vectorDirichletForm_garding (u : H¹₀(Ω; ℝ^m)) :
    ‖u‖ ^ 2 = vectorDirichletForm u u + ‖toLp u‖ ^ 2 := by
  rw [vectorDirichletForm_self, norm_sq, add_comm]

/-- The vector Dirichlet form has operator norm at most one for the full Sobolev norm. -/
theorem norm_vectorDirichletForm_le :
    ‖vectorDirichletForm (n := n) (m := m) (Ω := Ω)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one
  intro u v
  rw [one_mul]
  rw [vectorDirichletForm_eq_inner_gradient]
  exact (norm_inner_le_norm (∇ u) (∇ v)).trans
    (mul_le_mul (norm_gradient_le u) (norm_gradient_le v)
      (norm_nonneg _) (norm_nonneg _))

/-- The scalar bounded-domain Poincaré estimate gives coercivity for every finite target. -/
theorem vectorDirichletForm_isCoercive
    (hn : 0 < n) (hΩbounded : Bornology.IsBounded Ω) :
    IsCoercive (vectorDirichletForm (n := n) (m := m) (Ω := Ω)) := by
  obtain ⟨C, hC, h⟩ := dirichletForm_isCoercive hn hΩbounded
  refine ⟨C, hC, fun u ↦ ?_⟩
  rw [mul_assoc, ← pow_two, PiLp.norm_sq_eq_of_L2, Finset.mul_sum,
    vectorDirichletForm_apply]
  exact Finset.sum_le_sum fun i _ ↦ by simpa only [pow_two, mul_assoc] using h (u i)

end SobolevSpace.GraphSpace
