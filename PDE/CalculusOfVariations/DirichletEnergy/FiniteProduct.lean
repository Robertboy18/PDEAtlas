/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.FiniteProduct.Linear
public import PDE.Spaces.Sobolev.Variational.Spaces.H1

/-!
# Dirichlet energy of a finite Sobolev family

The energy is one half of the integral of the squared Frobenius norm of the
weak derivative. We write that norm as the sum of the squared Euclidean norms
of its columns, using the Sobolev representatives.
Every column is square-integrable, so this real-valued integral is finite.
-/

@[expose] public noncomputable section

namespace PDE.CalculusOfVariations

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace
open FiniteProductComposition
open scoped Sobolev

variable {n m : ℕ} {Ω : Set ℝ^n}

/-- The Dirichlet energy `½ ∫ |DU|²` of a finite family of `H¹` fields. -/
def vectorDirichletEnergy (U : Fin m → H¹(Ω)) : ℝ :=
  ∫ x, (∑ i : Fin n, ‖derivatives U i x‖ ^ 2) / 2 ∂domainMeasure n Ω

/-- The energy density is integrable because every weak derivative column is
square-integrable. No boundary or boundedness assumption is needed. -/
theorem integrable_vectorDirichletEnergy_density (U : Fin m → H¹(Ω)) :
    Integrable (fun x ↦ (∑ i : Fin n, ‖derivatives U i x‖ ^ 2) / 2)
      (domainMeasure n Ω) :=
  (integrable_finsetSum _ fun i _ ↦ (memLp_derivatives U i).norm.integrable_sq).div_const 2

/-- The Dirichlet energy is the sum of the energies of its derivative columns. -/
theorem vectorDirichletEnergy_eq_sum_integral (U : Fin m → H¹(Ω)) :
    vectorDirichletEnergy U =
      ∑ i : Fin n, ∫ x, ‖derivatives U i x‖ ^ 2 / 2 ∂domainMeasure n Ω := by
  simp only [vectorDirichletEnergy, Finset.sum_div]
  exact integral_finsetSum _ fun i _ ↦ (memLp_derivatives U i).norm.integrable_sq.div_const 2

/-- A squared-gradient energy is nonnegative. -/
theorem vectorDirichletEnergy_nonneg (U : Fin m → H¹(Ω)) :
    0 ≤ vectorDirichletEnergy U :=
  integral_nonneg fun _ ↦ div_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) (by norm_num)

end PDE.CalculusOfVariations
