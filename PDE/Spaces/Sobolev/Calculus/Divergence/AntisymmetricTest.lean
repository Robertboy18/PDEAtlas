/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Divergence.ZeroBoundary

/-!
# Solenoidal tests from antisymmetric derivatives

The vector test `eⱼ ∂ᵢφ - eᵢ ∂ⱼφ` lies in the vector H¹₀ space and
has zero weak divergence. This follows from commuting derivatives
of the smooth scalar test, including the repeated-index case.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal RealInnerProductSpace Sobolev

variable {n m : ℕ} {Ω : Set (ℝ^n)}

private theorem ZeroBoundaryVectorSpace.ofTestFunction_single_apply
    (j i : Fin m) (φ : TestFunctionOn n Ω) :
    ZeroBoundaryVectorSpace.ofTestFunction (Pi.single j φ) i =
      if i = j then testFunctionToH10 φ else 0 := by
  classical
  change testFunctionToH10Linear
    ((Pi.single j φ : Fin m → TestFunctionOn n Ω) i) = _
  by_cases hij : i = j
  · simp only [Pi.single_apply, hij, ite_true]
    rfl
  · simp [hij]

/-- A one-component vector test has its scalar derivative as divergence. -/
theorem ZeroBoundaryVectorSpace.divergence_ofTestFunction_single
    (j : Fin n) (φ : TestFunctionOn n Ω) :
    ∇· (ZeroBoundaryVectorSpace.ofTestFunction (Pi.single j φ)) =
      derivCoordCLM j (testFunctionToH10 φ) := by
  classical
  rw [ZeroBoundaryVectorSpace.divergence_apply]
  simp only [ZeroBoundaryVectorSpace.ofTestFunction_single_apply, apply_ite, map_zero]
  simp

/-- The full matrix-gradient pairing is the sum over both component indices. -/
theorem ZeroBoundaryVectorSpace.inner_gradient (u v : H¹₀(Ω; ℝ^m)) :
    ⟪∇ u, ∇ v⟫ =
      ∑ i : Fin m, ∑ j : Fin n, ⟪derivCoordCLM j (u i), derivCoordCLM j (v i)⟫ := by
  rw [ZeroBoundaryVectorSpace.gradient_eq_euclideanTuple,
    ZeroBoundaryVectorSpace.gradient_eq_euclideanTuple, Lp.inner_euclideanTuple,
    ← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]

/-- Pairing with a one-component test keeps every spatial derivative of
the selected component. -/
theorem ZeroBoundaryVectorSpace.inner_gradient_ofTestFunction_single
    (u : H¹₀(Ω; ℝ^m)) (i : Fin m) (φ : TestFunctionOn n Ω) :
    ⟪∇ u,
      ∇ (ZeroBoundaryVectorSpace.ofTestFunction (Pi.single i φ))⟫ =
      ∑ j : Fin n, ⟪derivCoordCLM j (u i),
        derivCoordCLM j (testFunctionToH10 φ)⟫ := by
  classical
  rw [ZeroBoundaryVectorSpace.inner_gradient]
  simp only [ZeroBoundaryVectorSpace.ofTestFunction_single_apply, apply_ite, map_zero]
  simp

/-- An antisymmetric derivative of a scalar test, as a vector H¹₀ field. -/
def antisymmetricTest (i j : Fin n) (φ : TestFunctionOn n Ω) :
    H¹₀(Ω; ℝ^n) :=
  ZeroBoundaryVectorSpace.ofTestFunction
    (Pi.single j (φ.iteratedPartialDeriv [i]) -
      Pi.single i (φ.iteratedPartialDeriv [j]))

/-- Antisymmetric derivative tests are divergence free in the L² sense. -/
theorem ZeroBoundaryVectorSpace.divergence_antisymmetricTest
    (i j : Fin n) (φ : TestFunctionOn n Ω) :
    ∇· (antisymmetricTest i j φ) = 0 := by
  classical
  rw [antisymmetricTest, map_sub, map_sub,
    ZeroBoundaryVectorSpace.divergence_ofTestFunction_single,
    ZeroBoundaryVectorSpace.divergence_ofTestFunction_single, sub_eq_zero]
  apply Lp.ext
  filter_upwards [derivCoordCLM_testFunction_apply_ae j (φ.iteratedPartialDeriv [i]),
    derivCoordCLM_testFunction_apply_ae i (φ.iteratedPartialDeriv [j])] with x hx hy
  rw [hx, hy]
  exact PDE.partialDeriv_partialDeriv_comm j i (φ.1.contDiff.of_le (by simp)) x

end SobolevSpace.GraphSpace
