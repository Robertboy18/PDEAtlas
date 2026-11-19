/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.MatrixSymbol.Regularity

/-!
# Differential identity for a matrix-symbol inverse transform

The time generator cancels the spatial Fourier derivatives at each frequency.
Integrability of the joint derivative then gives the same identity for the
Fréchet derivative of the inverse transform.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators Matrix.Norms.L2Operator

namespace PDE.Analysis.Fourier

variable {n m : ℕ}

/-- The time generator in coordinates, with the inverse Fourier sign. -/
theorem symbolGenerator_apply
    (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (ξ : ℝ^n) (v : EuclideanSpace ℂ (Fin m)) :
    symbolGenerator A ξ v = -(2 * Real.pi * Complex.I) •
      ∑ j, ξ j • Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) (A j) v := by
  have hs (j : Fin n) :
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) (ξ j • A j) =
        ξ j • Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) (A j) :=
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m)).toAlgEquiv.toLinearMap.map_smul_of_tower
      (ξ j) (A j)
  simp only [symbolGenerator, smul_apply, map_sum, hs, sum_apply]
  module

/-- Contract a joint derivative with the linear matrix symbol, using the
time direction and the standard spatial coordinate directions. -/
def symbolContraction (A : Fin n → Matrix (Fin m) (Fin m) ℂ) :
    ((ℝ × ℝ^n) →L[ℝ] EuclideanSpace ℂ (Fin m)) →L[ℝ]
      EuclideanSpace ℂ (Fin m) :=
  ContinuousLinearMap.apply ℝ _ (1, 0) + ∑ j,
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) (A j)).restrictScalars ℝ).comp
      (ContinuousLinearMap.apply ℝ _ (0, EuclideanSpace.single j 1))

/-- The contraction is the sum of the time derivative and the coefficient
matrices applied to the spatial derivatives. -/
@[simp]
theorem symbolContraction_apply (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (D : (ℝ × ℝ^n) →L[ℝ] EuclideanSpace ℂ (Fin m)) :
    symbolContraction A D = D (1, 0) + ∑ j,
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) (A j)
        (D (0, EuclideanSpace.single j 1)) := by
  simp [symbolContraction]

/-- The Fourier time and spatial derivatives cancel before integration. -/
theorem symbolContraction_inverseKernelDerivative
    (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (ξ : ℝ^n) (p : ℝ × ℝ^n)
    (v : EuclideanSpace ℂ (Fin m)) :
    symbolContraction A (inverseKernelDerivative ξ p v (symbolGenerator A ξ v)) = 0 := by
  rw [symbolContraction_apply]
  simp only [inverseKernelDerivative_apply, one_smul, inner_zero_right, zero_smul,
    zero_add, EuclideanSpace.inner_single_right, conj_trivial, one_mul,
    map_smul, symbolGenerator_apply]
  have hs (j : Fin n) :
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) (A j) (ξ j • v) =
        ξ j • Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) (A j) v :=
    (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin m) (A j)).map_smul_of_tower (ξ j) v
  simp only [hs, ← Finset.smul_sum]
  module

/-- The inverse transform satisfies the joint differential identity.
The conclusion holds at every signed time, in particular at time zero. -/
theorem symbolContraction_fderiv_symbolEvolution
    (A : Fin n → Matrix (Fin m) (Fin m) ℂ)
    (hA : ∀ ξ : ℝ^n,
      ∀ z ∈ spectrum ℂ (∑ j, ξ j • A j), z.im = 0)
    (g : Lp (EuclideanSpace ℂ (Fin m)) 1
      (volume : Measure (ℝ^n)))
    (hmom : ∀ k ≤ m, Integrable (fun ξ : ℝ^n ↦
      ‖ξ‖ ^ k * ‖g ξ‖))
    (p : ℝ × ℝ^n) :
    symbolContraction A (fderiv ℝ (fun q : ℝ × ℝ^n ↦
      𝓕⁻ (fun ξ ↦ symbolMultiplier A q.1 ξ (g ξ)) q.2) p) = 0 := by
  obtain ⟨hKi, hder⟩ := (contDiff_one_symbolEvolution A hA g hmom).2 p
  rw [hder.fderiv, ← (symbolContraction A).integral_comp_comm hKi]
  simp only [symbolContraction_inverseKernelDerivative, integral_zero]

end PDE.Analysis.Fourier
