/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Classical.VariableCoefficient.Operator
public import PDE.Analysis.Matrix.CharacteristicFlux

/-!
# Eikonal directions and the wave-energy flux

The principal matrix determines both the energy and the eikonal equation.
Completing its quadratic square proves the characteristic flux inequality.
-/

@[expose] public noncomputable section

namespace WaveEquation.VariableCoefficient

open PDE.Common
open scoped Matrix

variable {n : ℕ}

/-- Symmetry and a nonnegative quadratic form produce Mathlib's matrix positivity. -/
theorem posSemidef_of_quadratic_nonneg {A : Matrix (Fin n) (Fin n) ℝ} (hsymm : ∀ i j, A i j = A j i)
    (hpos : ∀ v : ℝ^n, 0 ≤ ∑ i, ∑ j, A i j * v i * v j) :
    A.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simpa using hsymm j i
  · intro v
    have h := hpos (WithLp.toLp 2 v)
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc] using h

/-- The flux in any eikonal direction is bounded by the full matrix energy. -/
theorem energyFlux_eikonal_le {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ} (u : ℝ^(n + 1) → ℝ)
    (p : ℝ^(n + 1)) (z : ℝ^n) (hsymm : ∀ i j, a (spatialPart p) i j = a (spatialPart p) j i)
    (hpos : ∀ v : ℝ^n, 0 ≤ ∑ i, ∑ j, a (spatialPart p) i j * v i * v j)
    (hz : ∑ i, ∑ j, a (spatialPart p) i j * z i * z j = 1) :
    (∑ j, energyFlux a u j p * z j) ≤ energyDensity a u p := by
  have hA := posSemidef_of_quadratic_nonneg hsymm hpos
  have hz' : (fun i ↦ z i) ⬝ᵥ (a (spatialPart p) *ᵥ (fun i ↦ z i)) = 1 := by
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc] using hz
  have h := hA.mul_dotProduct_mulVec_le_half
    (fun i ↦ (∂[i.succ] u) p) (fun i ↦ z i) ((∂[0] u) p) hz'
  have heq : (∑ j, energyFlux a u j p * z j) = (∂[0] u) p * ((fun i ↦ (∂[i.succ] u) p) ⬝ᵥ
          (a (spatialPart p) *ᵥ (fun i ↦ z i))) := by
    simp only [energyFlux, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [heq]
  convert h using 1
  simp [energyDensity, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_left_comm, mul_comm]

end WaveEquation.VariableCoefficient
