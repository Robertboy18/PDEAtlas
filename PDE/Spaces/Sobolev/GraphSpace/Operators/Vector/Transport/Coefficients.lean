/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.Transport

/-!
# Dependence of matrix transport on its coefficients

Matrix transport is a bounded linear function of its L∞ coefficients, with
an operator-norm bound from entrywise bounds. The same transport acts on finite
Hilbert products by conjugation with the finite-product equivalences.
The sign remains the evolution drift `-∑ⱼ Aʲ ∂ⱼ`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev ENNReal

/-- The inherited normed group on transport operators, named to keep nested
operator typeclass search short. -/
local instance SobolevSpace.GraphSpace.transportOperatorNormedAddCommGroup {n m : ℕ} {Ω : Set ℝ^n} :
    NormedAddCommGroup ((Fin m → W^{1,2}(Ω)) →L[ℝ] (Fin m → DerivLp n 2 Ω)) :=
  ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)
    (E := Fin m → W^{1,2}(Ω)) (F := Fin m → DerivLp n 2 Ω)

/-- The inherited real normed-space structure on transport operators. -/
local instance SobolevSpace.GraphSpace.transportOperatorNormedSpace {n m : ℕ} {Ω : Set ℝ^n} :
    NormedSpace ℝ ((Fin m → W^{1,2}(Ω)) →L[ℝ] (Fin m → DerivLp n 2 Ω)) :=
  ContinuousLinearMap.toNormedSpace (σ₁₂ := RingHom.id ℝ)
    (E := Fin m → W^{1,2}(Ω)) (F := Fin m → DerivLp n 2 Ω)

namespace SobolevSpace.GraphSpace

variable {n m : ℕ} {Ω : Set ℝ^n}

/-- Matrix transport as a bounded linear function of its L∞ coefficients.
Its values are the H¹-to-L² transport operators. -/
def vectorTransportCoefficientCLM :
    (Fin n → Fin m → Fin m → DerivLp n ∞ Ω) →L[ℝ]
      (Fin m → W^{1,2}(Ω)) →L[ℝ] (Fin m → DerivLp n 2 Ω) where
  toFun := vectorTransportCLM
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro U
    funext p
    simp only [vectorTransportCLM_apply, Pi.add_apply, add_apply,
      Lp.smul_add, Finset.sum_add_distrib, neg_add]
  map_smul' c A := by
    apply ContinuousLinearMap.ext
    intro U
    funext p
    simp only [vectorTransportCLM_apply, Pi.smul_apply, smul_apply,
      RingHom.id_apply, Lp.smul_assoc, Finset.smul_sum, smul_neg]
  cont := continuous_vectorTransportCLM

/-- The coefficient-linear map evaluates to the original transport operator. -/
@[simp]
theorem vectorTransportCoefficientCLM_apply
    (A : Fin n → Fin m → Fin m → DerivLp n ∞ Ω) :
    vectorTransportCoefficientCLM A = vectorTransportCLM A := rfl

/-- Uniform entrywise coefficient bounds control the transport operator norm.
The fixed constant depends only on the Sobolev spaces and component dimensions. -/
theorem norm_vectorTransportCLM_le_of_entry_bound
    (A : Fin n → Fin m → Fin m → DerivLp n ∞ Ω) {M : ℝ} (hM : 0 ≤ M)
    (hA : ∀ j p q, ‖A j p q‖ ≤ M) :
    ‖vectorTransportCLM A‖ ≤ ‖vectorTransportCoefficientCLM (n := n) (m := m) (Ω := Ω)‖ * M := by
  apply (vectorTransportCoefficientCLM.le_opNorm A).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (pi_norm_le_iff_of_nonneg hM).mpr fun j ↦
    (pi_norm_le_iff_of_nonneg hM).mpr fun p ↦
      (pi_norm_le_iff_of_nonneg hM).mpr (hA j p)

/-- The transport operator on the finite Hilbert products, obtained
by conjugating with Mathlib's finite-product equivalences. -/
def vectorTransportPiLpCLM (A : Fin n → Fin m → Fin m → DerivLp n ∞ Ω) :
    PiLp 2 (fun _ : Fin m ↦ W^{1,2}(Ω)) →L[ℝ]
      PiLp 2 (fun _ : Fin m ↦ DerivLp n 2 Ω) :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin m ↦ DerivLp n 2 Ω)).symm.toContinuousLinearMap.comp ((vectorTransportCLM A).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m ↦ W^{1,2}(Ω))).toContinuousLinearMap)

/-- The Hilbert-product transport has the same component values as the
original finite-product transport. -/
@[simp]
theorem vectorTransportPiLpCLM_apply
    (A : Fin n → Fin m → Fin m → DerivLp n ∞ Ω)
    (U : PiLp 2 (fun _ : Fin m ↦ W^{1,2}(Ω))) (p : Fin m) :
    vectorTransportPiLpCLM A U p = vectorTransportCLM A (fun q ↦ U q) p := rfl

end SobolevSpace.GraphSpace
