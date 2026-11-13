/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Operators.Vector.Transport
public import PDE.Spaces.Sobolev.Calculus.Product.MatrixEnergy
import PDE.Spaces.Sobolev.GraphSpace.Norms

/-!
# Energy of symmetric matrix transport

Symmetry bounds the L² transport energy by the differentiated coefficients.
For the H¹ energy, differentiation adds the coefficient commutator,
whose bound uses the same first coefficient derivatives. The fields may
have arbitrary support on the whole space.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal InnerProductSpace Sobolev

variable {n m : ℕ}

/-- The full matrix transport has the L² energy bound obtained by summing the
symmetric integration-by-parts identity over spatial directions. -/
theorem vectorTransportCLM_energy_le
    (A : Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hA : ∀ j p q, wkpBaseCoordinateCLM (A j p q) = wkpBaseCoordinateCLM (A j q p))
    (U : Fin m → W^{1,2}(ℝ^n)) :
    2 * (∑ p, ⟪vectorTransportCLM (fun j p q ↦ wkpBaseCoordinateCLM (A j p q)) U p,
      wkpBaseCoordinateCLM (U p)⟫_ℝ) ≤
      (∑ j, ∑ p, ∑ q, ‖wkpCoordinateCLM (singleDerivIndex n j) (A j p q)‖) *
        (∑ p, ‖wkpBaseCoordinateCLM (U p)‖ ^ 2) := by
  have hrow (j : Fin n) := symmetric_matrix_transport_energy_le (A j) (hA j) j U
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hrow j)
  dsimp only at hsum
  simp only [← Finset.sum_mul, ← Finset.mul_sum] at hsum
  have hpair :
      (∑ p, ⟪vectorTransportCLM (fun j p q ↦ wkpBaseCoordinateCLM (A j p q)) U p,
        wkpBaseCoordinateCLM (U p)⟫_ℝ) =
      ∑ j, -(∑ p, ∑ q, ⟪wkpBaseCoordinateCLM (A j p q) •
        wkpCoordinateCLM (singleDerivIndex n j) (U q), wkpBaseCoordinateCLM (U p)⟫_ℝ) := by
    simp only [vectorTransportCLM_apply, inner_neg_left, sum_inner,
      Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
  rw [hpair]
  change (∑ j, -(∑ p, ∑ q, ⟪wkpBaseCoordinateCLM (A j p q) •
    wkpCoordinateCLM (singleDerivIndex n j) (U q), wkpBaseCoordinateCLM (U p)⟫_ℝ)) ≤
    (1 / 2 : ℝ) * (∑ j, ∑ p, ∑ q,
      ‖wkpCoordinateCLM (singleDerivIndex n j) (A j p q)‖) *
      (∑ p, ‖wkpBaseCoordinateCLM (U p)‖ ^ 2) at hsum
  linarith only [hsum]

/-- The coefficient derivative sum in the H¹ transport energy bound: the L∞ norms
of the divergence entries, plus twice the L∞ norms of all coefficient derivatives. -/
def transportDerivativeSum (A : Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n)) : ℝ :=
  (∑ j, ∑ p, ∑ q, ‖wkpCoordinateCLM (singleDerivIndex n j) (A j p q)‖) +
    2 * ∑ l, ∑ p, ∑ j, ∑ q,
      ‖wkpCoordinateCLM (singleDerivIndex n l) (A j p q)‖

/-- The H¹ transport energy is bounded by `transportDerivativeSum`.
The commutator is derived from the weak product rule, rather than assumed as an estimate. -/
theorem vectorTransportH1CLM_energy_le
    (A : Fin n → Fin m → Fin m → W^{1,∞}(ℝ^n))
    (hA : ∀ j p q, wkpBaseCoordinateCLM (A j p q) = wkpBaseCoordinateCLM (A j q p))
    (U : Fin m → W^{2,2}(ℝ^n)) :
    2 * (∑ p, ⟪vectorTransportH1CLM isOpen_univ A U p,
      lowerOrderCLM (by decide : 1 ≤ 2) (U p)⟫_ℝ) ≤
      transportDerivativeSum A * (∑ p, ‖lowerOrderCLM (by decide : 1 ≤ 2) (U p)‖ ^ 2) := by
  classical
  let W (p : Fin m) := lowerOrderCLM (by decide : 1 ≤ 2) (U p)
  let g (l : Fin n) (p : Fin m) := ∂[l] (U p)
  let P := vectorTransportCLM (fun j p q ↦ wkpBaseCoordinateCLM (A j p q))
  let R (l : Fin n) (p : Fin m) := ∑ j, ∑ q,
    wkpCoordinateCLM (singleDerivIndex n l) (A j p q) • wkpBaseCoordinateCLM (g j q)
  let C := ∑ j, ∑ p, ∑ q, ‖wkpCoordinateCLM (singleDerivIndex n j) (A j p q)‖
  let D := ∑ l, ∑ p, ∑ j, ∑ q,
    ‖wkpCoordinateCLM (singleDerivIndex n l) (A j p q)‖
  have hg (l : Fin n) (p : Fin m) :
      wkpCoordinateCLM (singleDerivIndex n l) (W p) = wkpBaseCoordinateCLM (g l p) := by
    simp only [W, g, partialDerivCLM,
      wkpCoordinateCLM_apply, wkpBaseCoordinateCLM_apply,
      lowerOrderCLM_apply, derivativeWordCLM_apply, derivativeWordIndex_baseIndex,
      derivIndexOfList_singleton, DerivIndex.castOrder_singleDerivIndex]
  have hinner (p : Fin m) :
      ⟪vectorTransportH1CLM isOpen_univ A U p, W p⟫_ℝ =
        ⟪P W p, wkpBaseCoordinateCLM (W p)⟫_ℝ +
          ∑ l, (⟪P (g l) p, wkpBaseCoordinateCLM (g l p)⟫_ℝ -
            ⟪R l p, wkpBaseCoordinateCLM (g l p)⟫_ℝ) := by
    change ⟪(vectorTransportH1CLM isOpen_univ A U p : WkpAmbientOn n 1 2 univ),
      (W p : WkpAmbientOn n 1 2 univ)⟫_ℝ = _
    rw [ambient_inner_eq_base_add_sum_deriv]
    change ⟪wkpBaseCoordinateCLM (vectorTransportH1CLM isOpen_univ A U p),
      wkpBaseCoordinateCLM (W p)⟫_ℝ +
      (∑ l, ⟪wkpCoordinateCLM (singleDerivIndex n l)
        (vectorTransportH1CLM isOpen_univ A U p),
        wkpCoordinateCLM (singleDerivIndex n l) (W p)⟫_ℝ) = _
    simp only [vectorTransportH1CLM_base, vectorTransportH1CLM_derivative, hg,
      inner_sub_left, P, R, W, g]
  have hpair :
      (∑ p, ⟪vectorTransportH1CLM isOpen_univ A U p, W p⟫_ℝ) =
        (∑ p, ⟪P W p, wkpBaseCoordinateCLM (W p)⟫_ℝ) +
        (∑ l, ∑ p, ⟪P (g l) p, wkpBaseCoordinateCLM (g l p)⟫_ℝ) -
        (∑ l, ∑ p, ⟪R l p, wkpBaseCoordinateCLM (g l p)⟫_ℝ) := by
    simp only [hinner, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    simp only [Finset.sum_sub_distrib]
    ring
  have hnorm : (∑ p, ‖W p‖ ^ 2) =
      (∑ p, ‖wkpBaseCoordinateCLM (W p)‖ ^ 2) +
        ∑ l, ∑ p, ‖wkpBaseCoordinateCLM (g l p)‖ ^ 2 := by
    have hc (p : Fin m) : ‖W p‖ ^ 2 = ‖wkpBaseCoordinateCLM (W p)‖ ^ 2 +
        ∑ l, ‖wkpCoordinateCLM (singleDerivIndex n l) (W p)‖ ^ 2 :=
      ambient_norm_sq_eq_base_sq_add_sum_deriv_sq (W p).val
    simp only [hc, hg, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
  have hbase := vectorTransportCLM_energy_le A hA W
  have hgrad :
      2 * (∑ l, ∑ p, ⟪P (g l) p, wkpBaseCoordinateCLM (g l p)⟫_ℝ) ≤
        C * (∑ l, ∑ p, ‖wkpBaseCoordinateCLM (g l p)‖ ^ 2) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l _
    simpa only [Finset.mul_sum] using vectorTransportCLM_energy_le A hA (g l)
  have hcomm : |∑ l, ∑ p, ⟪R l p, wkpBaseCoordinateCLM (g l p)⟫_ℝ| ≤
      D * (∑ l, ∑ p, ‖wkpBaseCoordinateCLM (g l p)‖ ^ 2) := by
    have h := abs_sum_inner_w1TopMultiplier_derivative_commutator_le A g
    simpa only [R, D, sum_inner, w1TopMultiplierCLM_apply_coe,
      w1TopMultiplierAmbient_singleDeriv, add_sub_cancel_left,
      wkpCoordinateCLM_apply, wkpBaseCoordinateCLM_apply] using h
  have hcommLower := (neg_le_abs _).trans hcomm
  have hcross : 0 ≤ D * (∑ p, ‖wkpBaseCoordinateCLM (W p)‖ ^ 2) := by
    apply mul_nonneg _ (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
    exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
      Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  change 2 * (∑ p, ⟪vectorTransportH1CLM isOpen_univ A U p, W p⟫_ℝ) ≤
    (C + 2 * D) * (∑ p, ‖W p‖ ^ 2)
  rw [hpair, hnorm]
  change 2 * (∑ p, ⟪P W p, wkpBaseCoordinateCLM (W p)⟫_ℝ) ≤
    C * (∑ p, ‖wkpBaseCoordinateCLM (W p)‖ ^ 2) at hbase
  nlinarith only [hbase, hgrad, hcommLower, hcross]

end SobolevSpace.GraphSpace
