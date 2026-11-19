/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.Schauder.HigherOrder.FluxDifferentiation
public import PDE.Spaces.Sobolev.Calculus.Product.Operator

/-!
# First derivatives of variable-coefficient divergence equations

For W¹,∞ coefficients, an H² solution of `div(A Du) = div F`, with H¹
forcing components, has derivatives satisfying
`div(A D(∂ₖu)) = div(∂ₖF - (∂ₖA) Du)`.

The weak Leibniz multiplier constructs the differentiated flux. Testing the
original identity against differentiated smooth tests gives its divergence
identity, which extends by density to every H¹₀ test. Keeping the commutator
as divergence forcing avoids requiring second derivatives of the coefficients.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace
open scoped ENNReal Sobolev InnerProductSpace

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set ℝ^n}

/-- The differentiated equation with its explicit L² divergence
forcing. All weak product derivatives are constructed from the input bundles;
no differentiated equation or coefficient second derivative is assumed. -/
theorem interiorVariableCoeffForm_partialDeriv_eq_commutator
    (hΩ : IsOpen Ω) (A : Fin n → Fin n → W^{1,∞}(Ω))
    (W : W^{2,2}(Ω)) (F : Fin n → H¹(Ω))
    (hu : ∀ v : H¹₀(Ω),
      interiorVariableCoeffForm
        (multiplicationCoefficientOperator (fun i j ↦ wkpBaseCoordinateCLM (A i j)))
        (lowerOrderCLM (by omega : 1 ≤ 2) W) v =
          ∑ i, ⟪wkpBaseCoordinateCLM (F i), derivCoordCLM i v⟫_ℝ)
    (k : Fin n) :
    ∀ v : H¹₀(Ω),
      interiorVariableCoeffForm
        (multiplicationCoefficientOperator (fun i j ↦ wkpBaseCoordinateCLM (A i j)))
        (∂[k] W) v =
          ∑ i, ⟪wkpCoordinateCLM (singleDerivIndex n k) (F i) -
            ∑ j, wkpCoordinateCLM (singleDerivIndex n k) (A i j) •
              wkpCoordinateCLM (singleDerivIndex n j)
                (lowerOrderCLM (by omega : 1 ≤ 2) W), derivCoordCLM i v⟫_ℝ := by
  let U : H¹(Ω) := lowerOrderCLM (by omega : 1 ≤ 2) W
  let a (i j : Fin n) := wkpBaseCoordinateCLM (A i j)
  let da (i j : Fin n) := wkpCoordinateCLM (singleDerivIndex n k) (A i j)
  let P (i j : Fin n) := w1TopMultiplierCLM hΩ (A i j) (∂[j] W)
  let Q (i : Fin n) : H¹(Ω) := (∑ j, P i j) - F i
  have hbase (j : Fin n) : wkpBaseCoordinateCLM (∂[j] W) =
      wkpCoordinateCLM (singleDerivIndex n j) U := by
    simp only [U, wkpBaseCoordinateCLM_apply, partialDerivCLM,
      derivativeWordCLM_apply, derivativeWordIndex_baseIndex, wkpCoordinateCLM_apply,
      lowerOrderCLM_apply, DerivIndex.castOrder_singleDerivIndex]
    rfl
  have hcomm (j : Fin n) :
      wkpCoordinateCLM (singleDerivIndex n k) (∂[j] W) =
        wkpCoordinateCLM (singleDerivIndex n j) (∂[k] W) := by
    simp only [partialDerivCLM, wkpCoordinateCLM_apply, derivativeWordCLM_apply,
      derivativeWordIndex_singleDerivIndex_comm j k (by omega : 2 ≤ 2)]
  have hP (i j : Fin n) : wkpBaseCoordinateCLM (P i j) =
      a i j • wkpCoordinateCLM (singleDerivIndex n j) U := by
    change w1TopMultiplierAmbient (A i j) (∂[j] W).val (baseIndex n 1) = _
    rw [w1TopMultiplierAmbient_base]
    change a i j • wkpBaseCoordinateCLM (∂[j] W) = _
    rw [hbase]
  have hDP (i j : Fin n) : wkpCoordinateCLM (singleDerivIndex n k) (P i j) =
      a i j • wkpCoordinateCLM (singleDerivIndex n j) (∂[k] W) +
        da i j • wkpCoordinateCLM (singleDerivIndex n j) U := by
    change w1TopMultiplierAmbient (A i j) (∂[j] W).val (singleDerivIndex n k) = _
    rw [w1TopMultiplierAmbient_singleDeriv]
    change a i j • wkpCoordinateCLM (singleDerivIndex n k) (∂[j] W) +
      da i j • wkpBaseCoordinateCLM (∂[j] W) = _
    rw [hcomm, hbase]
  have hzero : ∀ v : H¹₀(Ω),
      (∑ i, ⟪wkpBaseCoordinateCLM (Q i), derivCoordCLM i v⟫_ℝ) = 0 := by
    intro v
    simp only [Q, map_sub, map_sum, hP, inner_sub_left, sum_inner, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (hu v)
  intro v
  have ht := sum_inner_coordinateDerivative_eq_zero Q hzero k v
  simp only [Q, map_sub, map_sum, hDP, inner_sub_left, sum_inner, inner_add_left,
    Finset.sum_add_distrib, Finset.sum_sub_distrib] at ht
  change (∑ i, ∑ j,
    ⟪a i j • wkpCoordinateCLM (singleDerivIndex n j) (∂[k] W), derivCoordCLM i v⟫_ℝ) = _
  simp only [inner_sub_left, sum_inner, Finset.sum_sub_distrib]
  change _ = (∑ i, ⟪wkpCoordinateCLM (singleDerivIndex n k) (F i), derivCoordCLM i v⟫_ℝ) -
    ∑ i, ∑ j, ⟪da i j • wkpCoordinateCLM (singleDerivIndex n j) U, derivCoordCLM i v⟫_ℝ
  linarith

end SobolevSpace.GraphSpace
