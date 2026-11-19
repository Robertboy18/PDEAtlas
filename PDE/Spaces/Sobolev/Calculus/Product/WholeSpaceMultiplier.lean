/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Product.HigherOrderOperator
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivativeCoordinates
public import PDE.Spaces.Sobolev.GraphSpace.Operators.ZeroOrder
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Whole-space Sobolev multipliers of every order

For every order `k`, including `k = 0`, multiplication by a coefficient in `W^{k,∞}(ℝ^n)` is a
bounded bilinear map

`wkMultiplication k : W^{k,∞}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n)`

with norm at most `wkTopMultiplierNormBound n k`. At order zero it is the `L∞`-by-`L²` Hölder
product, and at positive order it is `wkTopMultiplicationCLM` on `ℝ^n`. A whole-space Sobolev
element is determined by its base coordinate, and the base coordinate of the product is the
product of the base coordinates. This identifies the product after lowering the order and
gives the weak Leibniz rule `∂ᵢ(A U) = A ∂ᵢU + (∂ᵢA) U` as an identity in `W^{k,2}(ℝ^n)`.

## Main results

* `wkMultiplication`, with `wkMultiplication_base_ae` and
  `wkpBaseCoordinateCLM_wkMultiplication`.
* `norm_mul_wk_le`: `‖A U‖_{W^{k,2}} ≤ wkTopMultiplierNormBound n k ‖A‖_{W^{k,∞}} ‖U‖_{W^{k,2}}`,
  and the operator form `norm_wkMultiplication_le`.
* `lowerOrderCLM_wkMultiplication`: multiplication commutes with lowering the order.
* `partialDerivCLM_wkMultiplication`: the weak Leibniz rule for one partial derivative.
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

variable {n : ℕ}

/-- The `L∞`-by-`L²` product as a bounded bilinear map of order-zero whole-space Sobolev
elements. -/
def zeroOrderMultiplicationCLM :
    W^{0,∞}(ℝ^n) →L[ℝ] W^{0,2}(ℝ^n) →L[ℝ] W^{0,2}(ℝ^n) :=
  ((ContinuousLinearMap.compL ℝ (DerivLp n 2 Set.univ) (DerivLp n 2 Set.univ)
      (W^{0,2}(ℝ^n))
      (lpEquivZeroOrder (n := n) (p := 2)
        (Ω := Set.univ)).toContinuousLinearEquiv.toContinuousLinearMap).comp
    ((ContinuousLinearMap.mul ℝ ℝ).holderL (domainMeasure n Set.univ) ∞ 2 2)).bilinearComp
    wkpBaseCoordinateCLM wkpBaseCoordinateCLM

/-- The base coordinate of the order-zero product is the Hölder product of the base
coordinates. -/
theorem wkpBaseCoordinateCLM_zeroOrderMultiplicationCLM (A : W^{0,∞}(ℝ^n))
    (U : W^{0,2}(ℝ^n)) :
    wkpBaseCoordinateCLM (zeroOrderMultiplicationCLM A U) =
      (ContinuousLinearMap.mul ℝ ℝ).holder 2 (wkpBaseCoordinateCLM A)
        (wkpBaseCoordinateCLM U) :=
  rfl

/-- Multiplication by a `W^{k,∞}(ℝ^n)` coefficient on `W^{k,2}(ℝ^n)`, at every order. -/
def wkMultiplication : (k : ℕ) → W^{k,∞}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n)
  | 0 => zeroOrderMultiplicationCLM
  | k + 1 => wkTopMultiplicationCLM (Nat.succ_pos k) isOpen_univ

/-- The base representative of the product is the product of the base representatives. -/
theorem wkMultiplication_base_ae (k : ℕ) (A : W^{k,∞}(ℝ^n)) (U : W^{k,2}(ℝ^n)) :
    baseRepresentative (wkMultiplication k A U) =ᵐ[volume]
      fun x ↦ baseRepresentative A x * baseRepresentative U x := by
  cases k with
  | zero =>
    have h := (ContinuousLinearMap.mul ℝ ℝ).coeFn_holder (r := 2)
      (wkpBaseCoordinateCLM A) (wkpBaseCoordinateCLM U)
    simp only [domainMeasure, Measure.restrict_univ] at h
    exact h
  | succ k =>
    have h := wkTopProduct_base_ae (n := n) (Ω := Set.univ) (Nat.succ_pos k) isOpen_univ A U
    simp only [domainMeasure, Measure.restrict_univ] at h
    exact h

/-- The base coordinate of the product is the `L∞`-by-`L²` product of the base coordinates. -/
theorem wkpBaseCoordinateCLM_wkMultiplication (k : ℕ) (A : W^{k,∞}(ℝ^n))
    (U : W^{k,2}(ℝ^n)) :
    wkpBaseCoordinateCLM (wkMultiplication k A U) =
      mulLpLeft (wkpBaseCoordinateCLM A) (wkpBaseCoordinateCLM U) := by
  apply Lp.ext
  filter_upwards [ae_restrict_of_ae (s := Set.univ) (wkMultiplication_base_ae k A U),
    mulLpLeft_apply_ae (wkpBaseCoordinateCLM A) (wkpBaseCoordinateCLM U)] with x hx hm
  exact hx.trans hm.symm

/-- The Sobolev multiplier bound
`‖A U‖_{W^{k,2}} ≤ wkTopMultiplierNormBound n k ‖A‖_{W^{k,∞}} ‖U‖_{W^{k,2}}`, where the constant
is one at order zero. -/
theorem norm_mul_wk_le (k : ℕ) (A : W^{k,∞}(ℝ^n)) (U : W^{k,2}(ℝ^n)) :
    ‖wkMultiplication k A U‖ ≤ wkTopMultiplierNormBound n k * ‖A‖ * ‖U‖ := by
  cases k with
  | zero =>
    change ‖lpEquivZeroOrder ((ContinuousLinearMap.mul ℝ ℝ).holder 2 (wkpBaseCoordinateCLM A)
      (wkpBaseCoordinateCLM U))‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    calc
      _ ≤ ‖ContinuousLinearMap.mul ℝ ℝ‖ * ‖wkpBaseCoordinateCLM A‖ *
          ‖wkpBaseCoordinateCLM U‖ :=
        (ContinuousLinearMap.mul ℝ ℝ).norm_holder_apply_apply_le _ _
      _ ≤ 1 * ‖A‖ * ‖U‖ := by
        gcongr
        · exact ContinuousLinearMap.opNorm_mul_le ℝ ℝ
        · exact wkpBaseCoordinateCLM_norm_le A
        · exact wkpBaseCoordinateCLM_norm_le U
      _ = _ := by simp [wkTopMultiplierNormBound]
  | succ k => exact norm_wkTopMultiplicationCLM_apply_le (Nat.succ_pos k) isOpen_univ A U

section OperatorNorm

variable {k : ℕ}

/-- The normed group structure on bounded endomorphisms of `W^{k,2}(ℝ^n)`, named locally to
stabilize typeclass search. -/
local instance wholeSpaceEndomorphismNormedAddCommGroup :
    NormedAddCommGroup (W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n)) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- The real normed space structure on bounded endomorphisms of `W^{k,2}(ℝ^n)`. -/
local instance wholeSpaceEndomorphismNormedSpace :
    NormedSpace ℝ (W^{k,2}(ℝ^n) →L[ℝ] W^{k,2}(ℝ^n)) :=
  ContinuousLinearMap.toNormedSpace

/-- The operator norm of the bilinear multiplier is at most `wkTopMultiplierNormBound n k`. -/
theorem norm_wkMultiplication_le :
    ‖wkMultiplication (n := n) k‖ ≤ wkTopMultiplierNormBound n k :=
  ContinuousLinearMap.opNorm_le_bound₂ _ (wkTopMultiplierNormBound_nonneg n k)
    (norm_mul_wk_le k)

end OperatorNorm

/-- Lowering the order commutes with multiplication. -/
theorem lowerOrderCLM_wkMultiplication {r k : ℕ} (hrk : r ≤ k) (A : W^{k,∞}(ℝ^n))
    (U : W^{k,2}(ℝ^n)) :
    lowerOrderCLM hrk (wkMultiplication k A U) =
      wkMultiplication r (lowerOrderCLM hrk A) (lowerOrderCLM hrk U) := by
  apply WkpSpaceOn.ext_of_base_ae isOpen_univ
  change baseRepresentative (lowerOrderCLM hrk (wkMultiplication k A U)) =ᵐ[_]
    baseRepresentative (wkMultiplication r (lowerOrderCLM hrk A) (lowerOrderCLM hrk U))
  have h := wkMultiplication_base_ae r (lowerOrderCLM hrk A) (lowerOrderCLM hrk U)
  rw [baseRepresentative_lowerOrderCLM, baseRepresentative_lowerOrderCLM] at h
  rw [baseRepresentative_lowerOrderCLM]
  exact ae_restrict_of_ae ((wkMultiplication_base_ae k A U).trans h.symm)

/-- The weak Leibniz rule `∂ᵢ(A U) = A ∂ᵢU + (∂ᵢA) U` for whole-space Sobolev multipliers. -/
theorem partialDerivCLM_wkMultiplication (k : ℕ) (i : Fin n) (A : W^{k + 1,∞}(ℝ^n))
    (U : W^{k + 1,2}(ℝ^n)) :
    partialDerivCLM i (wkMultiplication (k + 1) A U) =
      wkMultiplication k (lowerOrderCLM (Nat.le_succ k) A) (partialDerivCLM i U) +
        wkMultiplication k (partialDerivCLM i A) (lowerOrderCLM (Nat.le_succ k) U) := by
  apply WkpSpaceOn.ext_of_base_ae isOpen_univ
  change baseRepresentative (partialDerivCLM i (wkMultiplication (k + 1) A U)) =ᵐ[_]
    baseRepresentative (wkMultiplication k (lowerOrderCLM (Nat.le_succ k) A)
        (partialDerivCLM i U) +
      wkMultiplication k (partialDerivCLM i A) (lowerOrderCLM (Nat.le_succ k) U))
  have hleft := wkTopProduct_firstDeriv_apply_ae (n := n) (Ω := Set.univ) (Nat.succ_pos k)
    isOpen_univ A U i
  have h1 := wkMultiplication_base_ae k (lowerOrderCLM (Nat.le_succ k) A) (partialDerivCLM i U)
  have h2 := wkMultiplication_base_ae k (partialDerivCLM i A) (lowerOrderCLM (Nat.le_succ k) U)
  rw [baseRepresentative_lowerOrderCLM, baseRepresentative_partialDerivCLM] at h1
  rw [baseRepresentative_lowerOrderCLM, baseRepresentative_partialDerivCLM] at h2
  rw [baseRepresentative_partialDerivCLM]
  filter_upwards [hleft, ae_restrict_of_ae (s := Set.univ) h1,
    ae_restrict_of_ae (s := Set.univ) h2,
    baseRepresentative_add_ae
      (wkMultiplication k (lowerOrderCLM (Nat.le_succ k) A) (partialDerivCLM i U))
      (wkMultiplication k (partialDerivCLM i A) (lowerOrderCLM (Nat.le_succ k) U))]
    with x hx hx1 hx2 hsum
  rw [hsum, hx1, hx2]
  exact hx

end SobolevSpace.GraphSpace
