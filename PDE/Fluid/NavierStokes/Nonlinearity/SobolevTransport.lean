/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonlinearity.BoundedTransport
public import PDE.Spaces.Sobolev.Calculus.Product.WholeSpaceMultiplier
public import PDE.Spaces.Sobolev.Evolution.VectorL2Triple
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Transport with Sobolev coefficients on whole-space vector fields

For coefficients `b : Fin n → W^{k,∞}(ℝ^n)` and `c : Fin n → Fin n → W^{k,∞}(ℝ^n)`, the
first-order operator

`(linearTransport k b c v)ⱼ = ∑ᵢ (bᵢ ∂ᵢvⱼ + cⱼᵢ vᵢ)`

is bounded from vector `H^{k+1}(ℝ^n)` to vector `H^k(ℝ^n)`, with norm at most
`wkTopMultiplierNormBound n k * ∑ⱼ ∑ᵢ (‖bᵢ‖ + ‖cⱼᵢ‖)`. It is the sum of the bounded bilinear maps
`velocityTransportCLM` and `stretchingCLM` of the coefficients and the field. At order zero it is
`BoundedTransport.transport` with the base coordinates of the coefficients, and lowering the
order of the output lowers the order of the coefficients and of the input.

## Main results

* `linearTransport`, with `linearTransport_apply`, `linearTransport_base_ae`,
  `norm_linearTransport_le`, `linearTransport_zero`, `vectorLowerOrderCLM_linearTransport` and
  `vectorLowerOrderCLM_zero_linearTransport`.
* `assembleComponents`: vector-valued bilinear maps from their components.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open scoped ENNReal Sobolev

namespace NavierStokes.SobolevConvection

variable {n : ℕ}

/-! ### Assembling vector fields from components -/

/-- The `j`-th component inclusion of scalar fields into whole-space vector fields. -/
def componentInclusion (k : ℕ) (j : Fin n) : W^{k,2}(ℝ^n) →L[ℝ] VectorH n k :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ W^{k,2}(ℝ^n))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin n ↦ W^{k,2}(ℝ^n)) j)

/-- Assemble a family of bilinear component maps into a bilinear map with vector values. -/
def assembleComponents {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ)
    (B : Fin n → E →L[ℝ] F →L[ℝ] W^{k,2}(ℝ^n)) : E →L[ℝ] F →L[ℝ] VectorH n k :=
  ∑ j : Fin n, (ContinuousLinearMap.compL ℝ F (W^{k,2}(ℝ^n)) (VectorH n k)
    (componentInclusion k j)).comp (B j)

/-- The components of an assembled map are the given component maps. -/
@[simp]
theorem assembleComponents_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ)
    (B : Fin n → E →L[ℝ] F →L[ℝ] W^{k,2}(ℝ^n)) (e : E) (f : F) (j : Fin n) :
    assembleComponents k B e f j = B j e f := by
  simp [assembleComponents, componentInclusion, ContinuousLinearMap.compL_apply,
    Pi.single_apply]

/-! ### Transport with Sobolev coefficients -/

/-- Component `j` of the convective term `∑ᵢ bᵢ ∂ᵢvⱼ`, bilinear in the velocity `b` and the
field `v`. -/
def scalarVelocityTransport (k : ℕ) (j : Fin n) :
    (Fin n → W^{k,∞}(ℝ^n)) →L[ℝ] VectorH n (k + 1) →L[ℝ] W^{k,2}(ℝ^n) :=
  ∑ i : Fin n, (wkMultiplication k).bilinearComp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ W^{k,∞}(ℝ^n)) i)
    ((partialDerivCLM i).comp (PiLp.proj 2 (fun _ : Fin n ↦ W^{k + 1,2}(ℝ^n)) j))

/-- Component `j` of the zero-order term `∑ᵢ cⱼᵢ vᵢ`, bilinear in the matrix `c` and the
field `v`. -/
def scalarStretching (k : ℕ) (j : Fin n) :
    (Fin n → Fin n → W^{k,∞}(ℝ^n)) →L[ℝ] VectorH n (k + 1) →L[ℝ] W^{k,2}(ℝ^n) :=
  ∑ i : Fin n, (wkMultiplication k).bilinearComp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ W^{k,∞}(ℝ^n)) i).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → W^{k,∞}(ℝ^n)) j))
    ((lowerOrderCLM (Nat.le_succ k)).comp (PiLp.proj 2 (fun _ : Fin n ↦ W^{k + 1,2}(ℝ^n)) i))

/-- The convective term `v ↦ (b·∇)v` as a bounded bilinear map of the velocity and the field. -/
def velocityTransportCLM (k : ℕ) :
    (Fin n → W^{k,∞}(ℝ^n)) →L[ℝ] VectorH n (k + 1) →L[ℝ] VectorH n k :=
  assembleComponents (E := Fin n → W^{k,∞}(ℝ^n)) (F := VectorH n (k + 1)) k
    (scalarVelocityTransport k)

/-- The zero-order term `v ↦ c v` as a bounded bilinear map of the matrix and the field. -/
def stretchingCLM (k : ℕ) :
    (Fin n → Fin n → W^{k,∞}(ℝ^n)) →L[ℝ] VectorH n (k + 1) →L[ℝ] VectorH n k :=
  assembleComponents (E := Fin n → Fin n → W^{k,∞}(ℝ^n)) (F := VectorH n (k + 1)) k
    (scalarStretching k)

/-- The transport `v ↦ (b·∇)v + c v` with coefficients in `W^{k,∞}(ℝ^n)`, from vector
`H^{k+1}(ℝ^n)` to vector `H^k(ℝ^n)`. -/
def linearTransport (k : ℕ) (b : Fin n → W^{k,∞}(ℝ^n)) (c : Fin n → Fin n → W^{k,∞}(ℝ^n)) :
    VectorH n (k + 1) →L[ℝ] VectorH n k :=
  velocityTransportCLM k b + stretchingCLM k c

/-- The components of the transport are `∑ᵢ (bᵢ ∂ᵢvⱼ + cⱼᵢ vᵢ)`. -/
theorem linearTransport_apply (k : ℕ) (b : Fin n → W^{k,∞}(ℝ^n))
    (c : Fin n → Fin n → W^{k,∞}(ℝ^n)) (v : VectorH n (k + 1)) (j : Fin n) :
    linearTransport k b c v j = ∑ i : Fin n,
      (wkMultiplication k (b i) (partialDerivCLM i (v j)) +
        wkMultiplication k (c j i) (lowerOrderCLM (Nat.le_succ k) (v i))) := by
  simp [linearTransport, velocityTransportCLM, stretchingCLM, scalarVelocityTransport,
    scalarStretching, sum_apply, Finset.sum_add_distrib]

/-- The base representative of each component is `∑ᵢ (bᵢ ∂ᵢvⱼ + cⱼᵢ vᵢ)` almost everywhere. -/
theorem linearTransport_base_ae (k : ℕ) (b : Fin n → W^{k,∞}(ℝ^n))
    (c : Fin n → Fin n → W^{k,∞}(ℝ^n)) (v : VectorH n (k + 1)) (j : Fin n) :
    baseRepresentative (linearTransport k b c v j) =ᵐ[volume] fun x ↦ ∑ i : Fin n,
      (baseRepresentative (b i) x * baseRepresentative (partialDerivCLM i (v j)) x +
        baseRepresentative (c j i) x * baseRepresentative (v i) x) := by
  rw [linearTransport_apply]
  have hs := baseRepresentative_sum_ae (fun i : Fin n ↦
    wkMultiplication k (b i) (partialDerivCLM i (v j)) +
      wkMultiplication k (c j i) (lowerOrderCLM (Nat.le_succ k) (v i)))
  have hadd := fun i : Fin n ↦ baseRepresentative_add_ae
    (wkMultiplication k (b i) (partialDerivCLM i (v j)))
    (wkMultiplication k (c j i) (lowerOrderCLM (Nat.le_succ k) (v i)))
  simp only [domainMeasure, Measure.restrict_univ] at hs hadd
  filter_upwards [hs, ae_all_iff.mpr hadd,
    ae_all_iff.mpr (fun i : Fin n ↦ wkMultiplication_base_ae k (b i) (partialDerivCLM i (v j))),
    ae_all_iff.mpr (fun i : Fin n ↦
      wkMultiplication_base_ae k (c j i) (lowerOrderCLM (Nat.le_succ k) (v i)))]
    with x hsum hplus hb hc
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hplus i, hb i, hc i, baseRepresentative_lowerOrderCLM]

/-- The sum of all coefficient norms, which bounds the transport. -/
def transportCoefficientBound (k : ℕ) (b : Fin n → W^{k,∞}(ℝ^n))
    (c : Fin n → Fin n → W^{k,∞}(ℝ^n)) : ℝ :=
  ∑ j : Fin n, ∑ i : Fin n, (‖b i‖ + ‖c j i‖)

theorem transportCoefficientBound_nonneg (k : ℕ) (b : Fin n → W^{k,∞}(ℝ^n))
    (c : Fin n → Fin n → W^{k,∞}(ℝ^n)) : 0 ≤ transportCoefficientBound k b c :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ by positivity

/-- Pointwise transport bound with the multiplier constant and the coefficient norms. -/
theorem norm_linearTransport_apply_le (k : ℕ) (b : Fin n → W^{k,∞}(ℝ^n))
    (c : Fin n → Fin n → W^{k,∞}(ℝ^n)) (v : VectorH n (k + 1)) :
    ‖linearTransport k b c v‖ ≤
      wkTopMultiplierNormBound n k * transportCoefficientBound k b c * ‖v‖ := by
  have hC := wkTopMultiplierNormBound_nonneg n k
  apply (PiLp.norm_le_sum_norm _).trans
  unfold transportCoefficientBound
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  rw [linearTransport_apply, Finset.mul_sum, Finset.sum_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ ‖wkMultiplication k (b i) (partialDerivCLM i (v j))‖ +
        ‖wkMultiplication k (c j i) (lowerOrderCLM (Nat.le_succ k) (v i))‖ := norm_add_le _ _
    _ ≤ wkTopMultiplierNormBound n k * ‖b i‖ * ‖v‖ +
        wkTopMultiplierNormBound n k * ‖c j i‖ * ‖v‖ := by
      apply add_le_add
      · exact (norm_mul_wk_le k _ _).trans (mul_le_mul_of_nonneg_left
          ((norm_partialDeriv_le i (v j)).trans (PiLp.norm_apply_le v j))
          (mul_nonneg hC (norm_nonneg _)))
      · exact (norm_mul_wk_le k _ _).trans (mul_le_mul_of_nonneg_left
          ((norm_lowerOrderCLM_apply_le _ (v i)).trans (PiLp.norm_apply_le v i))
          (mul_nonneg hC (norm_nonneg _)))
    _ = _ := by ring

/-- Operator-norm transport bound:
`‖linearTransport k b c‖ ≤ wkTopMultiplierNormBound n k ∑ⱼ ∑ᵢ (‖bᵢ‖ + ‖cⱼᵢ‖)`. -/
theorem norm_linearTransport_le (k : ℕ) (b : Fin n → W^{k,∞}(ℝ^n))
    (c : Fin n → Fin n → W^{k,∞}(ℝ^n)) :
    ‖linearTransport k b c‖ ≤ wkTopMultiplierNormBound n k * transportCoefficientBound k b c :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (wkTopMultiplierNormBound_nonneg n k) (transportCoefficientBound_nonneg k b c))
    (norm_linearTransport_apply_le k b c)

/-- At order zero, the transport is `BoundedTransport.transport` with the base coordinates of the
coefficients. -/
theorem linearTransport_zero (b : Fin n → W^{0,∞}(ℝ^n))
    (c : Fin n → Fin n → W^{0,∞}(ℝ^n)) :
    linearTransport 0 b c = BoundedTransport.transport (fun i ↦ wkpBaseCoordinateCLM (b i))
      (fun j i ↦ wkpBaseCoordinateCLM (c j i)) := by
  ext1 v
  apply PiLp.ext
  intro j
  apply (lpEquivZeroOrder (n := n) (p := 2) (Ω := Set.univ)).symm.injective
  change wkpBaseCoordinateCLM (linearTransport 0 b c v j) =
    wkpBaseCoordinateCLM (BoundedTransport.transport _ _ v j)
  rw [BoundedTransport.transport_base, BoundedTransport.scalarTransport_apply,
    linearTransport_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_add, wkpBaseCoordinateCLM_wkMultiplication, wkpBaseCoordinateCLM_wkMultiplication,
    wkpBaseCoordinateCLM_partialDerivCLM]
  rfl

/-- Lowering the order of the output lowers the order of the coefficients and of the input. -/
theorem vectorLowerOrderCLM_linearTransport {r k : ℕ} (hrk : r ≤ k)
    (b : Fin n → W^{k,∞}(ℝ^n)) (c : Fin n → Fin n → W^{k,∞}(ℝ^n)) (v : VectorH n (k + 1)) :
    vectorLowerOrderCLM hrk (linearTransport k b c v) =
      linearTransport r (fun i ↦ lowerOrderCLM hrk (b i))
        (fun j i ↦ lowerOrderCLM hrk (c j i))
        (vectorLowerOrderCLM (Nat.succ_le_succ hrk) v) := by
  apply PiLp.ext
  intro j
  rw [vectorLowerOrderCLM_apply, linearTransport_apply, linearTransport_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_add, lowerOrderCLM_wkMultiplication, lowerOrderCLM_wkMultiplication,
    lowerOrderCLM_partialDerivCLM, vectorLowerOrderCLM_apply, vectorLowerOrderCLM_apply,
    lowerOrderCLM_trans_apply, lowerOrderCLM_trans_apply]

/-- The order-zero part of the transport is `BoundedTransport.transport` with the base
coordinates of the coefficients, applied to the order-one part of the input. -/
theorem vectorLowerOrderCLM_zero_linearTransport (k : ℕ) (b : Fin n → W^{k,∞}(ℝ^n))
    (c : Fin n → Fin n → W^{k,∞}(ℝ^n)) (v : VectorH n (k + 1)) :
    vectorLowerOrderCLM (Nat.zero_le k) (linearTransport k b c v) =
      BoundedTransport.transport (fun i ↦ wkpBaseCoordinateCLM (b i))
        (fun j i ↦ wkpBaseCoordinateCLM (c j i))
        (vectorLowerOrderCLM (Nat.succ_le_succ (Nat.zero_le k)) v) := by
  rw [vectorLowerOrderCLM_linearTransport, linearTransport_zero]
  rfl

end NavierStokes.SobolevConvection
