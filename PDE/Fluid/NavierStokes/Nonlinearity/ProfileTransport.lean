/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.Nonlinearity.SobolevTransport
public import PDE.Spaces.Sobolev.Approximation.Density.SmoothFields
import PDE.Fluid.Incompressible.LerayProjection.OrderLowering

/-!
# Linearized convection around a profile in whole-space Sobolev spaces

For a profile `U : Fin n → W^{k+1,∞}(ℝ^n)`, the linearization of the convection term at `U` is

`profileTransport k U v = -Π(U·∇v + v·∇U)`,

from vector `H^{k+1}(ℝ^n)` to vector `H^k(ℝ^n)`, where `Π` is the whole-space Leray projection
`leraySobolev` and `U·∇v + v·∇U` is `linearTransport` with the coefficients `bᵢ = Uᵢ` and
`cⱼᵢ = ∂ᵢUⱼ`. It is a bounded bilinear map of the profile and the field, so it depends linearly
and continuously on `U` in the operator norm, with
`‖profileTransport k U‖ ≤ 2 n² wkTopMultiplierNormBound n k ‖U‖`.
Its values are solenoidal, its order-zero part is `-BoundedTransport.projectedTransport` with the
base coordinates of `U` and `∇U`, and lowering the order of the output lowers the order of the
profile and of the input.

## Main results

* `profileTransport`, with `profileTransport_apply` and `profileTransport_base_ae`.
* `norm_profileTransport_le`, `norm_profileTransport_sub_le`, `continuous_profileTransport`.
* `profileTransport_zero`, `vectorLowerOrderCLM_profileTransport`,
  `vectorLowerOrderCLM_zero_profileTransport`.
* `profileTransport_base_mem_solenoidal`, `leraySobolev_profileTransport`.
* `profileConvection_vectorWkpOfContDiff_base_ae`: for a smooth profile with bounded
  derivatives, the classical expression of the unprojected convection.
-/

@[expose] public noncomputable section

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open scoped ENNReal Sobolev

namespace NavierStokes.SobolevConvection

variable {n : ℕ}

/-! ### The linearization around a profile -/

/-- The velocity coefficient `bᵢ = Uᵢ` of the linearized convection at a profile `U`. -/
def profileVelocity (k : ℕ) :
    (Fin n → W^{k + 1,∞}(ℝ^n)) →L[ℝ] (Fin n → W^{k,∞}(ℝ^n)) :=
  ContinuousLinearMap.pi (φ := fun _ : Fin n ↦ W^{k,∞}(ℝ^n)) fun i ↦
    (lowerOrderCLM (Nat.le_succ k)).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ W^{k + 1,∞}(ℝ^n)) i)

/-- The matrix coefficient `cⱼᵢ = ∂ᵢUⱼ` of the linearized convection at a profile `U`. -/
def profileGradient (k : ℕ) :
    (Fin n → W^{k + 1,∞}(ℝ^n)) →L[ℝ] (Fin n → Fin n → W^{k,∞}(ℝ^n)) :=
  ContinuousLinearMap.pi (φ := fun _ : Fin n ↦ Fin n → W^{k,∞}(ℝ^n)) fun j ↦
    ContinuousLinearMap.pi (φ := fun _ : Fin n ↦ W^{k,∞}(ℝ^n)) fun i ↦
      (partialDerivCLM i).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ W^{k + 1,∞}(ℝ^n)) j)

/-- The unprojected linearized convection `v ↦ U·∇v + v·∇U` at a profile `U`. -/
def profileConvection (k : ℕ) (U : Fin n → W^{k + 1,∞}(ℝ^n)) :
    VectorH n (k + 1) →L[ℝ] VectorH n k :=
  linearTransport k (fun i ↦ lowerOrderCLM (Nat.le_succ k) (U i))
    (fun j i ↦ partialDerivCLM i (U j))

/-- The projected linearized convection as a bounded bilinear map of the profile and the
field. -/
def profileTransportCLM (k : ℕ) :
    (Fin n → W^{k + 1,∞}(ℝ^n)) →L[ℝ] VectorH n (k + 1) →L[ℝ] VectorH n k :=
  -((ContinuousLinearMap.compL ℝ (VectorH n (k + 1)) (VectorH n k) (VectorH n k)
    (leraySobolev n k)).comp ((velocityTransportCLM k).comp (profileVelocity k) +
      (stretchingCLM k).comp (profileGradient k)))

/-- The linearization `v ↦ -Π(U·∇v + v·∇U)` of the convection term at a profile
`U : Fin n → W^{k+1,∞}(ℝ^n)`, from vector `H^{k+1}(ℝ^n)` to vector `H^k(ℝ^n)`. -/
def profileTransport (k : ℕ) (U : Fin n → W^{k + 1,∞}(ℝ^n)) :
    VectorH n (k + 1) →L[ℝ] VectorH n k :=
  profileTransportCLM k U

/-- The projected transport is minus the Leray projection of the unprojected one. -/
theorem profileTransport_apply (k : ℕ) (U : Fin n → W^{k + 1,∞}(ℝ^n))
    (v : VectorH n (k + 1)) :
    profileTransport k U v = -leraySobolev n k (profileConvection k U v) :=
  rfl

/-- The components of the unprojected convection are `∑ᵢ (Uᵢ ∂ᵢvⱼ + ∂ᵢUⱼ vᵢ)` almost
everywhere. -/
theorem profileConvection_base_ae (k : ℕ) (U : Fin n → W^{k + 1,∞}(ℝ^n))
    (v : VectorH n (k + 1)) (j : Fin n) :
    baseRepresentative (profileConvection k U v j) =ᵐ[volume] fun x ↦ ∑ i : Fin n,
      (baseRepresentative (U i) x * baseRepresentative (partialDerivCLM i (v j)) x +
        baseRepresentative (partialDerivCLM i (U j)) x * baseRepresentative (v i) x) := by
  simpa only [profileConvection, baseRepresentative_lowerOrderCLM] using
    linearTransport_base_ae k (fun i ↦ lowerOrderCLM (Nat.le_succ k) (U i))
      (fun j i ↦ partialDerivCLM i (U j)) v j

/-- The base row of the projected transport is minus the Leray projection of an `L²` field whose
components are `∑ᵢ (Uᵢ ∂ᵢvⱼ + ∂ᵢUⱼ vᵢ)` almost everywhere. The Leray projection is nonlocal, so
the projected row is described through the unprojected convection rather than by a pointwise
formula. -/
theorem profileTransport_base_ae (k : ℕ) (U : Fin n → W^{k + 1,∞}(ℝ^n))
    (v : VectorH n (k + 1)) :
    l2SobolevRow (baseIndex n k) (profileTransport k U v) =
        -lerayProjection n (l2SobolevRow (baseIndex n k) (profileConvection k U v)) ∧
      ∀ j : Fin n, baseRepresentative (profileConvection k U v j) =ᵐ[volume] fun x ↦
        ∑ i : Fin n,
          (baseRepresentative (U i) x * baseRepresentative (partialDerivCLM i (v j)) x +
            baseRepresentative (partialDerivCLM i (U j)) x * baseRepresentative (v i) x) := by
  refine ⟨?_, profileConvection_base_ae k U v⟩
  rw [profileTransport_apply, map_neg, l2SobolevRow_leraySobolev]

/-- The projected transport takes values in solenoidal fields. -/
theorem profileTransport_base_mem_solenoidal (k : ℕ) (U : Fin n → W^{k + 1,∞}(ℝ^n))
    (v : VectorH n (k + 1)) :
    l2SobolevRow (baseIndex n k) (profileTransport k U v) ∈ l2Solenoidal n := by
  rw [(profileTransport_base_ae k U v).1]
  exact Submodule.neg_mem _ (lerayProjection_mem n _)

/-- The Leray projection leaves the projected transport unchanged. -/
theorem leraySobolev_profileTransport (k : ℕ) (U : Fin n → W^{k + 1,∞}(ℝ^n))
    (v : VectorH n (k + 1)) :
    leraySobolev n k (profileTransport k U v) = profileTransport k U v := by
  rw [profileTransport_apply, map_neg, leraySobolev_idempotent]

/-- The constant `2 n² wkTopMultiplierNormBound n k` in the bound of the projected transport by
the profile norm. -/
def profileTransportBound (n k : ℕ) : ℝ :=
  2 * (n : ℝ) ^ 2 * wkTopMultiplierNormBound n k

theorem profileTransportBound_nonneg (n k : ℕ) : 0 ≤ profileTransportBound n k :=
  mul_nonneg (by positivity) (wkTopMultiplierNormBound_nonneg n k)

/-- The coefficient bound of the profile coefficients is at most `2 n² ‖U‖`. -/
theorem transportCoefficientBound_profile_le (k : ℕ) (U : Fin n → W^{k + 1,∞}(ℝ^n)) :
    transportCoefficientBound k (fun i ↦ lowerOrderCLM (Nat.le_succ k) (U i))
        (fun j i ↦ partialDerivCLM i (U j)) ≤ 2 * (n : ℝ) ^ 2 * ‖U‖ := by
  unfold transportCoefficientBound
  calc
    _ ≤ ∑ _j : Fin n, ∑ _i : Fin n, (‖U‖ + ‖U‖) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro i _
      exact add_le_add ((norm_lowerOrderCLM_apply_le _ (U i)).trans (norm_le_pi_norm U i))
        ((norm_partialDeriv_le i (U j)).trans (norm_le_pi_norm U j))
    _ = _ := by simp; ring

/-- Pointwise bound of the projected transport by the profile norm. -/
theorem norm_profileTransport_apply_le (k : ℕ) (U : Fin n → W^{k + 1,∞}(ℝ^n))
    (v : VectorH n (k + 1)) :
    ‖profileTransport k U v‖ ≤ profileTransportBound n k * ‖U‖ * ‖v‖ := by
  rw [profileTransport_apply, norm_neg]
  apply (norm_leraySobolev_le _).trans
  apply (norm_linearTransport_apply_le k _ _ v).trans
  unfold profileTransportBound
  have hC := wkTopMultiplierNormBound_nonneg n k
  calc
    _ ≤ wkTopMultiplierNormBound n k * (2 * (n : ℝ) ^ 2 * ‖U‖) * ‖v‖ := by
      gcongr
      exact transportCoefficientBound_profile_le k U
    _ = _ := by ring

/-- Operator-norm bound
`‖profileTransport k U‖ ≤ 2 n² wkTopMultiplierNormBound n k ‖U‖_{W^{k+1,∞}}`. -/
theorem norm_profileTransport_le (k : ℕ) (U : Fin n → W^{k + 1,∞}(ℝ^n)) :
    ‖profileTransport k U‖ ≤ profileTransportBound n k * ‖U‖ :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (profileTransportBound_nonneg n k) (norm_nonneg U))
    (norm_profileTransport_apply_le k U)

/-- The projected transport is linear in the profile. -/
theorem profileTransport_sub (k : ℕ) (U V : Fin n → W^{k + 1,∞}(ℝ^n)) :
    profileTransport k (U - V) = profileTransport k U - profileTransport k V :=
  map_sub (profileTransportCLM k) U V

/-- The projected transport is Lipschitz in the profile for the operator norm. -/
theorem norm_profileTransport_sub_le (k : ℕ) (U V : Fin n → W^{k + 1,∞}(ℝ^n)) :
    ‖profileTransport k U - profileTransport k V‖ ≤ profileTransportBound n k * ‖U - V‖ := by
  rw [← profileTransport_sub]
  exact norm_profileTransport_le k (U - V)

/-- The projected transport depends continuously on the profile in the operator norm. -/
theorem continuous_profileTransport (k : ℕ) :
    Continuous (profileTransport (n := n) k) :=
  (profileTransportCLM k).continuous

/-- At order zero, the projected transport is `-BoundedTransport.projectedTransport` with the base
coordinates of `U` and `∇U`. -/
theorem profileTransport_zero (U : Fin n → W^{1,∞}(ℝ^n)) :
    profileTransport 0 U = -BoundedTransport.projectedTransport
      (fun i ↦ wkpBaseCoordinateCLM (U i))
      (fun j i ↦ wkpBaseCoordinateCLM (partialDerivCLM i (U j))) := by
  ext1 v
  rw [profileTransport_apply, profileConvection, linearTransport_zero]
  rfl

/-- Lowering the order of the projected transport lowers the order of the profile and of the
input. -/
theorem vectorLowerOrderCLM_profileTransport {r k : ℕ} (hrk : r ≤ k)
    (U : Fin n → W^{k + 1,∞}(ℝ^n)) (v : VectorH n (k + 1)) :
    vectorLowerOrderCLM hrk (profileTransport k U v) =
      profileTransport r (fun i ↦ lowerOrderCLM (Nat.succ_le_succ hrk) (U i))
        (vectorLowerOrderCLM (Nat.succ_le_succ hrk) v) := by
  rw [profileTransport_apply, profileTransport_apply, map_neg, vectorLowerOrderCLM_leraySobolev,
    profileConvection, profileConvection, vectorLowerOrderCLM_linearTransport]
  congr 4

/-- The order-zero part of the projected transport is `-BoundedTransport.projectedTransport` with
the base coordinates of `U` and `∇U`, applied to the order-one part of the input. -/
theorem vectorLowerOrderCLM_zero_profileTransport (k : ℕ) (U : Fin n → W^{k + 1,∞}(ℝ^n))
    (v : VectorH n (k + 1)) :
    vectorLowerOrderCLM (Nat.zero_le k) (profileTransport k U v) =
      -BoundedTransport.projectedTransport (fun i ↦ wkpBaseCoordinateCLM (U i))
        (fun j i ↦ wkpBaseCoordinateCLM (partialDerivCLM i (U j)))
        (vectorLowerOrderCLM (Nat.succ_le_succ (Nat.zero_le k)) v) := by
  rw [vectorLowerOrderCLM_profileTransport, profileTransport_zero]
  congr 3

/-- For a smooth profile with bounded derivatives, the components of the unprojected convection
are `∑ᵢ (Uᵢ ∂ᵢvⱼ + (∂ᵢU)ⱼ vᵢ)` almost everywhere, with the classical values and partial
derivatives of `U`. -/
theorem profileConvection_vectorWkpOfContDiff_base_ae (k : ℕ) (U : ℝ^n → ℝ^n)
    (hU : ContDiff ℝ (⊤ : ℕ∞) U)
    (hmem : ∀ m ≤ k + 1, MemLp (iteratedFDeriv ℝ m U) ⊤ volume)
    (v : VectorH n (k + 1)) (j : Fin n) :
    baseRepresentative (profileConvection k (vectorWkpOfContDiff U hU hmem) v j) =ᵐ[volume]
      fun x ↦ ∑ i : Fin n, (U x i * baseRepresentative (partialDerivCLM i (v j)) x +
        fderiv ℝ U x (EuclideanSpace.single i 1) j * baseRepresentative (v i) x) := by
  filter_upwards [profileConvection_base_ae k (vectorWkpOfContDiff U hU hmem) v j,
    ae_all_iff.mpr (fun i ↦ baseRepresentative_vectorWkpOfContDiff U hU hmem i),
    ae_all_iff.mpr (fun i ↦ baseRepresentative_partialDerivCLM_vectorWkpOfContDiff U hU hmem j i)]
    with x hx hU0 hU1
  rw [hx]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [hU0 i, hU1 i]

end NavierStokes.SobolevConvection
