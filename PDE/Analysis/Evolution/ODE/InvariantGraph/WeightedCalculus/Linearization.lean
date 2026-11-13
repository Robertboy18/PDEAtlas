/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedCalculus.Bilinear
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# The derivative along a weighted path

For a continuously differentiable Lipschitz map, the derivative along a
path is a bounded continuous operator-valued function. Pointwise application
acts on variations in every exponential weight with the original Lipschitz
bound.
-/

@[expose] public noncomputable section

open NNReal

namespace BoundedContinuousFunction

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {L : ℝ≥0} {N : E → F}

/-- The Fréchet derivative along a represented path, bounded by the
Lipschitz constant of the original map. -/
def exponentialDerivativeCoefficients (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N)
    (η : ℝ) (u : ℝ →ᵇ E) : ℝ →ᵇ (E →L[ℝ] F) :=
  ofNormedAddCommGroup (fun t ↦ fderiv ℝ N (exponentialLift η u t))
    ((hN1.continuous_fderiv one_ne_zero).comp (exponentialLift η u).continuous) L
    fun _ ↦ norm_fderiv_le_of_lipschitz ℝ hN

/-- The coefficient at each time is the derivative at the path value. -/
@[simp] theorem exponentialDerivativeCoefficients_apply
    (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N) (η : ℝ) (u : ℝ →ᵇ E) (t : ℝ) :
    exponentialDerivativeCoefficients hN hN1 η u t = fderiv ℝ N (exponentialLift η u t) := rfl

/-- The operator-valued coefficient has a uniform bound independent of the base path. -/
theorem norm_exponentialDerivativeCoefficients_le
    (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N) (η : ℝ) (u : ℝ →ᵇ E) :
    ‖exponentialDerivativeCoefficients hN hN1 η u‖ ≤ L := by
  apply (norm_le L.coe_nonneg).mpr
  intro t
  exact norm_fderiv_le_of_lipschitz ℝ hN

/-- Pointwise linearization about a path. Its argument may represent a
variation in any exponential weight. -/
def linearizedExponentialComposition
    (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N) (η : ℝ) (u : ℝ →ᵇ E) :
    (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ F) :=
  (ContinuousLinearMap.id ℝ (E →L[ℝ] F)).compLeftContinuousBounded₂ ℝ
    (exponentialDerivativeCoefficients hN hN1 η u)

/-- Evaluation of the linearized operator is the derivative applied to
the represented variation. -/
@[simp] theorem linearizedExponentialComposition_apply
    (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N) (η : ℝ)
    (u v : ℝ →ᵇ E) (t : ℝ) :
    linearizedExponentialComposition hN hN1 η u v t =
      fderiv ℝ N (exponentialLift η u t) (v t) := rfl

/-- Linearization preserves every variation weight because the scalar weight
commutes with the linear derivative. -/
@[simp] theorem exponentialLift_linearizedExponentialComposition
    (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N) (η θ : ℝ)
    (u v : ℝ →ᵇ E) (t : ℝ) :
    exponentialLift θ (linearizedExponentialComposition hN hN1 η u v) t =
      fderiv ℝ N (exponentialLift η u t) (exponentialLift θ v t) :=
  ((fderiv ℝ N (exponentialLift η u t)).map_smul (Real.exp (θ * |t|)) (v t)).symm

/-- The linearization has norm at most the original nonlinear Lipschitz constant. -/
theorem norm_linearizedExponentialComposition_le
    (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N) (η : ℝ) (u : ℝ →ᵇ E) :
    ‖linearizedExponentialComposition hN hN1 η u‖ ≤ L := by
  apply ContinuousLinearMap.opNorm_le_bound _ L.coe_nonneg
  intro v
  apply (norm_le (mul_nonneg L.coe_nonneg (norm_nonneg v))).mpr
  intro t
  exact (fderiv ℝ N (exponentialLift η u t)).le_of_opNorm_le_of_le
    (norm_fderiv_le_of_lipschitz ℝ hN) (v.norm_coe_le_norm t)

/-- Weight changes for variations commute with the pointwise derivative. -/
theorem increaseExponentialWeight_linearizedExponentialComposition
    (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N) (η : ℝ)
    {α β : ℝ} (hαβ : α ≤ β) (u v : ℝ →ᵇ E) :
    increaseExponentialWeight hαβ (linearizedExponentialComposition hN hN1 η u v) =
      linearizedExponentialComposition hN hN1 η u (increaseExponentialWeight hαβ v) := by
  apply exponentialLift_injective β
  ext t
  simp only [exponentialLift_increaseExponentialWeight,
    exponentialLift_linearizedExponentialComposition]

/-- Re-encoding the same base path leaves its pointwise linearization unchanged. -/
theorem linearizedExponentialComposition_of_weight_change
    (hN : LipschitzWith L N) (hN1 : ContDiff ℝ 1 N)
    {η θ : ℝ} (hηθ : η ≤ θ) (u : ℝ →ᵇ E) :
    linearizedExponentialComposition hN hN1 θ (increaseExponentialWeight hηθ u) =
      linearizedExponentialComposition hN hN1 η u := by
  ext v t
  simp only [linearizedExponentialComposition_apply, exponentialLift_increaseExponentialWeight]

end BoundedContinuousFunction
