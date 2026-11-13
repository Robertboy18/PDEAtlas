/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.IntegralOperator
public import PDE.Analysis.Evolution.ODE.InvariantGraph.WeightedComposition
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Construction of whole-line weighted solution paths

For a bounded linear Green operator `G` on weighted paths and an `L`-Lipschitz
remainder `N` with `N 0 = 0`, the Lyapunov–Perron map `u ↦ z + G (N ∘ u)` is a
contraction of Mathlib's complete space of bounded continuous functions whenever
`‖G‖ L < 1`. Its fixed point `perronPath` is unique and depends Lipschitz
continuously on the homogeneous term `z`. For the finite diagonal Green operator and
a constant center seed `ξ`, the fixed path solves `x' = rate • x + N x` on the
whole line.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {L : ℝ≥0} {N : E → E} {η : ℝ}

/-- A constant path, encoded in a nonnegative exponential weight. -/
def centerSeed (hη : 0 ≤ η) (ξ : E) : ℝ →ᵇ E :=
  increaseExponentialWeight hη (const ℝ ξ)

/-- The homogeneous center seed decodes to its specified constant value. -/
@[simp] theorem exponentialLift_centerSeed (hη : 0 ≤ η) (ξ : E) (t : ℝ) :
    exponentialLift η (centerSeed hη ξ) t = ξ := by
  have h := exponentialLift_increaseExponentialWeight hη (const ℝ ξ)
  simpa [centerSeed, exponentialLift] using congrArg (fun f : C(ℝ, E) ↦ f t) h

/-- The weighted Lyapunov–Perron map with a specified homogeneous term. -/
def perronOperator (η : ℝ) (G : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (z : ℝ →ᵇ E) (u : ℝ →ᵇ E) :
    ℝ →ᵇ E :=
  z + G (composeExponentialWeight hN hN0 η u)

/-- The operator is contracting when the Green norm times the nonlinear
Lipschitz constant is strictly less than one. -/
theorem contractingWith_perronOperator (η : ℝ)
    (G : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E)) (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (hsmall : ‖G‖ * L < 1) (z : ℝ →ᵇ E) :
    ContractingWith (‖G‖₊ * L) (perronOperator η G hN hN0 z) := by
  refine ⟨by exact_mod_cast hsmall, LipschitzWith.of_dist_le_mul fun u v ↦ ?_⟩
  simpa only [perronOperator, dist_add_left, Function.comp_apply] using
    (G.lipschitzWith.comp (lipschitzWith_composeExponentialWeight hN hN0 η)).dist_le_mul u v

variable [CompleteSpace E]

/-- The weighted fixed path obtained from the contraction theorem. -/
def perronPath (η : ℝ) (G : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hsmall : ‖G‖ * L < 1) (z : ℝ →ᵇ E) :
    ℝ →ᵇ E :=
  (contractingWith_perronOperator η G hN hN0 hsmall z).fixedPoint
    (perronOperator η G hN hN0 z)

/-- The constructed path satisfies the nonlinear integral equation. -/
theorem perronPath_eq (η : ℝ) (G : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hsmall : ‖G‖ * L < 1) (z : ℝ →ᵇ E) :
    perronPath η G hN hN0 hsmall z =
      z + G (composeExponentialWeight hN hN0 η (perronPath η G hN hN0 hsmall z)) :=
  (contractingWith_perronOperator η G hN hN0 hsmall z).fixedPoint_isFixedPt.symm

/-- The integral equation holds for the decoded paths. -/
theorem exponentialLift_perronPath (η : ℝ) (G : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hsmall : ‖G‖ * L < 1)
    (z : ℝ →ᵇ E) (t : ℝ) :
    exponentialLift η (perronPath η G hN hN0 hsmall z) t =
      exponentialLift η z t +
        exponentialLift η
          (G (composeExponentialWeight hN hN0 η (perronPath η G hN hN0 hsmall z))) t := by
  conv_lhs => rw [perronPath_eq]
  exact smul_add _ _ _

/-- A fixed path is necessarily the path constructed by contraction. -/
theorem perronPath_unique (η : ℝ) (G : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hsmall : ‖G‖ * L < 1)
    (z u : ℝ →ᵇ E) (hu : u = z + G (composeExponentialWeight hN hN0 η u)) :
    u = perronPath η G hN hN0 hsmall z :=
  (contractingWith_perronOperator η G hN hN0 hsmall z).fixedPoint_unique hu.symm

/-- Dependence on the homogeneous term follows from the contraction estimate. -/
theorem dist_perronPath_le (η : ℝ) (G : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hsmall : ‖G‖ * L < 1) (z w : ℝ →ᵇ E) :
    dist (perronPath η G hN hN0 hsmall z) (perronPath η G hN hN0 hsmall w) ≤
      dist z w / (1 - ‖G‖ * L) := by
  apply (contractingWith_perronOperator η G hN hN0 hsmall z).fixedPoint_lipschitz_in_map
    (contractingWith_perronOperator η G hN hN0 hsmall w)
  intro u
  simp only [perronOperator, dist_add_right, le_refl]

/-- The zero homogeneous term produces the zero path. -/
@[simp] theorem perronPath_zero (η : ℝ) (G : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hN : LipschitzWith L N) (hN0 : N 0 = 0) (hsmall : ‖G‖ * L < 1) :
    perronPath η G hN hN0 hsmall 0 = 0 := by
  symm
  apply perronPath_unique
  have hz : composeExponentialWeight hN hN0 η (0 : ℝ →ᵇ E) = 0 := by
    ext t
    change Real.exp (-(η * |t|)) • N (Real.exp (η * |t|) • (0 : E)) = 0
    rw [smul_zero, hN0, smul_zero]
  rw [hz, map_zero, add_zero]

variable {ι : Type*} [Fintype ι] {N : (ι → ℝ) → (ι → ℝ)}

/-- Add constant center data to the Green solution. -/
theorem hasDerivAt_centerSeed_add_diagonalGreen (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|) (f : ℝ →ᵇ (ι → ℝ))
    (ξ : ι → ℝ) (hξ : ∀ i, rate i * ξ i = 0) (t : ℝ) :
    HasDerivAt (exponentialLift η (centerSeed hη.le ξ + diagonalGreen hη rate hgap f))
      (fun i ↦ rate i *
          exponentialLift η (centerSeed hη.le ξ + diagonalGreen hη rate hgap f) t i +
        exponentialLift η f t i) t := by
  let G := diagonalGreen hη rate hgap
  have heq : (fun s ↦ ξ + exponentialLift η (G f) s) =
      exponentialLift η (centerSeed hη.le ξ + G f) := by
    funext s
    change ξ + Real.exp (η * |s|) • G f s =
      Real.exp (η * |s|) • (centerSeed hη.le ξ s + G f s)
    rw [smul_add]
    exact congrArg (fun z ↦ z + Real.exp (η * |s|) • G f s)
      (exponentialLift_centerSeed hη.le ξ s).symm
  have hd := (hasDerivAt_exponentialLift_diagonalGreen hη rate hgap f t).const_add ξ
  change HasDerivAt (fun s ↦ ξ + exponentialLift η (G f) s) _ t at hd
  rw [heq] at hd
  apply hd.congr_deriv
  ext i
  have hu := congrArg (fun z : ι → ℝ ↦ z i) (congrFun heq t)
  change ξ i + exponentialLift η (G f) t i =
    exponentialLift η (centerSeed hη.le ξ + G f) t i at hu
  change rate i * exponentialLift η (G f) t i + exponentialLift η f t i =
    rate i * exponentialLift η (centerSeed hη.le ξ + G f) t i + exponentialLift η f t i
  rw [← hu, mul_add, hξ i, zero_add]

/-- For center data, the constructed path satisfies the nonlinear
diagonal ODE at every real time. -/
theorem hasDerivAt_perronPath (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (hsmall : ‖diagonalGreen hη rate hgap‖ * L < 1)
    (ξ : ι → ℝ) (hξ : ∀ i, rate i * ξ i = 0) (t : ℝ) :
    let u := perronPath η (diagonalGreen hη rate hgap) hN hN0 hsmall (centerSeed hη.le ξ)
    HasDerivAt (exponentialLift η u)
      (fun i ↦ rate i * exponentialLift η u t i + N (exponentialLift η u t) i) t := by
  let G := diagonalGreen hη rate hgap
  let u := perronPath η G hN hN0 hsmall (centerSeed hη.le ξ)
  let f := composeExponentialWeight hN hN0 η u
  have heq : u = centerSeed hη.le ξ + G f :=
    perronPath_eq η G hN hN0 hsmall (centerSeed hη.le ξ)
  have hd := hasDerivAt_centerSeed_add_diagonalGreen hη rate hgap f ξ hξ t
  change HasDerivAt (exponentialLift η (centerSeed hη.le ξ + G f))
    (fun i ↦ rate i * exponentialLift η (centerSeed hη.le ξ + G f) t i +
      exponentialLift η f t i) t at hd
  rw [← heq] at hd
  simpa only [f, exponentialLift_composeExponentialWeight] using hd

end PDE.Analysis.Evolution
