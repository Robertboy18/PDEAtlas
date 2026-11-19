/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.InvariantGraph.Construction
public import PDE.Analysis.Evolution.ODE.Linear.Green.Uniqueness
import CAS.ExactTactic

/-!
# Characterization by the weighted differential equation

For a finite diagonal equation, the whole-line exponential growth condition
eliminates every noncenter homogeneous mode. The center values at zero fix the
remaining constants. Consequently a weighted nonlinear solution must
be the path obtained from the Lyapunov–Perron contraction.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction NNReal

namespace PDE.Analysis.Evolution

variable {ι : Type*} [Fintype ι] {η : ℝ}

/-- Two solutions of the diagonal equation `x' = rate • x + f` of growth
`O(e^{η|t|})`, with the same forcing and the same center values at `0`, agree on
the whole real line when every nonzero rate satisfies `η < |rate i|`. -/
theorem eq_of_weighted_diagonal_hasDerivAt (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|) (u v : ℝ →ᵇ (ι → ℝ))
    (f : ℝ → (ι → ℝ))
    (hu : ∀ t, HasDerivAt (exponentialLift η u)
      (fun i ↦ rate i * exponentialLift η u t i + f t i) t)
    (hv : ∀ t, HasDerivAt (exponentialLift η v)
      (fun i ↦ rate i * exponentialLift η v t i + f t i) t)
    (hinit : ∀ i, rate i = 0 → u 0 i = v 0 i) :
    u = v := by
  apply exponentialLift_injective η
  ext t i
  let d : ℝ → ℝ := fun s ↦ exponentialLift η u s i - exponentialLift η v s i
  have hd (s : ℝ) : HasDerivAt d (rate i • d s) s := by
    have h := (hasDerivAt_pi.mp (hu s) i).sub (hasDerivAt_pi.mp (hv s) i)
    convert h using 1
    dsimp [d]
    cas
  have hzero : d = 0 := by
    by_cases hi : rate i = 0
    · have hd0 (s : ℝ) : HasDerivAt d 0 s := by simpa only [hi, zero_smul] using hd s
      have hc := is_const_of_deriv_eq_zero (fun s ↦ (hd0 s).differentiableAt)
        (fun s ↦ (hd0 s).deriv)
      funext s
      have h0 : d 0 = 0 := by simp only [d, exponentialLift_zero, hinit i hi, sub_self]
      exact (hc s 0).trans h0
    · apply eq_zero_of_hasDerivAt_of_exponential_bound (C := ‖u‖ + ‖v‖) hd (hgap i hi)
      intro s
      calc
        ‖d s‖ ≤ ‖exponentialLift η u s i‖ + ‖exponentialLift η v s i‖ :=
          norm_sub_le _ _
        _ ≤ ‖exponentialLift η u s‖ + ‖exponentialLift η v s‖ :=
          add_le_add (norm_le_pi_norm _ i) (norm_le_pi_norm _ i)
        _ ≤ Real.exp (η * |s|) * ‖u‖ + Real.exp (η * |s|) * ‖v‖ :=
          add_le_add (norm_exponentialLift_le η u s) (norm_exponentialLift_le η v s)
        _ = Real.exp (η * |s|) * (‖u‖ + ‖v‖) := (mul_add _ _ _).symm
  exact sub_eq_zero.mp (congrFun hzero t)

/-- The center Green primitive vanishes at its base time. -/
theorem diagonalGreen_zero_apply_of_rate_eq_zero (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|) (f : ℝ →ᵇ (ι → ℝ))
    (i : ι) (hi : rate i = 0) :
    diagonalGreen hη rate hgap f 0 i = 0 := by
  rw [diagonalGreen_apply]
  simp only [hi, rateGreen, dite_true]
  have h := exponentialLift_centerGreen hη (piLinearIsometryEquiv (𝕜 := ℝ) f i) 0
  simpa only [exponentialLift_zero, intervalIntegral.integral_same] using h

variable {L : ℝ≥0} {N : (ι → ℝ) → (ι → ℝ)}

/-- A weighted solution of the nonlinear diagonal equation with prescribed center data
is the constructed fixed path. -/
theorem eq_perronPath_of_hasDerivAt (hη : 0 < η) (rate : ι → ℝ)
    (hgap : ∀ i, rate i ≠ 0 → η < |rate i|)
    (hN : LipschitzWith L N) (hN0 : N 0 = 0)
    (hsmall : ‖diagonalGreen hη rate hgap‖ * L < 1)
    (ξ : ι → ℝ) (hξ : ∀ i, rate i * ξ i = 0) (u : ℝ →ᵇ (ι → ℝ))
    (hu : ∀ t, HasDerivAt (exponentialLift η u)
      (fun i ↦ rate i * exponentialLift η u t i + N (exponentialLift η u t) i) t)
    (hinit : ∀ i, rate i = 0 → u 0 i = ξ i) :
    u = perronPath η (diagonalGreen hη rate hgap) hN hN0 hsmall (centerSeed hη.le ξ) := by
  apply perronPath_unique
  let f := composeExponentialWeight hN hN0 η u
  apply eq_of_weighted_diagonal_hasDerivAt rate hgap u
    (centerSeed hη.le ξ + diagonalGreen hη rate hgap f)
    (fun t ↦ N (exponentialLift η u t)) hu
  · intro t
    simpa only [f, exponentialLift_composeExponentialWeight] using
      hasDerivAt_centerSeed_add_diagonalGreen hη rate hgap f ξ hξ t
  · intro i hi
    change u 0 i = centerSeed hη.le ξ 0 i + diagonalGreen hη rate hgap f 0 i
    rw [diagonalGreen_zero_apply_of_rate_eq_zero hη rate hgap f i hi, add_zero]
    have h := congrArg (fun z : ι → ℝ ↦ z i) (exponentialLift_centerSeed hη.le ξ 0)
    simpa only [exponentialLift_zero, hinit i hi] using h.symm

end PDE.Analysis.Evolution
