/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.EReal.Inv

/-!
# Modulated nonlinear stability estimates

Modulated nonlinear stability arguments combine four inputs: coercive decay of
the linearized operator, a quadratic nonlinear remainder, a modulation term
bounded linearly by the perturbation, and a validated residual vector.

The main theorem combines their constants on a norm ball. A boundary theorem
then gives the strict inward-pointing inequality used to close a bootstrap
ball. Profiles, weights, symmetry conditions, and numerical constants are
supplied by each application.

The setting is a perturbation equation `e' = L e + N(e) + M(e) + r` in a real
inner product space `H`, with
`⟪L e, e⟫ ≤ -δ ‖e‖²`, `‖N(e)‖ ≤ c_N ‖e‖²`, `‖M(e)‖ ≤ c_M ‖e‖`, `‖r‖ ≤ ρ`.
Pairing the right-hand side with `e` and using Cauchy–Schwarz gives, for
`‖e‖ ≤ R`,

  `⟪e', e⟫ ≤ -(δ - c_M - c_N R) ‖e‖² + ρ ‖e‖`,

which is the energy inequality `½ d/dt ‖e‖² ≤ …` without the time derivative.
If `ρ < (δ - c_M - c_N R) R`, the right side is negative on the sphere
`‖e‖ = R`, so the vector field points strictly into the ball; this is the
inequality used to trap the perturbation. The theorems are algebraic
consequences of the four bounds.

The trapping condition `ρ < (δ - c_M - c_N R) R` has the form of condition (A.11) of the
stability lemma of Chen and Hou, Part I, Lemma A.2, with `R = E_*`; they prove that lemma for
weighted `L∞` energies of transport equations, and here the energy is the norm of `H`.

## Main results

* `ModulatedEnergyEstimate`: the structure recording `L, N, M, r` and their
  constants.
* `pairing_vectorField_le_on_ball`: the combined energy inequality on the
  ball of radius `R`, with rate `effectiveDecay R = δ - c_M - c_N R`.
* `pairing_vectorField_lt_zero_on_sphere`: strict inward pointing on the
  sphere when the residual bound is below `effectiveDecay R · R`.
* `pairing_vectorField_lt_zero_of_residual_eq_zero`: with zero residual
  (an exact profile), strict energy decay for every nonzero perturbation in
  the ball.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Appendix A, Lemma A.2.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Stability

open scoped RealInnerProductSpace

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Energy data for a perturbation equation
`e' = L e + N(e) + M(e) + r`. -/
structure ModulatedEnergyEstimate (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  /-- Linearized evolution operator. -/
  linear : H →L[ℝ] H
  /-- Nonlinear remainder. -/
  nonlinear : H → H
  /-- Modulation contribution after selecting the modulation parameters. -/
  modulation : H → H
  /-- Fixed profile residual or forcing error. -/
  residual : H
  /-- Linear coercive decay rate. -/
  decayRate : Set.Ioi (0 : ℝ)
  /-- Quadratic nonlinear constant. -/
  nonlinearConstant : NNReal
  /-- Linear modulation-loss constant. -/
  modulationConstant : NNReal
  /-- Validated residual norm bound. -/
  residualBound : NNReal
  /-- Coercivity of the linearized operator in the chosen energy inner product. -/
  linear_pairing_le :
    ∀ perturbation,
      ⟪linear perturbation, perturbation⟫ ≤
        -decayRate * ‖perturbation‖ * ‖perturbation‖
  /-- Quadratic nonlinear estimate. -/
  nonlinear_norm_le :
    ∀ perturbation,
      ‖nonlinear perturbation‖ ≤
        nonlinearConstant * ‖perturbation‖ * ‖perturbation‖
  /-- Linear bound for the selected modulation contribution. -/
  modulation_norm_le :
    ∀ perturbation,
      ‖modulation perturbation‖ ≤
        modulationConstant * ‖perturbation‖
  /-- Validated residual estimate. -/
  residual_norm_le : ‖residual‖ ≤ residualBound

namespace ModulatedEnergyEstimate

variable (estimate : ModulatedEnergyEstimate H)

/-- Full perturbation vector field. -/
def vectorField (perturbation : H) : H :=
  estimate.linear perturbation +
    estimate.nonlinear perturbation +
    estimate.modulation perturbation +
    estimate.residual

/-- Remaining decay rate on a closed norm ball. -/
def effectiveDecay (radius : ℝ) : ℝ :=
  estimate.decayRate -
    estimate.modulationConstant -
    estimate.nonlinearConstant * radius

/-- The nonlinear contribution to the energy pairing on a norm ball. -/
theorem nonlinear_pairing_le_on_ball
    {radius : ℝ} {perturbation : H}
    (hball : ‖perturbation‖ ≤ radius) :
    ⟪estimate.nonlinear perturbation, perturbation⟫ ≤
      estimate.nonlinearConstant * radius *
        ‖perturbation‖ * ‖perturbation‖ := by
  calc
    ⟪estimate.nonlinear perturbation, perturbation⟫ ≤
        ‖estimate.nonlinear perturbation‖ * ‖perturbation‖ :=
      real_inner_le_norm _ _
    _ ≤
        (estimate.nonlinearConstant *
          ‖perturbation‖ * ‖perturbation‖) *
          ‖perturbation‖ :=
      mul_le_mul_of_nonneg_right
        (estimate.nonlinear_norm_le perturbation)
        (norm_nonneg perturbation)
    _ ≤
        estimate.nonlinearConstant * radius *
          ‖perturbation‖ * ‖perturbation‖ := by
      have hcoefficient :
          estimate.nonlinearConstant * ‖perturbation‖ ≤
            estimate.nonlinearConstant * radius :=
        mul_le_mul_of_nonneg_left hball
          estimate.nonlinearConstant.property
      have hsquare :
          0 ≤ ‖perturbation‖ * ‖perturbation‖ :=
        mul_nonneg (norm_nonneg perturbation) (norm_nonneg perturbation)
      calc
        (estimate.nonlinearConstant *
            ‖perturbation‖ * ‖perturbation‖) *
            ‖perturbation‖ =
            (estimate.nonlinearConstant * ‖perturbation‖) *
              (‖perturbation‖ * ‖perturbation‖) := by ring
        _ ≤
            (estimate.nonlinearConstant * radius) *
              (‖perturbation‖ * ‖perturbation‖) :=
          mul_le_mul_of_nonneg_right hcoefficient hsquare
        _ =
            estimate.nonlinearConstant * radius *
              ‖perturbation‖ * ‖perturbation‖ := by ring

/-- The selected modulation term costs at most its declared linear rate in the energy pairing. -/
theorem modulation_pairing_le (perturbation : H) :
    ⟪estimate.modulation perturbation, perturbation⟫ ≤
      estimate.modulationConstant *
        ‖perturbation‖ * ‖perturbation‖ := by
  calc
    ⟪estimate.modulation perturbation, perturbation⟫ ≤
        ‖estimate.modulation perturbation‖ * ‖perturbation‖ :=
      real_inner_le_norm _ _
    _ ≤
        (estimate.modulationConstant * ‖perturbation‖) *
          ‖perturbation‖ :=
      mul_le_mul_of_nonneg_right
        (estimate.modulation_norm_le perturbation)
        (norm_nonneg perturbation)

/-- The validated profile residual contributes linearly in the perturbation norm. -/
theorem residual_pairing_le (perturbation : H) :
    ⟪estimate.residual, perturbation⟫ ≤
      estimate.residualBound * ‖perturbation‖ := by
  calc
    ⟪estimate.residual, perturbation⟫ ≤
        ‖estimate.residual‖ * ‖perturbation‖ :=
      real_inner_le_norm _ _
    _ ≤ estimate.residualBound * ‖perturbation‖ :=
      mul_le_mul_of_nonneg_right estimate.residual_norm_le
        (norm_nonneg perturbation)

/-- Combined modulated nonlinear energy inequality on a norm ball. -/
theorem pairing_vectorField_le_on_ball
    {radius : ℝ} {perturbation : H}
    (hball : ‖perturbation‖ ≤ radius) :
    ⟪estimate.vectorField perturbation, perturbation⟫ ≤
      -estimate.effectiveDecay radius *
          ‖perturbation‖ * ‖perturbation‖ +
        estimate.residualBound * ‖perturbation‖ := by
  rw [vectorField, inner_add_left, inner_add_left, inner_add_left]
  have hlinear := estimate.linear_pairing_le perturbation
  have hnonlinear :=
    estimate.nonlinear_pairing_le_on_ball hball
  have hmodulation := estimate.modulation_pairing_le perturbation
  have hresidual := estimate.residual_pairing_le perturbation
  dsimp only [effectiveDecay]
  linarith

/-- If residual forcing is smaller than the available decay on the boundary,
the energy vector field points strictly inward. -/
theorem pairing_vectorField_lt_zero_on_sphere
    {radius : ℝ}
    (hresidual :
      estimate.residualBound <
        estimate.effectiveDecay radius * radius)
    {perturbation : H} (hsphere : ‖perturbation‖ = radius) :
    ⟪estimate.vectorField perturbation, perturbation⟫ < 0 := by
  have hbound :=
    estimate.pairing_vectorField_le_on_ball hsphere.le
  rw [hsphere] at hbound
  -- Sphere membership makes the radius nonnegative; the strict residual margin rules out zero.
  have hradius : 0 ≤ radius := by
    rw [← hsphere]
    exact norm_nonneg perturbation
  have hresidual_nonneg : 0 ≤ (estimate.residualBound : ℝ) :=
    estimate.residualBound.property
  have hradius_ne : radius ≠ 0 := by
    intro hradius_zero
    rw [hradius_zero, mul_zero] at hresidual
    exact not_lt_of_ge hresidual_nonneg hresidual
  have hradius_pos : 0 < radius :=
    lt_of_le_of_ne hradius (Ne.symm hradius_ne)
  have hstrict :
      -estimate.effectiveDecay radius * radius * radius +
          estimate.residualBound * radius < 0 := by
    calc
      -estimate.effectiveDecay radius * radius * radius +
          estimate.residualBound * radius =
          (estimate.residualBound -
            estimate.effectiveDecay radius * radius) * radius := by
        ring
      _ < 0 := mul_neg_of_neg_of_pos (sub_neg.mpr hresidual) hradius_pos
  exact hbound.trans_lt hstrict

/-- In the exact-profile case, every sufficiently small perturbation has strict energy decay. -/
theorem pairing_vectorField_lt_zero_of_residual_eq_zero
    {radius : ℝ}
    (hdecay : 0 < estimate.effectiveDecay radius)
    (hresidual : estimate.residualBound = 0)
    {perturbation : H}
    (hnonzero : perturbation ≠ 0)
    (hball : ‖perturbation‖ ≤ radius) :
    ⟪estimate.vectorField perturbation, perturbation⟫ < 0 := by
  have hbound :=
    estimate.pairing_vectorField_le_on_ball hball
  have hresidual_real :
      (estimate.residualBound : ℝ) = 0 :=
    congrArg (fun bound : NNReal ↦ (bound : ℝ)) hresidual
  have hnorm : 0 < ‖perturbation‖ := norm_pos_iff.mpr hnonzero
  have hstrict :
      -(estimate.effectiveDecay radius *
          ‖perturbation‖ * ‖perturbation‖) < 0 :=
    neg_neg_of_pos (mul_pos (mul_pos hdecay hnorm) hnorm)
  calc
    ⟪estimate.vectorField perturbation, perturbation⟫ ≤
        -estimate.effectiveDecay radius *
            ‖perturbation‖ * ‖perturbation‖ +
          estimate.residualBound * ‖perturbation‖ :=
      hbound
    _ = -(estimate.effectiveDecay radius *
          ‖perturbation‖ * ‖perturbation‖) := by
      rw [hresidual_real]
      ring
    _ < 0 := hstrict

end ModulatedEnergyEstimate

end PDE.Analysis.Stability
