/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import
  PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.PowerIncrement
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.Operator

/-!
# Second finite differences of the nonlinear cone equation

Three solutions at the same time scale give a linear equation for their
second finite difference. The coefficient is the first derivative of the
reaction at the middle solution. The two nonlinear remainders require
only first differentiability.

For absolute powers between one and two, absorption leaves a remainder
of order `p` in the first increments. This estimate concerns the
cone equation; it neither assumes nor proves a second derivative of its
solutions.
-/

@[expose] public noncomputable section

open BoundedContinuousFunction

namespace WaveEquation.SmallData.Classical.LocalPower.LowerPower

private theorem second_increment_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K D : E →L[ℝ] E) (N : E → E) {t : ℝ} (a₀ a₁ a₂ u₀ u₁ u₂ : E) (h₀ : u₀ = a₀ + t ^ 2 • K (N u₀))
    (h₁ : u₁ = a₁ + t ^ 2 • K (N u₁)) (h₂ : u₂ = a₂ + t ^ 2 • K (N u₂))
    (hsmall : t ^ 2 * ‖K‖ * ‖D‖ ≤ 1 / 2) :
    ‖(u₁ - u₀) + (u₂ - u₀)‖ ≤ 2 * ‖(a₁ - a₀) + (a₂ - a₀)‖ + 2 * t ^ 2 *
      ‖K ((N u₁ - N u₀ - D (u₁ - u₀)) + (N u₂ - N u₀ - D (u₂ - u₀)))‖ := by
  let d := (u₁ - u₀) + (u₂ - u₀)
  let b := (a₁ - a₀) + (a₂ - a₀)
  let r₁ := N u₁ - N u₀ - D (u₁ - u₀)
  let r₂ := N u₂ - N u₀ - D (u₂ - u₀)
  have heq : d = b + t ^ 2 • K (D d + (r₁ + r₂)) := by
    have hsource : D d + (r₁ + r₂) = (N u₁ - N u₀) + (N u₂ - N u₀) := by
      dsimp [d, r₁, r₂]
      rw [map_add]
      abel
    have hdiff₁ := congrArg₂ (fun x y : E ↦ x - y) h₁ h₀
    have hdiff₂ := congrArg₂ (fun x y : E ↦ x - y) h₂ h₀
    calc
      d = ((a₁ + t ^ 2 • K (N u₁)) - (a₀ + t ^ 2 • K (N u₀))) +
          ((a₂ + t ^ 2 • K (N u₂)) - (a₀ + t ^ 2 • K (N u₀))) :=
        congrArg₂ (fun x y : E ↦ x + y) hdiff₁ hdiff₂
      _ = b + t ^ 2 • K (D d + (r₁ + r₂)) := by
        rw [hsource, map_add, map_sub, map_sub, smul_add, smul_sub, smul_sub]
        dsimp only [b]
        abel
  have hnorm :
      ‖d‖ ≤ ‖b‖ + t ^ 2 * (‖K‖ * (‖D‖ * ‖d‖) + ‖K (r₁ + r₂)‖) := by
    calc
      ‖d‖ = ‖b + t ^ 2 • K (D d + (r₁ + r₂))‖ := congrArg norm heq
      _ ≤ ‖b‖ + ‖t ^ 2 • K (D d + (r₁ + r₂))‖ := norm_add_le _ _
      _ = ‖b‖ + t ^ 2 * ‖K (D d + (r₁ + r₂))‖ := by
        rw [norm_smul, Real.norm_of_nonneg (sq_nonneg t)]
      _ ≤ ‖b‖ + t ^ 2 * (‖K‖ * (‖D‖ * ‖d‖) + ‖K (r₁ + r₂)‖) := by
        gcongr
        rw [map_add]
        exact (norm_add_le _ _).trans (add_le_add
          ((K.le_opNorm _).trans (mul_le_mul_of_nonneg_left (D.le_opNorm d)
            (norm_nonneg K))) (le_refl _))
  have habs := mul_le_mul_of_nonneg_right hsmall (norm_nonneg d)
  change ‖d‖ ≤ 2 * ‖b‖ + 2 * t ^ 2 * ‖K (r₁ + r₂)‖
  nlinarith

/-- Absorption of the linearized power equation keeps both nonlinear
remainders inside the Duhamel operator. Their spatial distribution
on the cone is retained in this estimate. -/
theorem norm_cone_second_increment_le_remainder {p t M : ℝ}
    (hp : 1 < p) (a₀ a₁ a₂ u₀ u₁ u₂ : Cone →ᵇ ℝ) (hu₀ : ‖u₀‖ ≤ M) :
    let f : C(ℝ, ℝ) := ⟨fun x ↦ |x| ^ p, by
      simpa only [Real.norm_eq_abs] using
        (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun x : ℝ ↦ ‖x‖ ^ p)).continuous⟩
    let N := composeCompact (α := Cone) f
    let D := fderiv ℝ N u₀
    u₀ = a₀ + t ^ 2 • duhamelOperator (N u₀) →
    u₁ = a₁ + t ^ 2 • duhamelOperator (N u₁) →
    u₂ = a₂ + t ^ 2 • duhamelOperator (N u₂) →
    t ^ 2 * ‖duhamelOperator‖ * (p * M ^ (p - 1)) ≤ 1 / 2 →
    ‖(u₁ - u₀) + (u₂ - u₀)‖ ≤
      2 * ‖(a₁ - a₀) + (a₂ - a₀)‖ +
        2 * t ^ 2 * ‖duhamelOperator ((N u₁ - N u₀ - D (u₁ - u₀)) +
          (N u₂ - N u₀ - D (u₂ - u₀)))‖ := by
  intro f N D h₀ h₁ h₂ hsmall
  have hD : ‖D‖ ≤ p * M ^ (p - 1) := norm_fderiv_composeCompact_abs_rpow_le hp u₀ hu₀
  exact second_increment_bound duhamelOperator D N a₀ a₁ a₂ u₀ u₁ u₂ h₀ h₁ h₂
    ((mul_le_mul_of_nonneg_left hD
      (mul_nonneg (sq_nonneg t) (norm_nonneg duhamelOperator))).trans hsmall)

/-- The absolute-power cone equation controls second finite
differences by the free-field difference and `p`th powers of the first
solution differences. Only the central solution needs a norm bound. -/
theorem norm_cone_second_increment_le {p t M : ℝ}
    (hp : 1 < p) (hp₂ : p ≤ 2)
    (a₀ a₁ a₂ u₀ u₁ u₂ : Cone →ᵇ ℝ) (hu₀ : ‖u₀‖ ≤ M) :
    let f : C(ℝ, ℝ) := ⟨fun x ↦ |x| ^ p, by
      simpa only [Real.norm_eq_abs] using
        (contDiff_norm_rpow hp : ContDiff ℝ 1 (fun x : ℝ ↦ ‖x‖ ^ p)).continuous⟩
    let N := composeCompact (α := Cone) f
    u₀ = a₀ + t ^ 2 • duhamelOperator (N u₀) →
    u₁ = a₁ + t ^ 2 • duhamelOperator (N u₁) →
    u₂ = a₂ + t ^ 2 • duhamelOperator (N u₂) →
    t ^ 2 * ‖duhamelOperator‖ * (p * M ^ (p - 1)) ≤ 1 / 2 →
    ‖(u₁ - u₀) + (u₂ - u₀)‖ ≤
      2 * ‖(a₁ - a₀) + (a₂ - a₀)‖ +
        2 * (t ^ 2 * ‖duhamelOperator‖) *
          ((2 * p) * ‖u₁ - u₀‖ ^ p + (2 * p) * ‖u₂ - u₀‖ ^ p) := by
  intro f N h₀ h₁ h₂ hsmall
  have he := norm_cone_second_increment_le_remainder hp a₀ a₁ a₂ u₀ u₁ u₂ hu₀ h₀ h₁ h₂ hsmall
  apply he.trans
  have hrem := (norm_add_le (N u₁ - N u₀ - fderiv ℝ N u₀ (u₁ - u₀))
    (N u₂ - N u₀ - fderiv ℝ N u₀ (u₂ - u₀))).trans (add_le_add
        (norm_composeCompact_abs_rpow_sub_linear_le hp hp₂ u₀ u₁)
        (norm_composeCompact_abs_rpow_sub_linear_le hp hp₂ u₀ u₂))
  calc
    _ ≤ 2 * ‖(a₁ - a₀) + (a₂ - a₀)‖ + 2 * t ^ 2 * (‖duhamelOperator‖ *
          ((2 * p) * ‖u₁ - u₀‖ ^ p + (2 * p) * ‖u₂ - u₀‖ ^ p)) := by
      gcongr
      exact (duhamelOperator.le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hrem (norm_nonneg duhamelOperator))
    _ = _ := by simp only [mul_assoc]

end WaveEquation.SmallData.Classical.LocalPower.LowerPower
