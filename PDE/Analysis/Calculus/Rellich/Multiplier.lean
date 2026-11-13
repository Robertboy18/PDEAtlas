/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Rellich.Field
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Rellich flux for a variable multiplier

The stress-energy flux is contracted with an arbitrary C¹ vector field.
Its divergence retains the antisymmetric derivative of the second field;
for a gradient this remainder vanishes. The normal component is signed,
so the identity applies to transverse multipliers without star-shapedness.
-/

@[expose] public noncomputable section

open scoped Gradient

namespace PDE.Analysis

variable {n : ℕ}

/-- The stress-energy flux contracted with the multiplier `X`. -/
def rellichMultiplierField (X G : ℝ^n → ℝ^n) (x : ℝ^n) : ℝ^n :=
  inner ℝ (X x) (G x) • G x - (‖G x‖ ^ 2 / 2) • X x

/-- A dilation multiplier recovers the usual Rellich field. -/
@[simp] theorem rellichMultiplierField_sub_const (c : ℝ^n) (G : ℝ^n → ℝ^n) :
    rellichMultiplierField (fun x ↦ x - c) G = rellichField c G := rfl

/-- C¹ multiplier and gradient fields give a C¹ stress-energy flux. -/
theorem contDiff_rellichMultiplierField {X G : ℝ^n → ℝ^n}
    (hX : ContDiff ℝ 1 X) (hG : ContDiff ℝ 1 G) :
    ContDiff ℝ 1 (rellichMultiplierField X G) :=
  ((hX.inner ℝ hG).smul hG).sub
    ((hG.norm_sq (𝕜 := ℝ)).div_const 2 |>.smul hX)

/-- The exact divergence, including the antisymmetric derivative remainder. -/
theorem divergence_rellichMultiplierField {X G : ℝ^n → ℝ^n} {x : ℝ^n}
    (hX : DifferentiableAt ℝ X x) (hG : DifferentiableAt ℝ G x) :
    ∇· (rellichMultiplierField X G) x =
      inner ℝ (X x) (G x) * ∇· G x +
        inner ℝ (fderiv ℝ X x (G x)) (G x) -
        (‖G x‖ ^ 2 / 2) * ∇· X x +
        inner ℝ (X x) (fderiv ℝ G x (G x)) -
        inner ℝ (G x) (fderiv ℝ G x (X x)) := by
  have ha := hX.inner ℝ hG
  have hb : DifferentiableAt ℝ (fun y ↦ ‖G y‖ ^ 2 / 2) x := by
    simpa only [div_eq_mul_inv] using (hG.norm_sq (𝕜 := ℝ)).mul_const (2 : ℝ)⁻¹
  change ∇· (fun y ↦ inner ℝ (X y) (G y) • G y -
    (‖G y‖ ^ 2 / 2) • X y) x = _
  rw [divergence_sub
    (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp x (ha.fun_smul hG))
    (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp x (hb.fun_smul hX))]
  rw [divergence_smul ha hG, divergence_smul hb hX, fderiv_inner_apply ℝ hX hG]
  have hnorm : HasFDerivAt (fun y ↦ ‖G y‖ ^ 2 / 2)
      ((innerSL ℝ (G x)).comp (fderiv ℝ G x)) x := by
    convert (hG.hasFDerivAt.norm_sq.mul_const (2 : ℝ)⁻¹) using 1
    · simp only [div_eq_mul_inv]
    · ext v
      simp
  rw [hnorm.fderiv]
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  ring

/-- Schwarz symmetry removes the remainder for an actual gradient germ. -/
theorem divergence_rellichMultiplierField_of_gradient
    {u : ℝ^n → ℝ} {X G : ℝ^n → ℝ^n} {x : ℝ^n}
    (hu : ContDiffAt ℝ 2 u x) (hX : DifferentiableAt ℝ X x)
    (hG : DifferentiableAt ℝ G x) (heq : G =ᶠ[nhds x] ∇ u) :
    ∇· (rellichMultiplierField X G) x =
      inner ℝ (X x) (G x) * laplacian u x +
        inner ℝ (fderiv ℝ X x (G x)) (G x) -
        (‖G x‖ ^ 2 / 2) * ∇· X x := by
  have hdiv : ∇· G x = laplacian u x := by
    rw [laplacian_eq_divergence_gradient]
    exact heq.divergence_eq
  rw [divergence_rellichMultiplierField hX hG, hdiv,
    (heq.fderiv (𝕜 := ℝ)).eq_of_nhds]
  have hs := hu.inner_fderiv_gradient_comm (G x) (X x)
  rw [real_inner_comm] at hs
  linarith

/-- A normal gradient gives half its squared norm times the signed multiplier flux. -/
theorem inner_rellichMultiplierField_of_normal
    {X G : ℝ^n → ℝ^n} (x ν : ℝ^n) (hG : G x = inner ℝ (G x) ν • ν) :
    inner ℝ (rellichMultiplierField X G x) ν =
      (‖G x‖ ^ 2 / 2) * inner ℝ (X x) ν := by
  have hr : inner ℝ (X x) (G x) = inner ℝ (G x) ν * inner ℝ (X x) ν :=
    (congrArg (fun z ↦ inner ℝ (X x) z) hG).trans (inner_smul_right _ _ _)
  have hn : ‖G x‖ ^ 2 = inner ℝ (G x) ν ^ 2 := by
    have h := congrArg (fun z ↦ inner ℝ (G x) z) hG
    simpa only [real_inner_self_eq_norm_sq, inner_smul_right, pow_two] using h
  rw [rellichMultiplierField, inner_sub_left]
  simp only [inner_smul_left, starRingEnd_apply, star_trivial]
  rw [hr, hn]
  ring

/-- The volume stress is bounded by squared forcing and gradient norms.
The three constants bound the multiplier, its derivative, and its divergence. -/
theorem two_mul_rellich_integrand_le {v w : ℝ^n}
    {A : ℝ^n →L[ℝ] ℝ^n} {l d M K D : ℝ}
    (hM : ‖v‖ ≤ M) (hK : ‖A‖ ≤ K) (hD : |d| ≤ D) :
    2 * (inner ℝ v w * l + inner ℝ (A w) w - (‖w‖ ^ 2 / 2) * d) ≤
      l ^ 2 + (M ^ 2 + 2 * K + D) * ‖w‖ ^ 2 := by
  have hp : |inner ℝ v w| ≤ M * ‖w‖ :=
    (abs_real_inner_le_norm v w).trans (mul_le_mul_of_nonneg_right hM (norm_nonneg w))
  have hs := (sq_le_sq₀ (abs_nonneg (inner ℝ v w))
    (mul_nonneg ((norm_nonneg v).trans hM) (norm_nonneg w))).2 hp
  simp only [sq_abs, mul_pow] at hs
  have hy : 2 * inner ℝ v w * l ≤ M ^ 2 * ‖w‖ ^ 2 + l ^ 2 := by
    nlinarith [sq_nonneg (inner ℝ v w - l)]
  have ha : inner ℝ (A w) w ≤ K * ‖w‖ ^ 2 := calc
    _ ≤ ‖A w‖ * ‖w‖ := real_inner_le_norm _ _
    _ ≤ (‖A‖ * ‖w‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right (A.le_opNorm w) (norm_nonneg w)
    _ = ‖A‖ * ‖w‖ ^ 2 := by ring
    _ ≤ K * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right hK (sq_nonneg _)
  have hd : -d * ‖w‖ ^ 2 ≤ D * ‖w‖ ^ 2 :=
    mul_le_mul_of_nonneg_right ((neg_le_abs d).trans hD) (sq_nonneg _)
  nlinarith

end PDE.Analysis
