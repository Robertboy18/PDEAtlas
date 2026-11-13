/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Divergence.Locality
public import PDE.Analysis.Calculus.Gradient.Hessian
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The Rellich vector field and its actual divergence

The calculation is first made for an arbitrary differentiable vector field,
retaining its antisymmetric derivative remainder. For an actual gradient
the remainder vanishes by Schwarz symmetry.
-/

@[expose] public noncomputable section

open scoped Gradient

namespace PDE.Analysis

variable {n : ℕ}

/-- The stress-energy flux associated to a vector field and dilation about `c`. -/
def rellichField (c : ℝ^n) (G : ℝ^n → ℝ^n) (x : ℝ^n) : ℝ^n :=
  inner ℝ (x - c) (G x) • G x - (‖G x‖ ^ 2 / 2) • (x - c)

/-- A C¹ vector field has a C¹ Rellich field. -/
theorem contDiff_rellichField {G : ℝ^n → ℝ^n} (hG : ContDiff ℝ 1 G) (c : ℝ^n) :
    ContDiff ℝ 1 (rellichField c G) :=
  (((contDiff_id.sub contDiff_const).inner ℝ hG).smul hG).sub
    ((hG.norm_sq (𝕜 := ℝ)).div_const 2 |>.smul (contDiff_id.sub contDiff_const))

/-- The divergence of a dilation field is the dimension, with arbitrary center. -/
theorem divergence_sub_const (c x : ℝ^n) :
    ∇· (fun y ↦ y - c) x = (n : ℝ) := by
  have hi (i : Fin n) : (∂[i] (fun y : ℝ^n ↦ y i - c i)) x = 1 := by
    have hp : HasFDerivAt (fun y : ℝ^n ↦ y i - c i) (EuclideanSpace.proj (𝕜 := ℝ) i) x :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.sub_const (c i)
    rw [partialDeriv, hp.fderiv]
    simp
  simp only [divergence, PiLp.sub_apply, hi, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The exact Rellich divergence for an arbitrary differentiable vector field.
The final two terms record its antisymmetric derivative. -/
theorem divergence_rellichField {G : ℝ^n → ℝ^n} {x : ℝ^n}
    (hG : DifferentiableAt ℝ G x) (c : ℝ^n) :
    ∇· (rellichField c G) x =
      inner ℝ (x - c) (G x) * ∇· G x +
        (1 - (n : ℝ) / 2) * ‖G x‖ ^ 2 +
        inner ℝ (x - c) (fderiv ℝ G x (G x)) -
        inner ℝ (G x) (fderiv ℝ G x (x - c)) := by
  have hr : DifferentiableAt ℝ (fun y : ℝ^n ↦ y - c) x :=
    differentiableAt_id.sub_const c
  have ha := hr.inner ℝ hG
  have hb : DifferentiableAt ℝ (fun y ↦ ‖G y‖ ^ 2 / 2) x := by
    simpa only [div_eq_mul_inv] using (hG.norm_sq (𝕜 := ℝ)).mul_const (2 : ℝ)⁻¹
  change ∇· (fun y ↦ inner ℝ (y - c) (G y) • G y -
    (‖G y‖ ^ 2 / 2) • (y - c)) x = _
  rw [divergence_sub
    (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp x (ha.fun_smul hG))
    (fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt.comp x (hb.fun_smul hr))]
  rw [divergence_smul ha hG, divergence_smul hb hr, divergence_sub_const,
    fderiv_inner_apply ℝ hr hG]
  have hnorm : HasFDerivAt (fun y ↦ ‖G y‖ ^ 2 / 2)
      ((innerSL ℝ (G x)).comp (fderiv ℝ G x)) x := by
    convert (hG.hasFDerivAt.norm_sq.mul_const (2 : ℝ)⁻¹) using 1
    · simp only [div_eq_mul_inv]
    · ext v
      simp
  have hrad : HasFDerivAt (fun y : ℝ^n ↦ y - c) (ContinuousLinearMap.id ℝ (ℝ^n)) x :=
    (hasFDerivAt_id x).sub_const c
  rw [hnorm.fderiv, hrad.fderiv]
  simp only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  ring

/-- When the vector field is the actual gradient near the evaluation point,
the Rellich divergence has no antisymmetric remainder. -/
theorem divergence_rellichField_of_gradient
    {u : ℝ^n → ℝ} {G : ℝ^n → ℝ^n} {x : ℝ^n}
    (hu : ContDiffAt ℝ 2 u x) (hG : DifferentiableAt ℝ G x)
    (heq : G =ᶠ[nhds x] ∇ u) (c : ℝ^n) :
    ∇· (rellichField c G) x =
      inner ℝ (x - c) (G x) * laplacian u x +
        (1 - (n : ℝ) / 2) * ‖G x‖ ^ 2 := by
  have hdiv : ∇· G x = laplacian u x := by
    rw [laplacian_eq_divergence_gradient]
    exact heq.divergence_eq
  rw [divergence_rellichField hG c, hdiv, (heq.fderiv (𝕜 := ℝ)).eq_of_nhds]
  have hs := hu.inner_fderiv_gradient_comm (G x) (x - c)
  rw [real_inner_comm] at hs
  linarith

end PDE.Analysis
