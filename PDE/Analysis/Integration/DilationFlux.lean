/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-!
# Dilation flux on half-plane rectangles

The divergence theorem applied to `x * u(x)²` gives the exact finite-domain
identity used to recover an unweighted square integral from a radial gradient
moment. The axis face has zero flux, and the flux through the other three faces is
assumed to decay.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open MeasureTheory Set

/-- The finite-radius dilation identity on `[0,R] × [-R,R]` for a `C¹` function.
The derivatives are Fréchet derivatives in the two coordinate directions. -/
theorem halfRectangle_dilation_identity (u : ℝ × ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (R : ℝ) (hR : 0 ≤ R) :
    2 * (∫ x in Icc (0, -R) (R, R), u x ^ 2) +
      2 * (∫ x in Icc (0, -R) (R, R),
        u x * (x.1 * fderiv ℝ u x (1, 0) + x.2 * fderiv ℝ u x (0, 1))) =
      (∫ r in (0 : ℝ)..R, R * u (r, R) ^ 2) +
        (∫ r in (0 : ℝ)..R, R * u (r, -R) ^ 2) +
        ∫ z in -R..R, R * u (R, z) ^ 2 := by
  let F : ℝ × ℝ → ℝ := fun x ↦ x.1 * u x ^ 2
  let G : ℝ × ℝ → ℝ := fun x ↦ x.2 * u x ^ 2
  let dF : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun x ↦
    (u x ^ 2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (x.1 * (2 * u x)) • fderiv ℝ u x
  let dG : ℝ × ℝ → (ℝ × ℝ →L[ℝ] ℝ) := fun x ↦
    (u x ^ 2) • ContinuousLinearMap.snd ℝ ℝ ℝ +
      (x.2 * (2 * u x)) • fderiv ℝ u x
  have hdF (x : ℝ × ℝ) : HasFDerivAt F (dF x) x := by
    convert! (hasFDerivAt_fst (𝕜 := ℝ) (p := x)).mul
      ((hu.differentiable (by norm_num)).differentiableAt.hasFDerivAt.pow 2) using 1
    simp [dF, nsmul_eq_mul, smul_smul, add_comm]
  have hdG (x : ℝ × ℝ) : HasFDerivAt G (dG x) x := by
    convert! (hasFDerivAt_snd (𝕜 := ℝ) (p := x)).mul
      ((hu.differentiable (by norm_num)).differentiableAt.hasFDerivAt.pow 2) using 1
    simp [dG, nsmul_eq_mul, smul_smul, add_comm]
  have hcF : Continuous F := continuous_fst.mul (hu.continuous.pow 2)
  have hcG : Continuous G := continuous_snd.mul (hu.continuous.pow 2)
  have hdu (v : ℝ × ℝ) : Continuous (fun x ↦ fderiv ℝ u x v) :=
    (hu.continuous_fderiv_apply (hn := by norm_num)).comp
      (continuous_id.prodMk continuous_const)
  have hcDiv : Continuous (fun x ↦ dF x (1, 0) + dG x (0, 1)) := by
    dsimp [dF, dG]
    fun_prop
  have hid := integral_divergence_prod_Icc_of_hasFDerivAt_of_le F G dF dG
    (0, -R) (R, R) (show (0, -R) ≤ (R, R) from ⟨hR, by linarith⟩)
    hcF.continuousOn hcG.continuousOn (fun x _ ↦ hdF x) (fun x _ ↦ hdG x)
    (hcDiv.integrableOn_Icc)
  have hsq : IntegrableOn (fun x : ℝ × ℝ ↦ u x ^ 2) (Icc (0, -R) (R, R)) :=
    (hu.continuous.pow 2).integrableOn_Icc
  have hmixed : IntegrableOn (fun x : ℝ × ℝ ↦
      u x * (x.1 * fderiv ℝ u x (1, 0) + x.2 * fderiv ℝ u x (0, 1)))
      (Icc (0, -R) (R, R)) :=
    (hu.continuous.mul ((continuous_fst.mul (hdu (1, 0))).add
      (continuous_snd.mul (hdu (0, 1))))).integrableOn_Icc
  have heq : (fun x ↦ dF x (1, 0) + dG x (0, 1)) =
      fun x ↦ 2 * u x ^ 2 + 2 *
        (u x * (x.1 * fderiv ℝ u x (1, 0) + x.2 * fderiv ℝ u x (0, 1))) := by
    funext x
    simp [dF, dG]
    ring
  rw [heq, integral_add (hsq.const_mul 2) (hmixed.const_mul 2),
    integral_const_mul, integral_const_mul] at hid
  simpa [F, G, neg_mul, intervalIntegral.integral_neg, sub_neg_eq_add] using hid

/-- The truncated square estimate obtained from the divergence identity.
Only `C¹` regularity and a nonnegative radius are required on the bounded box;
all local integrability obligations follow from continuity. -/
theorem halfRectangle_l2_squared_le_flux_add_gradient (u : ℝ × ℝ → ℝ)
    (hu : ContDiff ℝ 1 u) (R : ℝ) (hR : 0 ≤ R) :
    (∫ x in Icc (0, -R) (R, R), u x ^ 2) ≤
      ((∫ r in (0 : ℝ)..R, R * u (r, R) ^ 2) +
        (∫ r in (0 : ℝ)..R, R * u (r, -R) ^ 2) +
        ∫ z in -R..R, R * u (R, z) ^ 2) +
      ∫ x in Icc (0, -R) (R, R), (x.1 ^ 2 + x.2 ^ 2) *
        ((fderiv ℝ u x (1, 0)) ^ 2 + (fderiv ℝ u x (0, 1)) ^ 2) := by
  have hdu (v : ℝ × ℝ) : Continuous (fun x ↦ fderiv ℝ u x v) :=
    (hu.continuous_fderiv_apply (hn := by norm_num)).comp
      (continuous_id.prodMk continuous_const)
  let mixed : ℝ × ℝ → ℝ := fun x ↦
    u x * (x.1 * fderiv ℝ u x (1, 0) + x.2 * fderiv ℝ u x (0, 1))
  let moment : ℝ × ℝ → ℝ := fun x ↦ (x.1 ^ 2 + x.2 ^ 2) *
    ((fderiv ℝ u x (1, 0)) ^ 2 + (fderiv ℝ u x (0, 1)) ^ 2)
  have hm : Continuous mixed :=
    hu.continuous.mul ((continuous_fst.mul (hdu (1, 0))).add
      (continuous_snd.mul (hdu (0, 1))))
  have hg : Continuous moment :=
    ((continuous_fst.pow 2).add (continuous_snd.pow 2)).mul
      (((hdu (1, 0)).pow 2).add ((hdu (0, 1)).pow 2))
  have hs := (hu.continuous.pow 2).integrableOn_Icc (μ := volume) (a := (0, -R)) (b := (R, R))
  have hpoint (x : ℝ × ℝ) : -2 * mixed x ≤ u x ^ 2 + moment x := by
    dsimp [mixed, moment]
    nlinarith only [sq_nonneg (u x + x.1 * fderiv ℝ u x (1, 0) +
      x.2 * fderiv ℝ u x (0, 1)), sq_nonneg
      (x.1 * fderiv ℝ u x (0, 1) - x.2 * fderiv ℝ u x (1, 0))]
  have hint := integral_mono (μ := volume.restrict (Icc (0, -R) (R, R)))
    ((hm.integrableOn_Icc).const_mul (-2)) (hs.add hg.integrableOn_Icc) hpoint
  change IntegrableOn (fun x ↦ u x ^ 2) (Icc (0, -R) (R, R)) volume at hs
  simp only [Pi.add_apply, Pi.pow_apply] at hint
  rw [integral_const_mul, integral_add hs hg.integrableOn_Icc] at hint
  have hid := halfRectangle_dilation_identity u hu R hR
  change 2 * _ + 2 * (∫ x in Icc (0, -R) (R, R), mixed x) = _ at hid
  change _ ≤ _ + ∫ x in Icc (0, -R) (R, R), moment x
  linarith

end PDE.Analysis
