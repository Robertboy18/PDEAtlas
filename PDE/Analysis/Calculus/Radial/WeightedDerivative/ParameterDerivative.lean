/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Radial.WeightedDerivative.Regularity

/-!
# Parameter derivatives of weighted radial transforms

A fixed directional derivative in an external parameter commutes with the
weighted radial transform. The induction uses the regular recurrence at zero
and symmetry of mixed derivatives of the original profile. A transform of
order `k` needs only `k+1` derivatives for one parameter derivative.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- First parameter derivatives commute with a weighted radial transform at
every signed radius, at the exact finite differentiability order. -/
theorem fderiv_oddRadialTransform_pow_mul
    (k : ℕ) {F : E × ℝ → ℝ} (hF : ContDiff ℝ (k + 1) F)
    (x v : E) (r : ℝ) :
    fderiv ℝ (fun y ↦
      oddRadialTransform k (fun s ↦ s ^ (2 * k + 1) * F (y, s)) r) x v =
      oddRadialTransform k
        (fun s ↦ s ^ (2 * k + 1) * fderiv ℝ (fun y ↦ F (y, s)) x v) r := by
  induction k generalizing F with
  | zero =>
      have hd : DifferentiableAt ℝ (fun y ↦ F (y, r)) x :=
        (hF.comp (contDiff_id.prodMk contDiff_const)).differentiable
          (by norm_num) x
      simp only [oddRadialTransform_zero, Nat.mul_zero, zero_add, pow_one]
      rw [fderiv_const_mul hd]
      simp
  | succ k ih =>
      let G : E × ℝ → ℝ := fun p ↦ fderiv ℝ (fun y ↦ F (y, p.2)) p.1 v
      let Ψ : E × ℝ → ℝ := fun p ↦
        (2 * k + 3 : ℝ) * F p + p.2 * deriv (fun s ↦ F (p.1, s)) p.2
      have hF₂ : ContDiff ℝ 2 F := hF.of_le (by norm_cast; omega)
      have hF₁ : ContDiff ℝ 1 F := hF₂.of_le (by norm_num)
      have hFr : ContDiff ℝ (k + 1)
          (fun p : E × ℝ ↦ deriv (fun s ↦ F (p.1, s)) p.2) := by
        apply contDiff_deriv_prod_snd
        simpa only [Nat.cast_add, Nat.cast_one] using hF
      have hG : ContDiff ℝ (k + 1) G := by
        apply contDiff_fderiv_prod_firstSlice
        simpa only [Nat.cast_add, Nat.cast_one] using hF
      have hΨ : ContDiff ℝ (k + 1) Ψ :=
        (contDiff_const.mul (hF.of_le (by norm_cast; omega))).add
          (contDiff_snd.mul hFr)
      have hΨderiv (s : ℝ) :
          fderiv ℝ (fun y ↦ Ψ (y, s)) x v =
            (2 * k + 3 : ℝ) * G (x, s) + s * deriv (fun t ↦ G (x, t)) s := by
        have hd : DifferentiableAt ℝ (fun y ↦ F (y, s)) x :=
          (hF₁.comp (contDiff_id.prodMk contDiff_const)).differentiable one_ne_zero x
        have hdr : DifferentiableAt ℝ (fun y ↦ deriv (fun t ↦ F (y, t)) s) x :=
          (hFr.comp (contDiff_id.prodMk contDiff_const)).differentiable
            (by norm_num) x
        dsimp only [Ψ]
        rw [fderiv_fun_add (hd.const_mul _) (hdr.const_mul _),
          fderiv_const_mul hd, fderiv_const_mul hdr]
        simp only [add_apply, smul_apply, smul_eq_mul]
        rw [fderiv_deriv_prod_comm hF₂]
      have he : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      have hrec :
          (fun y ↦ oddRadialTransform (k + 1)
            (fun s ↦ s ^ (2 * (k + 1) + 1) * F (y, s)) r) =
          (fun y ↦ oddRadialTransform k
            (fun s ↦ s ^ (2 * k + 1) * Ψ (y, s)) r) := by
        funext y
        simpa only [he, Ψ, Function.comp_def] using congrFun
          (oddRadialTransform_step k
            (hF₁.comp (contDiff_const.prodMk contDiff_id) :
              ContDiff ℝ 1 (fun s ↦ F (y, s)))) r
      rw [hrec, ih hΨ]
      simp_rw [hΨderiv]
      simpa only [he, G, Function.comp_def] using (congrFun
        (oddRadialTransform_step k
          ((hG.of_le (by norm_cast; omega)).comp (contDiff_const.prodMk contDiff_id) :
            ContDiff ℝ 1 (fun s ↦ G (x, s)))) r).symm

end PDE.Analysis
