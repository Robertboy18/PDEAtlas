/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.Prod.SliceDerivative
public import PDE.Analysis.Calculus.Radial.WeightedDerivative

/-!
# Finite regularity of weighted radial transforms

The recurrence replaces one weighted radial differentiation by
`F ↦ (2k+3) F + r ∂ᵣF`. It holds at zero as well as at nonzero radii.
Consequently `k` transforms lose at most `k` derivatives jointly in the radius
and arbitrary normed-space parameters. No regularity of an intermediate
transform is assumed.
-/

@[expose] public noncomputable section

namespace PDE.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A weighted radial transform of order `k` loses at most `k` joint
derivatives, including at radius zero. -/
theorem contDiff_oddRadialTransform_pow_mul
    (k s : ℕ) {F : E × ℝ → ℝ} (hF : ContDiff ℝ (k + s) F) :
    ContDiff ℝ s (fun p : E × ℝ ↦
      oddRadialTransform k (fun r ↦ r ^ (2 * k + 1) * F (p.1, r)) p.2) := by
  induction k generalizing F with
  | zero =>
      simpa using contDiff_snd.mul hF
  | succ k ih =>
      have hF₁ : ContDiff ℝ 1 F := hF.of_le (by norm_cast; omega)
      have hF₀ : ContDiff ℝ (k + s) F := hF.of_le (by norm_cast; omega)
      have hFr : ContDiff ℝ (k + s)
          (fun p : E × ℝ ↦ deriv (fun r ↦ F (p.1, r)) p.2) := by
        apply contDiff_deriv_prod_snd
        convert hF using 1
        push_cast
        ring
      have he : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
      have hrec :
          (fun p : E × ℝ ↦ oddRadialTransform (k + 1)
            (fun r ↦ r ^ (2 * (k + 1) + 1) * F (p.1, r)) p.2) =
          (fun p : E × ℝ ↦ oddRadialTransform k (fun r ↦
            r ^ (2 * k + 1) * ((2 * k + 3 : ℝ) * F (p.1, r) +
              r * deriv (fun s ↦ F (p.1, s)) r)) p.2) := by
        funext p
        simpa only [he, Function.comp_def] using congrFun
          (oddRadialTransform_step k
            (hF₁.comp (contDiff_const.prodMk contDiff_id) :
              ContDiff ℝ 1 (fun r ↦ F (p.1, r)))) p.2
      rw [hrec]
      exact ih ((contDiff_const.mul hF₀).add (contDiff_snd.mul hFr))

end PDE.Analysis
