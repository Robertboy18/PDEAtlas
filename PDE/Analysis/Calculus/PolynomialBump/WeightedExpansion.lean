/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.PolynomialBump.Basic
import CAS.ExactTactic

/-!
# Polynomial ball profiles with variable radius and amplitude

The amplitude and squared radius are scalar functions of time. Their derivatives
give the temporal derivative, while the spatial slices use the stationary bump.
The formulas include the moving support sphere because the positive-part cube is C².
-/

@[expose] public noncomputable section

namespace PDE.Analysis

open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Local joint C² regularity of a polynomial profile with C² scalar parameters. -/
theorem contDiffAt_weightedPolynomialBallBump (z : E)
    {ρ w : ℝ → ℝ} {x : E} {t : ℝ}
    (hρ : ContDiffAt ℝ 2 ρ t) (hw : ContDiffAt ℝ 2 w t) :
    ContDiffAt ℝ 2 (fun p : E × ℝ ↦ w p.2 * (ρ p.2 - ‖p.1 - z‖ ^ 2)⁺ ^ 3) (x, t) := by
  have hgap : ContDiffAt ℝ 2 (fun p : E × ℝ ↦ ρ p.2 - ‖p.1 - z‖ ^ 2) (x, t) :=
    (hρ.comp (x, t) contDiffAt_snd).sub ((contDiffAt_fst.sub contDiffAt_const).norm_sq ℝ)
  exact (hw.comp (x, t) contDiffAt_snd).mul
    (contDiff_two_posPart_cube.contDiffAt.comp (x, t) hgap)

omit [InnerProductSpace ℝ E] in
/-- The temporal derivative depends only on the amplitude and squared-radius
derivatives; no spatial or mixed derivative is assumed. -/
theorem hasDerivAt_weightedPolynomialBallBump (z x : E)
    {ρ w : ℝ → ℝ} {ρ' w' t : ℝ} (hρ : HasDerivAt ρ ρ' t) (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s ↦ w s * (ρ s - ‖x - z‖ ^ 2)⁺ ^ 3)
      (w' * (ρ t - ‖x - z‖ ^ 2)⁺ ^ 3 +
        3 * ρ' * w t * (ρ t - ‖x - z‖ ^ 2)⁺ ^ 2) t := by
  have hcube := (hasDerivAt_posPart_pow 1 _).comp t (hρ.sub_const (‖x - z‖ ^ 2))
  convert! hw.mul hcube using 1
  simp only [Function.comp_apply, Nat.reduceAdd, Nat.cast_ofNat]
  cas

omit [InnerProductSpace ℝ E] in
/-- At a nonnegative squared radius, a weighted spatial slice is the
stationary polynomial bump multiplied by its amplitude. -/
theorem weightedPolynomialBallBump_eq_ballBump (z : E) {ρ w : ℝ} (hρ : 0 ≤ ρ) :
    (fun x ↦ w * (ρ - ‖x - z‖ ^ 2)⁺ ^ 3) =
      fun x ↦ w * polynomialBallBump z (√ρ) x := by
  funext x
  simp only [polynomialBallBump, Real.sq_sqrt hρ]

end PDE.Analysis
