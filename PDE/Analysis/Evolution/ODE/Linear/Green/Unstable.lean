/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Green.Stable

/-!
# The unstable exponential Green integral

Time reversal turns the stable past integral into the negative future integral
for `u' - a • u = f`. This gives convergence, the growth estimate, and the
classical equation with the same spectral-gap constant.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The future Green integral, obtained by reversing the stable equation. -/
def futureExponentialIntegral (a : ℝ) (f : ℝ → E) (t : ℝ) : E :=
  -pastExponentialIntegral a (fun s ↦ f (-s)) (-t)

/-- The time-reversed construction is the usual negative tail integral. -/
theorem futureExponentialIntegral_eq_integral (a : ℝ) (f : ℝ → E) (t : ℝ) :
    futureExponentialIntegral a f t =
      -(Real.exp (a * t) • ∫ s in Ioi t, Real.exp (-(a * s)) • f s) := by
  have hi : (∫ s in Iic (-t), Real.exp (a * s) • f (-s)) =
      ∫ s in Ioi t, Real.exp (-(a * s)) • f s := by
    simpa only [mul_neg, neg_neg] using
      integral_comp_neg_Iic (-t) (fun s ↦ Real.exp (-(a * s)) • f s)
  simp only [futureExponentialIntegral, pastExponentialIntegral, mul_neg, neg_neg, hi]

/-- Time reversal preserves the exponential growth estimate. -/
theorem norm_futureExponentialIntegral_le {a η C : ℝ} {f : ℝ → E}
    (hη : 0 ≤ η) (ha : η < a) (hC : 0 ≤ C)
    (hbound : ∀ t, ‖f t‖ ≤ Real.exp (η * |t|) * C) (t : ℝ) :
    ‖futureExponentialIntegral a f t‖ ≤ Real.exp (η * |t|) * (C / (a - η)) := by
  simpa only [futureExponentialIntegral, norm_neg, abs_neg] using
    norm_pastExponentialIntegral_le hη ha hC
      (fun s ↦ by simpa only [abs_neg] using hbound (-s)) (-t)

/-- The future integral is a classical solution of the unstable
inhomogeneous linear equation. -/
theorem hasDerivAt_futureExponentialIntegral [CompleteSpace E]
    {a η C : ℝ} {f : ℝ → E}
    (hη : 0 ≤ η) (ha : η < a) (hC : 0 ≤ C) (hf : Continuous f)
    (hbound : ∀ t, ‖f t‖ ≤ Real.exp (η * |t|) * C) (t : ℝ) :
    HasDerivAt (futureExponentialIntegral a f)
      (f t + a • futureExponentialIntegral a f t) t := by
  have hp := hasDerivAt_pastExponentialIntegral hη ha hC
    (show Continuous (fun s ↦ f (-s)) from hf.comp continuous_neg)
    (fun s ↦ by simpa only [abs_neg] using hbound (-s)) (-t)
  simpa only [Function.comp_def, neg_neg, neg_one_smul, futureExponentialIntegral,
    smul_neg, sub_eq_add_neg] using! (hp.scomp t (hasDerivAt_id t).neg).neg

end PDE.Analysis.Evolution
