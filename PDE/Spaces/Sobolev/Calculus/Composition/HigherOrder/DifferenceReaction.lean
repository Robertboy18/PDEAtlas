/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.CompactParametricIntegral.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A smooth reaction representing finite differences

Averaging the derivative along a segment factors a smooth finite-dimensional
reaction difference through a direction. Applying the Sobolev composition bound
to this smooth reaction will give a bound linear in the norm of the direction.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace SobolevSpace.Composition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative averaged between two endpoints, applied to a direction. -/
def averagedDerivative (f : E → ℝ) (a b w : E) : ℝ :=
  ∫ t : Icc (0 : ℝ) 1, fderiv ℝ f (b + (t : ℝ) • (a - b)) w
    ∂volume.comap Subtype.val

/-- The averaged derivative is smooth in both endpoints and the direction. -/
theorem contDiff_averagedDerivative {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin 3 → E ↦ averagedDerivative f (y 0) (y 1) (y 2)) := by
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  apply contDiff_infty.mpr
  intro k
  have hb (j : Fin 3) : ContDiff ℝ k (fun p : (Fin 3 → E) × ℝ ↦ p.1 j) :=
    (contDiff_apply ℝ (fun _ : Fin 3 ↦ E) j).comp contDiff_fst
  exact PDE.contDiff_integral_compact_parametrization
    (μ := volume.comap (Subtype.val : Icc (0 : ℝ) 1 → ℝ))
    (((hD.of_le (by simp)).comp
      ((hb 1).add (contDiff_snd.smul ((hb 0).sub (hb 1))))).clm_apply (hb 2))
    continuous_subtype_val

/-- A zero direction gives zero averaged derivative. -/
theorem averagedDerivative_zero (f : E → ℝ) (a b : E) :
    averagedDerivative f a b 0 = 0 := by
  simp [averagedDerivative]

/-- Scaling the direction scales the averaged derivative. -/
theorem averagedDerivative_smul (f : E → ℝ) (a b w : E) (c : ℝ) :
    averagedDerivative f a b (c • w) = c • averagedDerivative f a b w := by
  simp only [averagedDerivative, map_smul]
  exact integral_smul c _

/-- The fundamental theorem of calculus recovers the actual reaction difference. -/
theorem averagedDerivative_sub {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : E) :
    averagedDerivative f a b (a - b) = f a - f b := by
  rw [averagedDerivative, integral_subtype_comap measurableSet_Icc
    (fun t : ℝ ↦ fderiv ℝ f (b + t • (a - b)) (a - b)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have hd (t : ℝ) : HasDerivAt (fun s ↦ f (b + s • (a - b)))
      (fderiv ℝ f (b + t • (a - b)) (a - b)) t := by
    simpa only [Function.comp_def, Pi.add_apply, zero_add, one_smul, id_eq] using
      (hf.differentiable (by simp) (b + t • (a - b))).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t b).add ((hasDerivAt_id t).smul_const (a - b)))
  have hc : Continuous (fun t : ℝ ↦ fderiv ℝ f (b + t • (a - b)) (a - b)) :=
    ((hf.continuous_fderiv (by simp)).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t)
    (hc.intervalIntegrable 0 1)

/-- When the endpoints coincide, the average is the derivative at that point. -/
theorem averagedDerivative_self
    (f : E → ℝ) (a w : E) : averagedDerivative f a a w = fderiv ℝ f a w := by
  rw [averagedDerivative, integral_subtype_comap measurableSet_Icc
    (fun t : ℝ ↦ fderiv ℝ f (a + t • (a - a)) w)]
  simp

end SobolevSpace.Composition
