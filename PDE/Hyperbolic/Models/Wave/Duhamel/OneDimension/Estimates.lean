/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.OneDimension.ContinuousDerivative
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import CAS.IntegrationTactic

/-!
# Bounds and causality for the one-dimensional retarded wave

The characteristic double integral is linear on continuous sources and only uses
forcing from the past time slab. A bounded source gains a quadratic time factor.
-/

@[expose] public noncomputable section

open PDE.Common PDE.Analysis MeasureTheory Set
open scoped Topology

namespace WaveEquation

/-- The characteristic integral gains one factor of the elapsed time. -/
theorem norm_dAlembert_zero_le {h : ℝ → ℝ} {C t : ℝ} (hh : ∀ y, ‖h y‖ ≤ C) (ht : 0 ≤ t) (x : ℝ) :
    ‖dAlembertFormula (fun _ ↦ 0) h x t‖ ≤ t * C := by
  simp only [dAlembertFormula, add_zero, mul_zero, zero_add, norm_mul]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := x - t) (b := x + t) (fun y _ ↦ hh y)
  have he : |x + t - (x - t)| = 2 * t := by
    rw [show x + t - (x - t) = 2 * t by cas, abs_of_nonneg (by positivity)]
  rw [he] at hi
  norm_num
  simp only [Real.norm_eq_abs] at hi
  nlinarith

/-- The retarded field is the oriented characteristic double integral. -/
theorem dAlembertDuhamelSolution_eq_doubleIntegral (f : ℝ^2 → ℝ) (p : ℝ^2) :
    dAlembertDuhamelSolution f p = ∫ s in (0 : ℝ)..p 0, dAlembertFormula (fun _ ↦ 0)
      (fun y ↦ f (timeSpaceCons (max 0 s) (EuclideanSpace.single (0 : Fin 1) y))) (p 1)
      (p 0 - s) := by
  simp [dAlembertDuhamelSolution, retardedWave, retardedIntegral, dAlembertSolution1D,
    splitSpaceTime, joinSpaceTime, spatialPart, PDE.time, timeSpaceCons, Matrix.vecTail]

/-- A scalar envelope for the source bounds the retarded integral. -/
theorem norm_dAlembertDuhamelSolution_le_integral
    {f : ℝ^2 → ℝ} {b : ℝ → ℝ} (hb : Continuous b) {p : ℝ^2} (hp : 0 ≤ p 0)
    (hbound : ∀ s ∈ Icc 0 (p 0), ∀ x : ℝ^1, ‖f (timeSpaceCons s x)‖ ≤ b s) :
    ‖dAlembertDuhamelSolution f p‖ ≤ ∫ s in (0 : ℝ)..p 0, (p 0 - s) * b s := by
  rw [dAlembertDuhamelSolution_eq_doubleIntegral]
  apply intervalIntegral.norm_integral_le_of_norm_le hp (Filter.Eventually.of_forall fun s hs ↦ ?_)
    ((continuous_const.sub continuous_id).mul hb |>.intervalIntegrable 0 (p 0))
  have hs0 : 0 ≤ s := hs.1.le
  simpa only [max_eq_right hs0, Pi.mul_apply, Pi.sub_apply, id_eq] using norm_dAlembert_zero_le
    (fun y ↦ hbound s ⟨hs0, hs.2⟩ (EuclideanSpace.single 0 y)) (sub_nonneg.mpr hs.2) (p 1)

/-- Bounded source values give a quadratic bound on each finite strip. -/
theorem norm_dAlembertDuhamelSolution_le {f : ℝ^2 → ℝ} {C : ℝ}
    (hbound : ∀ p, ‖f p‖ ≤ C) {p : ℝ^2} (hp : 0 ≤ p 0) :
    ‖dAlembertDuhamelSolution f p‖ ≤ (p 0) ^ 2 / 2 * C := by
  apply (norm_dAlembertDuhamelSolution_le_integral (b := fun _ ↦ C) continuous_const hp
    (fun s _ x ↦ hbound (timeSpaceCons s x))).trans_eq
  rw [intervalIntegral.integral_mul_const]
  have hi : (∫ s in (0 : ℝ)..p 0, p 0 - s) = (p 0) ^ 2 / 2 := by
    cas
  rw [hi]

/-- Joint continuity of the waves emitted by a continuous forcing term. -/
theorem continuous_dAlembert_source_kernel {f : ℝ^2 → ℝ} (hf : Continuous f) :
    Continuous (fun p : ℝ × ℝ^2 ↦ dAlembertFormula (fun _ ↦ 0)
      (fun y ↦ f (timeSpaceCons (max 0 p.1) (EuclideanSpace.single (0 : Fin 1) y)))
      (p.2 1) (p.2 0)) := by
  apply continuous_dAlembert_zero_displacement_family
    (h := fun s y ↦ f (timeSpaceCons (max 0 s) (EuclideanSpace.single (0 : Fin 1) y)))
  exact hf.comp ((contDiff_timeSpaceCons_uncurry 1 (m := 0)).continuous.comp
    ((continuous_const.max continuous_fst).prodMk ((PiLp.continuous_toLp 2 (fun _ : Fin 1 ↦ ℝ)).comp
        (continuous_pi fun i ↦ by
          fin_cases i
          simpa using (continuous_snd : Continuous (fun p : ℝ × ℝ ↦ p.2))))))

/-- The retarded field is linear on continuous sources. -/
theorem dAlembertDuhamelSolution_sub {f g : ℝ^2 → ℝ}
    (hf : Continuous f) (hg : Continuous g) (p : ℝ^2) :
    dAlembertDuhamelSolution (fun q ↦ f q - g q) p =
      dAlembertDuhamelSolution f p - dAlembertDuhamelSolution g p := by
  let L := (spaceTimeContinuousLinearEquiv 1).symm.toContinuousLinearMap
  have hc (k : ℝ^2 → ℝ) (hk : Continuous k) : Continuous (fun s : ℝ ↦ dAlembertFormula (fun _ ↦ 0)
        (fun y ↦ k (timeSpaceCons (max 0 s) (EuclideanSpace.single (0 : Fin 1) y)))
        (p 1) (p 0 - s)) := by
    simpa [Function.comp_def, L, joinSpaceTime, spatialPart, timeSpaceCons, Matrix.vecTail] using
      (continuous_dAlembert_source_kernel hk).comp (continuous_id.prodMk (L.continuous.comp
          ((continuous_const (y := spatialPart p)).prodMk
            (continuous_const (y := p 0) |>.sub continuous_id))))
  simp only [dAlembertDuhamelSolution_eq_doubleIntegral]
  rw [← intervalIntegral.integral_sub ((hc f hf).intervalIntegrable 0 (p 0))
    ((hc g hg).intervalIntegrable 0 (p 0))]
  refine intervalIntegral.integral_congr fun s _ ↦ ?_
  have he (k : ℝ^2 → ℝ) (hk : Continuous k) : Continuous (fun y : ℝ ↦
      k (timeSpaceCons (max 0 s) (EuclideanSpace.single (0 : Fin 1) y))) :=
    hk.comp ((contDiff_timeSpaceCons_uncurry 1 (m := 0)).continuous.comp (continuous_const.prodMk
        ((PiLp.continuous_toLp 2 (fun _ : Fin 1 ↦ ℝ)).comp
          (continuous_pi fun i ↦ by
            fin_cases i
            change Continuous (fun y : ℝ ↦ y)
            exact continuous_id))))
  simp only [dAlembertFormula, add_zero, mul_zero, zero_add]
  rw [intervalIntegral.integral_sub (he f hf |>.intervalIntegrable _ _)
    (he g hg |>.intervalIntegrable _ _), mul_sub]

/-- The retarded field only uses forcing on its past time slab. -/
theorem dAlembertDuhamelSolution_eq_of_eqOn_past {f g : ℝ^2 → ℝ} {p : ℝ^2} (hp : 0 ≤ p 0)
    (hfg : ∀ s ∈ Icc 0 (p 0), ∀ x : ℝ^1, f (timeSpaceCons s x) = g (timeSpaceCons s x)) :
    dAlembertDuhamelSolution f p = dAlembertDuhamelSolution g p := by
  rw [dAlembertDuhamelSolution_eq_doubleIntegral, dAlembertDuhamelSolution_eq_doubleIntegral]
  refine intervalIntegral.integral_congr fun s hs ↦ ?_
  have hs' : s ∈ Icc 0 (p 0) := by simpa only [uIcc_of_le hp] using hs
  have he : (fun y : ℝ ↦ f (timeSpaceCons (max 0 s) (EuclideanSpace.single (0 : Fin 1) y))) =
      (fun y : ℝ ↦ g (timeSpaceCons (max 0 s) (EuclideanSpace.single (0 : Fin 1) y))) := by
    funext y
    rw [max_eq_right hs'.1]
    exact hfg s hs' (EuclideanSpace.single 0 y)
  dsimp only
  rw [he]

end WaveEquation
