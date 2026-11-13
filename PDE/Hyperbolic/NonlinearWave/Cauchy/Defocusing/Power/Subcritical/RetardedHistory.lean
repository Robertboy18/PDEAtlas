/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.LocalFreeField
public import PDE.Analysis.Integration.ParametricIntervalSmooth.Local
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Retaining a bounded past source when restarting the cone equation

The past part of the retarded integral is a C¹ free field at every later
anchor. Its bound depends only on the source amplitude and the elapsed time.
No bound on derivatives of the past source is needed.
-/

@[expose] public noncomputable section

open Set MeasureTheory PDE.Analysis
open WaveEquation.SmallData.Classical.LocalPower

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The three-dimensional retarded spherical kernel, in physical coordinates. -/
def retardedSourceKernel (F : ℝ × ℝ^3 → ℝ) (q : (ℝ × ℝ^3) × ℝ) : ℝ :=
  (q.1.1 - q.2) * unitSphereAverage 3 (fun y ↦ F (q.2, y)) q.1.2 (q.1.1 - q.2)

/-- A C¹ source gives a jointly C¹ spherical kernel, including zero age. -/
theorem contDiff_one_retardedSourceKernel {F : ℝ × ℝ^3 → ℝ}
    (hF : ContDiff ℝ 1 F) : ContDiff ℝ 1 (retardedSourceKernel F) := by
  have hc : ContDiff ℝ 1 (fun z : ((ℝ × ℝ^3) × ℝ) × ℝ^3 ↦
      F (z.1.2, z.1.1.2 + (z.1.1.1 - z.1.2) • z.2)) := hF.comp (contDiff_fst.snd.prodMk
      (contDiff_fst.fst.snd.add ((contDiff_fst.fst.fst.sub contDiff_fst.snd).smul contDiff_snd)))
  exact (contDiff_fst.fst.sub contDiff_snd).mul ((contDiff_integral_compact_parametrization
      (μ := (volume : Measure (ℝ^3)).toSphere) hc continuous_subtype_val).div_const _)

/-- All waves emitted before `a`, evaluated at time `a + p.1`. -/
def retardedHistory (a : ℝ) (F : ℝ × ℝ^3 → ℝ) (p : ℝ × ℝ^3) : ℝ :=
  ∫ s in (0 : ℝ)..a, retardedSourceKernel F ((a + p.1, p.2), s)

/-- The prescribed past becomes a C¹ free field for the future cone problem. -/
theorem contDiff_one_retardedHistory {F : ℝ × ℝ^3 → ℝ}
    (hF : ContDiff ℝ 1 F) (a : ℝ) : ContDiff ℝ 1 (retardedHistory a F) :=
  (contDiff_intervalIntegral (contDiff_one_retardedSourceKernel hF) 0 a).comp
    ((contDiff_const.add contDiff_fst).prodMk contDiff_snd)

/-- The past contribution is controlled by amplitude alone, uniformly in the
spatial center and throughout the next unit interval. -/
theorem norm_retardedHistory_le {F : ℝ × ℝ^3 → ℝ} {a M : ℝ} (ha : 0 ≤ a)
    (hbound : ∀ s ∈ Icc 0 a, ∀ x : ℝ^3, |F (s, x)| ≤ M) {p : ℝ × ℝ^3} (hp : p.1 ∈ Icc 0 1) :
    |retardedHistory a F p| ≤ a * (a + 1) * M := by
  have hkernel (s : ℝ) (hs : s ∈ Ioc 0 a) :
      ‖retardedSourceKernel F ((a + p.1, p.2), s)‖ ≤ (a + 1) * M := by
    have hage : 0 ≤ a + p.1 - s := by linarith [hs.2, hp.1]
    have hage' : a + p.1 - s ≤ a + 1 := by linarith [hs.1, hp.2]
    have havg : ‖unitSphereAverage 3 (fun y ↦ F (s, y)) p.2 (a + p.1 - s)‖ ≤ M := by
      unfold unitSphereAverage
      rw [norm_div, Real.norm_of_nonneg (unitSphereArea_pos (n := 3)).le]
      apply (div_le_iff₀ (unitSphereArea_pos (n := 3))).mpr
      exact norm_integral_le_of_norm_le_const
        (Filter.Eventually.of_forall fun θ ↦ by
          simpa only [Real.norm_eq_abs] using hbound s ⟨hs.1.le, hs.2⟩
            (p.2 + (a + p.1 - s) • (θ : ℝ^3)))
    change ‖(a + p.1 - s) * unitSphereAverage 3 (fun y ↦ F (s, y)) p.2 (a + p.1 - s)‖ ≤ _
    rw [norm_mul, Real.norm_of_nonneg hage]
    exact mul_le_mul hage' havg (norm_nonneg _) (by positivity)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := a) (fun s hs ↦ hkernel s (by
      simpa only [uIoc_of_le ha] using hs))
  simpa only [retardedHistory, Real.norm_eq_abs, sub_zero, abs_of_nonneg ha,
    mul_assoc, mul_comm a, mul_left_comm a] using hi

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
