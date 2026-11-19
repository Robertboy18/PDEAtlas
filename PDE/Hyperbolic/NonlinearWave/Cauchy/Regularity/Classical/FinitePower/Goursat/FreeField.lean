/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.DSlope
public import PDE.Analysis.Calculus.Radial.Lift.FiniteRegularity
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Radial
import CAS.ExactTactic

/-!
# Smooth radial free waves

The radial divided difference extends smoothly through the spatial origin and solves the three-
dimensional free wave equation.
-/

@[expose] public noncomputable section

section

open Set Filter PDE PDE.Analysis PDE.Common WaveEquation
open scoped ContDiff Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- The symmetric divided slope of a scalar profile, with radius first. -/
def radialFreeProfile (F : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  2 * dslope F (p.2 - p.1) (p.2 + p.1)

/-- The radial free field, including its regular value at the spatial axis. -/
def radialFreeField (F : ℝ → ℝ) (p : ℝ × ℝ^3) : ℝ :=
  radialFreeProfile F (‖p.2‖, p.1)

/-- Away from zero radius, the divided slope has the familiar quotient form. -/
theorem radialFreeProfile_eq_div (F : ℝ → ℝ) (t : ℝ) {r : ℝ} (hr : r ≠ 0) :
    radialFreeProfile F (r, t) = (F (t + r) - F (t - r)) / r := by
  have hne : t + r ≠ t - r := by intro h; apply hr; linarith
  simp only [radialFreeProfile, dslope_of_ne F hne, slope_def_field]
  generalize F (t + r) = A, F (t - r) = B
  cas using hr

/-- The scalar radial profile is even in its radius. -/
theorem radialFreeProfile_even (F : ℝ → ℝ) (r t : ℝ) :
    radialFreeProfile F (-r, t) = radialFreeProfile F (r, t) := by
  by_cases hr : r = 0
  · simp only [hr, neg_zero]
  have hne : t + r ≠ t - r := by intro h; apply hr; linarith
  simp only [radialFreeProfile, sub_neg_eq_add, ← sub_eq_add_neg,
    dslope_of_ne F hne, dslope_of_ne F hne.symm, slope_comm F (t + r)]

/-- A smooth scalar profile gives six derivatives of its symmetric divided slope. -/
theorem contDiff_six_radialFreeProfile {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ 6 (radialFreeProfile F) := by
  have hF7 : ContDiff ℝ 7 F := hF.of_le (by simp)
  have hd := contDiff_dslope_joint (n := 6) (F := fun q : ℝ × ℝ ↦ F q.2) (hF7.comp contDiff_snd)
  exact contDiff_const.mul (hd.comp ((contDiff_const (c := (0 : ℝ))).prodMk
    ((contDiff_snd.sub contDiff_fst).prodMk (contDiff_snd.add contDiff_fst))))

/-- The radial field is jointly C³, including at the spatial origin. -/
theorem contDiff_three_radialFreeField {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ 3 (radialFreeField F) := by
  have hlift : ContDiff ℝ 3 (fun q : ℝ^3 × ℝ ↦ radialFreeProfile F (‖q.1‖, q.2)) :=
    contDiff_norm_prod_of_even (E := ℝ^3) (F := ℝ) (G := ℝ) 3
      (f := radialFreeProfile F) (contDiff_six_radialFreeProfile hF) (radialFreeProfile_even F)
  change ContDiff ℝ 3 (fun p : ℝ × ℝ^3 ↦ radialFreeProfile F (‖p.2‖, p.1))
  exact hlift.comp (f := fun p : ℝ × ℝ^3 ↦ (p.2, p.1)) (contDiff_snd.prodMk contDiff_fst)

/-- The radial field solves the homogeneous physical wave equation at every point. -/
theorem waveOperator_radialFreeField {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (t : ℝ) (x : ℝ^3) :
    waveOperator (fun z : ℝ^4 ↦ radialFreeField F (timeSpaceContinuousLinearEquiv 3 z))
      (timeSpaceCons t x) = 0 := by
  let U : ℝ^4 → ℝ := fun z ↦ radialFreeField F (timeSpaceContinuousLinearEquiv 3 z)
  let W : Parameter → ℝ := fun p ↦ F (p.1 + 1) - F (p.2.1 - 1)
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by simp)
  have hW : ContDiff ℝ 2 W := (hF2.comp (contDiff_fst.add contDiff_const)).sub
      (hF2.comp (contDiff_snd.fst.sub contDiff_const))
  have hU : ContDiff ℝ 2 U :=
    ((contDiff_three_radialFreeField hF).of_le (by norm_num)).comp
      (timeSpaceContinuousLinearEquiv 3).contDiff
  have heq (z : ℝ^4) (hz : spatialPart z ≠ 0) : U z = radialGoursatField W 0 z := by
    rw [show U z = radialFreeProfile F (‖spatialPart z‖, time z) by rfl,
      radialFreeProfile_eq_div F _ (norm_ne_zero_iff.mpr hz)]
    simp only [radialGoursatField, W, sub_add_cancel, add_sub_cancel_right]
  have haway (y : ℝ^3) (hy : y ≠ 0) : waveOperator U (timeSpaceCons t y) = 0 := by
    have hnear : U =ᶠ[𝓝 (timeSpaceCons t y)] radialGoursatField W 0 := by
      have hsp : Continuous (spatialPart : ℝ^4 → ℝ^3) := (spatialPartCLM 3).continuous
      filter_upwards [hsp.continuousAt.eventually
        (isOpen_compl_singleton.mem_nhds (by simpa using hy))] with z hz
      exact heq z hz
    rw [waveOperator_congr_nhds hnear, waveOperator_radialGoursatField hW 0 t hy]
    have hfirst : (fun b : ℝ ↦ deriv (fun a : ℝ ↦ W (a, b, 0)) (t + ‖y‖ - 1)) =
        fun _ ↦ deriv F (t + ‖y‖ - 1 + 1) := by
      funext b
      simpa only [Function.comp_def, id_eq, mul_one, W] using
        (((hF2.differentiable (by norm_num) _).hasDerivAt.comp _
        ((hasDerivAt_id (t + ‖y‖ - 1)).add_const 1)).sub_const (F (b - 1))).deriv
    rw [hfirst, deriv_const, mul_zero]
  have hc : Continuous (fun y : ℝ^3 ↦ waveOperator U (timeSpaceCons t y)) :=
    (continuous_waveOperator_of_contDiff_two hU).comp
      ((timeSpaceContinuousLinearEquiv 3).symm.continuous.comp
        (continuous_const.prodMk continuous_id))
  have hall := Continuous.ext_on (dense_compl_singleton (0 : ℝ^3)) hc
    (continuous_const (y := (0 : ℝ))) (fun y hy ↦ haway y hy)
  exact congrFun hall x

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end

section

open PDE.Analysis
open scoped ContDiff

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- The symmetric divided-slope profile is smooth through zero radius. -/
theorem contDiff_infty_radialFreeProfile {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (radialFreeProfile F) := by
  have hF' : ContDiff ℝ ((∞ : ℕ∞ω) + 1) (fun q : ℝ × ℝ ↦ F q.2) := by
    simpa [Function.comp_def] using hF.comp (contDiff_snd (𝕜 := ℝ))
  have hd := contDiff_dslope_joint (n := (⊤ : ℕ∞)) hF'
  exact contDiff_const.mul (hd.comp ((contDiff_const (c := (0 : ℝ))).prodMk
    ((contDiff_snd.sub contDiff_fst).prodMk (contDiff_snd.add contDiff_fst))))

/-- The same radial free field is jointly smooth, including at the spatial axis. -/
theorem contDiff_infty_radialFreeField {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (radialFreeField F) := by
  refine contDiff_infty.mpr fun k ↦ ?_
  have hlift : ContDiff ℝ k (fun q : ℝ^3 × ℝ ↦ radialFreeProfile F (‖q.1‖, q.2)) :=
    contDiff_norm_prod_of_even (E := ℝ^3) (F := ℝ) (G := ℝ) k
      (f := radialFreeProfile F) (contDiff_infty.mp (contDiff_infty_radialFreeProfile hF) (2 * k))
      (radialFreeProfile_even F)
  exact hlift.comp (f := fun p : ℝ × ℝ^3 ↦ (p.2, p.1)) (contDiff_snd.prodMk contDiff_fst)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end
