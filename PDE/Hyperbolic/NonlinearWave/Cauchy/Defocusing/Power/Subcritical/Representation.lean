/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RetardedTrace
public import PDE.Hyperbolic.Models.Wave.Duhamel.Kirchhoff
public import PDE.Analysis.Calculus.SignedPower.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The retarded ball representation

Radial coarea converts the constructed three-dimensional Duhamel wave into its inverse-distance ball
integral, the retarded potential (44) of Evans, §2.4.2. Integrability follows from continuity on the
compact cone and local integrability of the Newton kernel. For a solution of the power wave equation
this gives the integral identity (14) of §12.3.2, which is the representation behind (19) in the
proof of Theorem 3 of §12.3.3.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.2, equation (44); §12.3.2, equation (14); §12.3.3, proof
  of Theorem 3, equation (19).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric PDE PDE.Common PDE.Analysis WaveEquation
open SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The retarded inverse-distance integral of a continuous field is integrable
on every finite ball, without a support or decay condition. -/
theorem integrableOn_retarded_div_norm {f : ℝ^4 → ℝ} (hf : Continuous f) (c : ℝ^3) (T : ℝ) :
    IntegrableOn (fun y ↦ f (backwardConeGraph c T y) / ‖y - c‖) (ball c T) := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_backwardConeGraph c T
  have hc : Continuous (fun y : ℝ^3 ↦ f (backwardConeGraph c T (c + y))) :=
    (hf.comp hK.continuous).comp (continuous_const.add continuous_id)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℝ^3) T).image hc).isBounded.exists_norm_le
  have hi : IntegrableOn (fun y : ℝ^3 ↦ f (backwardConeGraph c T (c + y)) / ‖y‖)
      (ball 0 T) := by
    apply integrableOn_ball_of_norm_le_rpow (by simp) (α := 1) (C := C) (by norm_num)
    · filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      simp only [norm_div, Real.norm_of_nonneg (norm_nonneg _), Real.rpow_neg_one]
      exact (div_le_div_of_nonneg_right
        (hC _ (mem_image_of_mem _ (ball_subset_closedBall hy))) (norm_nonneg y)).trans_eq
          (div_eq_mul_inv C ‖y‖)
    · exact (hc.measurable.div continuous_norm.measurable).aestronglyMeasurable
  have hpre : (fun y : ℝ^3 ↦ c + y) ⁻¹' ball c T = ball 0 T := by
    ext y
    simp [mem_ball, dist_eq_norm]
  have hm := (measurePreserving_add_left (volume : Measure (ℝ^3)) c).integrableOn_comp_preimage
     (Homeomorph.addLeft c).measurableEmbedding
      (f := fun y ↦ f (backwardConeGraph c T y) / ‖y - c‖) (s := ball c T)
  apply hm.mp
  rw [hpre]
  change IntegrableOn (fun y : ℝ^3 ↦ f (backwardConeGraph c T (c + y)) / ‖c + y - c‖) (ball 0 T)
  simpa only [add_sub_cancel_left] using hi

/-- On a positive-radius spherical section, the kernel cancels one power of
the surface Jacobian. -/
theorem sphereIntegral_retarded_div_norm (f : ℝ^4 → ℝ) (c : ℝ^3) (T : ℝ) {r : ℝ} (hr : 0 < r) :
    sphereIntegral 3 (fun y ↦ f (backwardConeGraph c T y) / ‖y - c‖) c r =
      (4 * Real.pi) * (r * unitSphereAverage 3 (fun y ↦ f (timeSpaceCons (T - r) y)) c r) := by
  have hn (ω : sphere (0 : ℝ^3) 1) : ‖c + r • (ω : ℝ^3) - c‖ = r := by
    simp [norm_smul, mem_sphere_zero_iff_norm.mp ω.property, abs_of_pos hr]
  simp only [sphereIntegral, unitSphereAverage, unitSphereArea_three,
    backwardConeGraph, hn, abs_of_pos hr, integral_div]
  norm_num only
  field_simp

/-- The constructed Duhamel wave is exactly the inverse-distance retarded ball
integral. This change of variables only requires a continuous source. -/
theorem oddDuhamelSolution_eq_retarded_ball {f : ℝ^4 → ℝ} (hf : Continuous f) (c : ℝ^3) {T : ℝ}
    (hT : 0 ≤ T) :
    oddDuhamelSolution 0 f (timeSpaceCons T c) = (1 / (4 * Real.pi)) * ∫ y in ball c T,
      f (backwardConeGraph c T y) / ‖y - c‖ := by
  have hco := coarea_formula_ball (fun y ↦ f (backwardConeGraph c T y) / ‖y - c‖) c T
    (integrableOn_retarded_div_norm hf c T)
  change (∫ y in ball c T, f (backwardConeGraph c T y) / ‖y - c‖) = _ at hco
  rw [oddDuhamelSolution_eq_integral 0 f c hT]
  simp only [Nat.doubleFactorial, Nat.cast_one, inv_one, one_mul,
    oddWavePotential_timeSpaceCons, oddSphericalProfile_zero]
  rw [hco, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  have hs : (∫ r in (0 : ℝ)..T,
      sphereIntegral 3 (fun y ↦ f (backwardConeGraph c T y) / ‖y - c‖) c r) =
      (4 * Real.pi) * ∫ r in (0 : ℝ)..T,
        r * unitSphereAverage 3 (fun y ↦ f (timeSpaceCons (T - r) y)) c r := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with r hr
    rw [uIoc_of_le hT] at hr
    exact sphereIntegral_retarded_div_norm f c T hr.1
  rw [hs, ← mul_assoc, one_div_mul_cancel (by positivity : 4 * Real.pi ≠ 0), one_mul]
  have he := intervalIntegral.integral_comp_sub_left
    (fun s ↦ (T - s) * unitSphereAverage 3 (fun y ↦ f (timeSpaceCons s y)) c (T - s))
    (a := 0) (b := T) T
  simpa only [sub_self, sub_zero, sub_sub_cancel] using he.symm

/-- A smooth candidate satisfies the nonlinear retarded formula from its
PDE on the finite forward strip. Its wave operator supplies the C² forcing. -/
theorem eq_retarded_ball_of_power_solution {p : ℝ} {u : ℝ^4 → ℝ} {g h : ℝ^3 → ℝ}
    (hu : ContDiff ℝ 4 u) (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hposition : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) (c : ℝ^3) {T : ℝ} (hT : 0 < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) +
      Real.signedPower p (u (timeSpaceCons t x)) = 0) :
    u (timeSpaceCons T c) = spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons T c) -
      (1 / (4 * Real.pi)) * ∫ y in ball c T, Real.signedPower p (retardedTrace u c T y) / ‖y -
      c‖ := by
  have hsecond (i : Fin 4) : ContDiff ℝ 2 (∂[i] (∂[i] u)) := contDiff_partialDeriv_of_succ (m := 2)
      (contDiff_partialDeriv_of_succ (m := 3) hu)
  have hf : ContDiff ℝ 2 (waveOperator u) := (hsecond 0).sub (ContDiff.sum fun i _ ↦ hsecond i.succ)
  have he := eq_kirchhoffFormula_add_duhamel (hu.of_le (by norm_num)) hf.contDiffOn
    hg hh (fun _ _ _ ↦ rfl) hposition hinitial hT.le c
  rw [oddDuhamelSolution_eq_retarded_ball hf.continuous c hT.le] at he
  have hint : (∫ y in ball c T, waveOperator u (backwardConeGraph c T y) / ‖y - c‖) =
      -(∫ y in ball c T, Real.signedPower p (retardedTrace u c T y) / ‖y - c‖) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne c)] with y hy hne
    have hyT : ‖y - c‖ < T := by simpa only [mem_ball, dist_eq_norm] using hy
    have hyn : 0 < ‖y - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hpde := hwave (T - ‖y - c‖) ⟨sub_pos.mpr hyT, sub_lt_self T hyn⟩ y
    change waveOperator u (timeSpaceCons (T - ‖y - c‖) y) / ‖y - c‖ = _
    rw [eq_neg_of_add_eq_zero_left hpde, neg_div]
    rfl
  rw [hint, mul_neg, ← sub_eq_add_neg] at he
  exact he

/-- The nonlinear representation uses any H¹ representative of the centered
trace. Translation and changes on null sets preserve the source integral. -/
theorem eq_centered_retarded_ball_of_power_solution {p : ℝ} {u : ℝ^4 → ℝ} {g h : ℝ^3 → ℝ}
    (hu : ContDiff ℝ 4 u) (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hposition : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) (c : ℝ^3) {T : ℝ} (hT : 0 < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) +
      Real.signedPower p (u (timeSpaceCons t x)) = 0)
    (U : H¹(ball (0 : ℝ^3) T))
    (hbase : baseRepresentative U =ᵐ[domainMeasure 3 (ball 0 T)] fun x ↦
      u (timeSpaceCons (T - ‖x‖) (c + x))) :
    u (timeSpaceCons T c) = spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons T c) -
      (1 / (4 * Real.pi)) * ∫ x in ball (0 : ℝ^3) T, Real.signedPower p (baseRepresentative U x) /
      ‖x‖ := by
  have he := eq_retarded_ball_of_power_solution hu hg hh hposition hinitial c hT hwave
  have hpre : (fun x : ℝ^3 ↦ c + x) ⁻¹' ball c T = ball 0 T := by
    ext x
    simp only [mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]
  have hm : MeasurePreserving (fun x : ℝ^3 ↦ c + x)
      (volume.restrict (ball 0 T)) (volume.restrict (ball c T)) := by
    have hm := (measurePreserving_add_left (volume : Measure (ℝ^3)) c).restrict_preimage
      (s := ball c T) measurableSet_ball
    rwa [hpre] at hm
  have hint := hm.integral_comp (Homeomorph.addLeft c).measurableEmbedding
    (fun y ↦ Real.signedPower p (retardedTrace u c T y) / ‖y - c‖)
  simp only [retardedTrace, Function.comp_apply, backwardConeGraph, add_sub_cancel_left] at hint
  have hrep : (∫ x in ball (0 : ℝ^3) T, Real.signedPower p (baseRepresentative U x) / ‖x‖) =
      ∫ x in ball (0 : ℝ^3) T, Real.signedPower p (u (timeSpaceCons (T - ‖x‖) (c + x))) / ‖x‖ :=
    integral_congr_ae (hbase.mono fun x hx ↦ by
      dsimp only
      rw [hx])
  simp only [retardedTrace, Function.comp_apply, backwardConeGraph] at he
  rw [← hint, ← hrep] at he
  exact he

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
