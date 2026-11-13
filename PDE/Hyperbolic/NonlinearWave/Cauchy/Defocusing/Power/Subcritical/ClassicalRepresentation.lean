/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.Representation
public import PDE.Hyperbolic.Models.Wave.Duhamel.OneDimension.Construction
import PDE.Hyperbolic.NonlinearWave.SmallData.StraussCritical.Representation
import PDE.Analysis.Integration.ParametricIntervalSmooth.Local
import PDE.FDeriv.PartialDeriv.Transforms
import CAS.ExactTactic

/-!
# Retarded representation of classical real-power waves

Spherical reduction and one-dimensional finite propagation identify the
forced wave. Differentiating the odd reduced profile at radius zero gives the
three-dimensional retarded formula. The candidate needs only C² regularity;
the real-power source is C¹ for every exponent greater than one.
-/

@[expose] public noncomputable section

open Set MeasureTheory Metric PDE PDE.Common PDE.Analysis WaveEquation
open WaveEquation.SmallData
open SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A C² one-dimensional forced wave with zero Cauchy data agrees with the
retarded field on a finite strip. No equation beyond the strip is needed. -/
theorem eq_dAlembertDuhamel_on_strip {v f : ℝ^2 → ℝ} (hv : ContDiff ℝ 2 v) (hf : ContDiff ℝ 1 f)
    {T : ℝ} (hT : 0 < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^1, waveOperator v (timeSpaceCons t x) = f (timeSpaceCons t x))
    (hzero : ∀ x : ℝ^1, v (timeSpaceCons 0 x) = 0)
    (hinitial : ∀ x : ℝ^1, (∂[0] v) (timeSpaceCons 0 x) = 0) (x : ℝ^1) :
    v (timeSpaceCons T x) = dAlembertDuhamelSolution f (timeSpaceCons T x) := by
  have hd := contDiff_two_dAlembertDuhamelSolution hf.contDiffOn
  have hw (y : ℝ^1) : EqOn (fun t ↦ waveOperator v (timeSpaceCons t y))
      (fun t ↦ f (timeSpaceCons t y)) (Icc 0 T) := by
    have hc : Continuous (fun t ↦ timeSpaceCons t y) :=
      (contDiff_timeSpaceCons_uncurry 1 (m := 1)).continuous.comp
      (continuous_id.prodMk continuous_const)
    simpa only [closure_Ioo hT.ne] using (show EqOn (fun t ↦ waveOperator v (timeSpaceCons t y))
        (fun t ↦ f (timeSpaceCons t y)) (Ioo 0 T) from fun t ht ↦ hwave t ht y).closure
        ((continuous_waveOperator_of_contDiff_two hv).comp hc) (hf.continuous.comp hc)
  have hz := eq_zero_on_closed_backwardCone (hv.sub hd) x
    (fun t ht y _ ↦ by
      have he := hw y ⟨ht.1, ht.2.le⟩
      dsimp only at he
      rw [waveOperator_sub hv.contDiffAt hd.contDiffAt, he,
        waveOperator_dAlembertDuhamelSolution hf.contDiffOn (by simpa using ht.1), sub_self])
    (fun y _ ↦ by simp only [hzero, dAlembertDuhamelSolution_initial, sub_self])
    (fun y _ ↦ by
      rw [partialDeriv_sub (hv.differentiable (by norm_num) _)
        (hd.differentiable (by norm_num) _), hinitial,
        partialDeriv_dAlembertDuhamelSolution_initial hf.contDiffOn, sub_self])
  exact sub_eq_zero.mp (hz T ⟨hT.le, le_rfl⟩ x (by simp))

private theorem hasDerivAt_intervalIntegral_of_continuous {F D : ℝ → ℝ → ℝ}
    (hF : Continuous F.uncurry) (hD : Continuous D.uncurry)
    (hd : ∀ r s, HasDerivAt (fun q ↦ F q s) (D r s) r) (a b r : ℝ) :
    HasDerivAt (fun q ↦ ∫ s in a..b, F q s) (∫ s in a..b, D r s) r := by
  let J (q s : ℝ) := ContinuousLinearMap.toSpanSingleton ℝ (D q s)
  have hJ : Continuous J.uncurry := (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp hD
  have he := hasFDerivAt_intervalIntegral_of_continuousOn (U := univ) (a := a) (b := b)
    (D := J) isOpen_univ hF.continuousOn hJ.continuousOn
    (fun q _ s _ ↦ (hd q s).hasFDerivAt) (mem_univ r)
  have hi : IntervalIntegrable (J r) volume a b :=
    (hJ.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  apply he.hasDerivAt.congr_deriv
  rw [ContinuousLinearMap.intervalIntegral_apply hi]
  simp only [J, ContinuousLinearMap.toSpanSingleton_apply_one]

/-- The spatial derivative at the center of an odd reduced retarded field is
its outgoing characteristic integral. -/
theorem deriv_dAlembertDuhamel_radius_zero {f : ℝ^2 → ℝ} (hf : ContDiff ℝ 1 f)
    (hodd : ∀ s, Function.Odd (fun r ↦ f (timeSpaceCons s (EuclideanSpace.single (0 : Fin 1) r))))
    {T : ℝ} (hT : 0 ≤ T) :
    deriv (fun r ↦ dAlembertDuhamelSolution f (timeSpaceCons T
      (EuclideanSpace.single (0 : Fin 1) r))) 0 = ∫ s in (0 : ℝ)..T,
      f (timeSpaceCons s (EuclideanSpace.single (0 : Fin 1) (T - s))) := by
  let H (s r : ℝ) := f (timeSpaceCons s (EuclideanSpace.single (0 : Fin 1) r))
  let L : ℝ →L[ℝ] ℝ^1 := ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single 0 1)
  have hL (r : ℝ) : L r = EuclideanSpace.single 0 r := by
    ext i
    fin_cases i
    simp [L]
  have hH : Continuous H.uncurry := by
    simpa only [Function.comp_def, Function.uncurry_def, H, hL] using
      hf.continuous.comp ((contDiff_timeSpaceCons_uncurry 1 (m := 1)).continuous.comp
        (continuous_fst.prodMk (L.continuous.comp continuous_snd)))
  let F (r s : ℝ) := dAlembertFormula (fun _ ↦ 0) (H s) r (T - s)
  let D (r s : ℝ) := (1 / 2 : ℝ) * (H s (r + (T - s)) - H s (r - (T - s)))
  have hF : Continuous F.uncurry := by
    have hc := (continuous_dAlembert_zero_displacement_family hH).comp (continuous_snd.prodMk
        ((contDiff_timeSpaceCons_uncurry 1 (m := 1)).continuous.comp
          (((continuous_const (y := T)).sub continuous_snd).prodMk
            (L.continuous.comp continuous_fst))))
    simpa only [Function.comp_def, Function.uncurry_def, Pi.sub_apply, F, hL, timeSpaceCons_zero,
      timeSpaceCons_single_one] using hc
  have hD : Continuous D.uncurry := continuous_const.mul ((hH.comp (continuous_snd.prodMk
        (continuous_fst.add (continuous_const.sub continuous_snd)))).sub
      (hH.comp (continuous_snd.prodMk (continuous_fst.sub (continuous_const.sub continuous_snd)))))
  have hd (r s : ℝ) : HasDerivAt (fun q ↦ F q s) (D r s) r := by
    have hc : Continuous (H s) := hH.comp (continuous_const.prodMk continuous_id)
    have hleft : HasDerivAt (fun q : ℝ ↦ q - (T - s)) 1 r := by cas
    have hright : HasDerivAt (fun q : ℝ ↦ q + (T - s)) 1 r := by cas
    have hint := (intervalIntegral.integral_hasFDerivAt
      (hc.intervalIntegrable (r - (T - s)) (r + (T - s)))
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter
      hc.continuousAt hc.continuousAt).comp_hasDerivAt r (hleft.prodMk hright)
    simpa [F, D, dAlembertFormula] using hint.const_mul (1 / 2 : ℝ)
  have he : (fun r ↦ dAlembertDuhamelSolution f
      (timeSpaceCons T (EuclideanSpace.single (0 : Fin 1) r))) =
      fun r ↦ ∫ s in (0 : ℝ)..T, F r s := by
    funext r
    rw [dAlembertDuhamelSolution_eq_double_integral _ hT]
    simp only [F, dAlembertFormula, add_zero, mul_zero, zero_add, H]
  rw [he, (hasDerivAt_intervalIntegral_of_continuous hF hD hd 0 T 0).deriv]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [D, zero_add, zero_sub, H]
  have ho := hodd s (T - s)
  dsimp only at ho
  rw [ho]
  ring

/-- Spherical reduction recovers the center value of a C² three-dimensional
wave from a C¹ forcing and zero Cauchy data. -/
theorem eq_characteristic_integral_of_zero_data {u f : ℝ^4 → ℝ} (hu : ContDiff ℝ 2 u)
    (hf : ContDiff ℝ 1 f) {T : ℝ} (hT : 0 < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) = f (timeSpaceCons t x))
    (hzero : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = 0) :
    u (timeSpaceCons T (0 : ℝ^3)) = ∫ s in (0 : ℝ)..T, (T - s) *
      waveSphericalMean f 0 s (T - s) := by
  have hrep (r : ℝ) := eq_dAlembertDuhamel_on_strip (contDiff_radiusMean hu)
    (contDiff_radiusMean hf) hT (x := EuclideanSpace.single (0 : Fin 1) r)
    (fun t ht x ↦ by
      have hx : EuclideanSpace.single (0 : Fin 1) (x 0) = x := by
        ext i
        fin_cases i
        simp
      simpa only [hx] using waveOperator_radiusMean hu hf.continuous (hwave t ht) (x 0))
    (fun x ↦ by
      simp only [radiusMean, timeSpaceCons_zero, waveSphericalMean, hzero,
        unitSphereAverage, integral_zero, zero_div, mul_zero])
    (fun x ↦ by
      rw [partialDeriv_radiusMean_initial hu hinitial]
      simp only [unitSphereAverage, integral_zero, zero_div, mul_zero])
  have hmean : ContDiff ℝ 1 (fun r ↦ waveSphericalMean u 0 T r) := (contDiff_unitSphereAverage
      ((hu.of_le (by norm_num)).comp (contDiff_timeSpaceCons_spatial 3 T))).comp
        (contDiff_const.prodMk contDiff_id)
  have hleft : HasDerivAt (fun r ↦ radiusMean u
      (timeSpaceCons T (EuclideanSpace.single (0 : Fin 1) r)))
      (u (timeSpaceCons T (0 : ℝ^3))) 0 := by
    have hd := (hasDerivAt_id (0 : ℝ)).mul (hmean.differentiable one_ne_zero 0).hasDerivAt
    change HasDerivAt (fun r ↦ r * waveSphericalMean u 0 T r) _ 0 at hd
    simpa only [radiusMean, timeSpaceCons_zero, timeSpaceCons_single_one,
      waveSphericalMean_zero, id_eq, zero_mul, one_mul, add_zero] using hd
  rw [← hleft.deriv, funext hrep,
    deriv_dAlembertDuhamel_radius_zero (contDiff_radiusMean hf) (radiusMean_odd f) hT.le]
  simp only [radiusMean, timeSpaceCons_zero, timeSpaceCons_single_one]

/-- A finite-strip C² wave with zero Cauchy data has the retarded ball formula
for every C¹ forcing. The argument uses no second derivative of the forcing. -/
theorem eq_retarded_ball_of_zero_data {u f : ℝ^4 → ℝ} (hu : ContDiff ℝ 2 u) (hf : ContDiff ℝ 1 f)
    {T : ℝ} (hT : 0 < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) = f (timeSpaceCons t x))
    (hzero : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = 0) (c : ℝ^3) :
    u (timeSpaceCons T c) = (1 / (4 * Real.pi)) * ∫ y in ball c T,
      f (backwardConeGraph c T y) / ‖y - c‖ := by
  let a := timeSpaceCons 0 c
  have he (t : ℝ) (x : ℝ^3) : timeSpaceCons t x + a = timeSpaceCons t (c + x) := by
    ext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [a, add_comm]
  have hw (z : ℝ^4) : waveOperator (fun q ↦ u (q + a)) z = waveOperator u (z + a) := by
    simp only [waveOperator, partialDeriv_comp_add_right]
  have hrep := eq_characteristic_integral_of_zero_data
    (u := fun q ↦ u (q + a)) (f := fun q ↦ f (q + a))
    (hu.comp (contDiff_id.add contDiff_const)) (hf.comp (contDiff_id.add contDiff_const)) hT
    (fun t ht x ↦ by rw [hw, he]; exact hwave t ht (c + x))
    (fun x ↦ by rw [he]; exact hzero (c + x))
    (fun x ↦ by
      rw [partialDeriv_comp_add_right]
      change (∂[0] u) (timeSpaceCons 0 x + a) = 0
      rw [he]
      exact hinitial (c + x))
  rw [he, add_zero] at hrep
  rw [← oddDuhamelSolution_eq_retarded_ball hf.continuous c hT.le,
    oddDuhamelSolution_eq_integral 0 f c hT.le]
  simp only [Nat.doubleFactorial, Nat.cast_one, inv_one, one_mul,
    oddWavePotential_timeSpaceCons, oddSphericalProfile_zero]
  rw [hrep]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [waveSphericalMean, unitSphereAverage, he, zero_add]

/-- The C¹ real-power forcing gives the retarded representation of a
C² candidate on a finite forward strip. -/
theorem eq_retarded_ball_of_classical_power_solution {p : ℝ} (hp : 1 ≤ p) {u : ℝ^4 → ℝ}
    {g h : ℝ^3 → ℝ} (hu : ContDiff ℝ 2 u) (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hposition : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) (c : ℝ^3) {T : ℝ} (hT : 0 < T)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) +
      Real.signedPower p (u (timeSpaceCons t x)) = 0) :
    u (timeSpaceCons T c) = spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons T c) -
      (1 / (4 * Real.pi)) * ∫ y in ball c T, Real.signedPower p (retardedTrace u c T y) / ‖y -
      c‖ := by
  have hv := contDiff_two_kirchhoffFormula hg hh
  have hf := ((Real.contDiff_one_signedPower hp).comp (hu.of_le (by norm_num))).neg
  have he := eq_retarded_ball_of_zero_data (hu.sub hv) hf hT
    (fun t ht x ↦ by
      rw [waveOperator_sub hu.contDiffAt hv.contDiffAt,
        waveOperator_kirchhoffFormula hg hh (by simpa using ht.1), sub_zero]
      exact eq_neg_of_add_eq_zero_left (hwave t ht x))
    (fun x ↦ by simp only [hposition, kirchhoffFormula_initial_position, sub_self])
    (fun x ↦ by
      rw [partialDeriv_sub (hu.differentiable (by norm_num) _)
        (hv.differentiable (by norm_num) _), hinitial,
        partialDeriv_kirchhoffFormula_initial_velocity
          (hg.of_le (by norm_num)) (hh.of_le (by norm_num)), sub_self]) c
  simp only [neg_div, integral_neg, mul_neg, retardedTrace, Function.comp_apply] at he ⊢
  linarith

/-- The nonlinear representation uses any H¹ representative of the centered
trace. Translation and changes on null sets preserve the source integral. -/
theorem eq_centered_retarded_ball_of_classical_power_solution {p : ℝ} (hp : 1 ≤ p) {u : ℝ^4 → ℝ}
    {g h : ℝ^3 → ℝ} (hu : ContDiff ℝ 2 u) (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
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
  have he := eq_retarded_ball_of_classical_power_solution hp hu hg hh hposition hinitial c hT hwave
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
