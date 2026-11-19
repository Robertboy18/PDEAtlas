/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SphericalMean.Regularity
public import PDE.Analysis.Integration.ParametricIntervalSmooth.Local
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Differentiating compact spatial tests of the retarded kernel

A continuous source coefficient can be integrated against a twice continuously
differentiable wave test. Both age derivatives fall on the test, while the
source time remains an undifferentiated integration index. The second derivative
retains the instantaneous source pairing at the moving endpoint.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory PDE.Analysis
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

private theorem hasDerivAt_retarded_scalar {K D : ℝ × ℝ → ℝ} (hK : Continuous K) (hD : Continuous D)
    (hd : ∀ s r, HasDerivAt (fun a ↦ K (s, a)) (D (s, r)) r) (t : ℝ) :
    HasDerivAt (fun a ↦ ∫ s in (0 : ℝ)..a, K (s, a - s)) (K (t, 0) + ∫ s in (0 : ℝ)..t,
      D (s, t - s)) t := by
  have h := hasDerivAt_intervalIntegral_moving_right_of_continuousOn
    (U := univ) (F := fun a s ↦ K (s, a - s)) (D := fun a s ↦ D (s, a - s))
    (L := id) (a := 0) (lo := -|t| - 1) (hi := |t| + 1)
    isOpen_univ (mem_univ t) (by constructor <;> linarith [abs_nonneg t])
    (by change -|t| - 1 < t ∧ t < |t| + 1
        constructor <;> linarith [neg_abs_le t, le_abs_self t])
    (hK.comp (by fun_prop)).continuousOn (hD.comp (by fun_prop)).continuousOn
    (fun a _ s _ ↦ by
      simpa only [Function.comp_def, id_eq, mul_one] using
        (hd s (a - s)).comp a ((hasDerivAt_id a).sub_const s)) (hasDerivAt_id t)
  simpa only [id_eq, sub_self, one_mul] using h

private theorem hasDerivAt_compact_integral {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] {μ : Measure Y} [IsFiniteMeasure μ]
    {f d : ℝ → Y → ℝ} (hf : Continuous f.uncurry) (hd : Continuous d.uncurry)
    (hderiv : ∀ r y, HasDerivAt (fun a ↦ f a y) (d r y) r) (r : ℝ) :
    HasDerivAt (fun a ↦ ∫ y, f a y ∂μ) (∫ y, d r y ∂μ) r := by
  let D : ℝ → Y → ℝ →L[ℝ] ℝ := fun a y ↦ ContinuousLinearMap.toSpanSingleton ℝ (d a y)
  have hD : Continuous D.uncurry := (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp hd
  have h := hasFDerivAt_integral_of_compact (μ := μ) hf hD (fun a y ↦ (hderiv a y).hasFDerivAt) r
  apply h.hasDerivAt.congr_deriv
  rw [ContinuousLinearMap.integral_apply]
  · simp only [D, ContinuousLinearMap.toSpanSingleton_apply_one]
  · exact (hD.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (fun _ _ ↦ mem_univ _))

/-- Integrating a continuously weighted family of twice differentiable age
kernels gives the expected second retarded derivative. Neither the coefficient
nor the compact index requires a derivative. -/
theorem hasDerivAt_deriv_retarded_compact_pairing {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] {μ : Measure Y} [IsFiniteMeasure μ] {c : ℝ × Y → ℝ}
    {K D E : Y × ℝ → ℝ} (hc : Continuous c) (hK : Continuous K) (hD : Continuous D)
    (hE : Continuous E) (hd : ∀ y r, HasDerivAt (fun a ↦ K (y, a)) (D (y, r)) r)
    (he : ∀ y r, HasDerivAt (fun a ↦ D (y, a)) (E (y, r)) r) (hz : ∀ y, K (y, 0) = 0) (t : ℝ) :
    HasDerivAt (deriv (fun a ↦ ∫ s in (0 : ℝ)..a, ∫ y, c (s, y) * K (y, a - s) ∂μ))
      ((∫ y, c (t, y) * D (y, 0) ∂μ) + ∫ s in (0 : ℝ)..t, ∫ y, c (s, y) * E (y, t - s) ∂μ) t := by
  let A : ℝ × ℝ → ℝ := fun p ↦ ∫ y, c (p.1, y) * K (y, p.2) ∂μ
  let B : ℝ × ℝ → ℝ := fun p ↦ ∫ y, c (p.1, y) * D (y, p.2) ∂μ
  let C : ℝ × ℝ → ℝ := fun p ↦ ∫ y, c (p.1, y) * E (y, p.2) ∂μ
  have hA : Continuous A := continuous_integral_of_compact
    ((hc.comp (by fun_prop)).mul (hK.comp (by fun_prop)))
  have hB : Continuous B := continuous_integral_of_compact
    ((hc.comp (by fun_prop)).mul (hD.comp (by fun_prop)))
  have hC : Continuous C := continuous_integral_of_compact
    ((hc.comp (by fun_prop)).mul (hE.comp (by fun_prop)))
  have hAB (s r : ℝ) : HasDerivAt (fun a ↦ A (s, a)) (B (s, r)) r := by
    exact hasDerivAt_compact_integral (μ := μ) (f := fun b y ↦ c (s, y) * K (y, b))
      (d := fun b y ↦ c (s, y) * D (y, b))
      ((hc.comp (by fun_prop)).mul (hK.comp (by fun_prop)))
      ((hc.comp (by fun_prop)).mul (hD.comp (by fun_prop)))
      (fun b y ↦ (hd y b).const_mul (c (s, y))) r
  have hBC (s r : ℝ) : HasDerivAt (fun a ↦ B (s, a)) (C (s, r)) r := by
    exact hasDerivAt_compact_integral (μ := μ) (f := fun b y ↦ c (s, y) * D (y, b))
      (d := fun b y ↦ c (s, y) * E (y, b))
      ((hc.comp (by fun_prop)).mul (hD.comp (by fun_prop)))
      ((hc.comp (by fun_prop)).mul (hE.comp (by fun_prop)))
      (fun b y ↦ (he y b).const_mul (c (s, y))) r
  have hfirst : deriv (fun a ↦ ∫ s in (0 : ℝ)..a, A (s, a - s)) =
      fun a ↦ ∫ s in (0 : ℝ)..a, B (s, a - s) := by
    funext a
    simpa only [A, hz, mul_zero, integral_zero, zero_add] using
      (hasDerivAt_retarded_scalar hA hB hAB a).deriv
  change HasDerivAt (deriv (fun a ↦ ∫ s in (0 : ℝ)..a, A (s, a - s))) _ t
  rw [hfirst]
  exact hasDerivAt_retarded_scalar hB hC hBC t


/-- The compactly tested Kirchhoff kernel satisfies the scalar weak wave
identity. Only the spatial test has two derivatives; the source coefficient
is merely continuous in its time and compact spatial index. -/
theorem hasDerivAt_deriv_retarded_spherical_pairing {Y : Type*} [TopologicalSpace Y]
    [CompactSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] {μ : Measure Y}
    [IsFiniteMeasure μ] {c : ℝ × Y → ℝ} (hc : Continuous c) {a : Y → ℝ^3} (ha : Continuous a)
    {φ : ℝ^3 → ℝ} (hφ : ContDiff ℝ 2 φ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (deriv (fun b ↦ ∫ s in (0 : ℝ)..b,
      ∫ y, c (s, y) * ((b - s) * unitSphereAverage 3 φ (a y) (b - s)) ∂μ))
      ((∫ y, c (t, y) * φ (a y) ∂μ) +
        ∫ s in (0 : ℝ)..t,
          ∫ y, c (s, y) * ((t - s) * unitSphereAverage 3 (laplacian φ) (a y) (t - s)) ∂μ)
      t := by
  let K : ℝ^3 × ℝ → ℝ := fun p ↦ p.2 * unitSphereAverage 3 φ p.1 p.2
  let D : ℝ^3 × ℝ → ℝ := fun p ↦ fderiv ℝ K p (0, 1)
  let E : ℝ^3 × ℝ → ℝ := fun p ↦ fderiv ℝ D p (0, 1)
  have hK : ContDiff ℝ 2 K := contDiff_snd.mul (contDiff_unitSphereAverage hφ)
  have hD : ContDiff ℝ 1 D :=
    (hK.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hE : Continuous E := (hD.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hd (x : ℝ^3) (r : ℝ) : HasDerivAt (fun b ↦ K (x, b)) (D (x, r)) r :=
    ((hK.differentiable (by norm_num) (x, r)).hasFDerivAt).comp_hasDerivAt r
      ((hasDerivAt_const r x).prodMk (hasDerivAt_id r))
  have he (x : ℝ^3) (r : ℝ) : HasDerivAt (fun b ↦ D (x, b)) (E (x, r)) r :=
    ((hD.differentiable one_ne_zero (x, r)).hasFDerivAt).comp_hasDerivAt r
      ((hasDerivAt_const r x).prodMk (hasDerivAt_id r))
  have hDzero (x : ℝ^3) : D (x, 0) = φ x := by
    have hp := ((hasDerivAt_id (0 : ℝ)).fun_mul
      (hasDerivAt_unitSphereAverage φ x 0 (hφ.of_le (by norm_num)))).deriv
    simpa only [K, (hd x 0).deriv, id_eq, one_mul, zero_mul, add_zero,
      unitSphereAverage_zero] using hp
  have hEwave (x : ℝ^3) {r : ℝ} (hr : 0 < r) :
      E (x, r) = r * unitSphereAverage 3 (laplacian φ) x r := by
    have hfirst : deriv (fun b ↦ K (x, b)) = fun b ↦ D (x, b) := funext (fun b ↦ (hd x b).deriv)
    have hw := secondDeriv_radius_mul_unitSphereAverage hφ x hr
    change deriv (deriv (fun b ↦ K (x, b))) r = _ at hw
    rw [hfirst, (he x r).deriv] at hw
    exact hw
  have h := hasDerivAt_deriv_retarded_compact_pairing (μ := μ) (K := fun p : Y × ℝ ↦ K (a p.1, p.2))
    (D := fun p : Y × ℝ ↦ D (a p.1, p.2)) (E := fun p : Y × ℝ ↦ E (a p.1, p.2)) hc
    (hK.continuous.comp (ha.comp continuous_fst |>.prodMk continuous_snd))
    (hD.continuous.comp (ha.comp continuous_fst |>.prodMk continuous_snd))
    (hE.comp (ha.comp continuous_fst |>.prodMk continuous_snd))
    (fun y r ↦ hd (a y) r) (fun y r ↦ he (a y) r) (fun y ↦ by simp [K]) t
  simp only [hDzero] at h
  apply h.congr_deriv
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume t] with s hst hs
  have hs' : s ∈ Ioc 0 t := by simpa only [uIoc_of_le ht.le] using hs
  have hpos : 0 < t - s := sub_pos.mpr (lt_of_le_of_ne hs'.2 hst)
  apply integral_congr_ae
  filter_upwards [] with y
  rw [hEwave (a y) hpos]

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
