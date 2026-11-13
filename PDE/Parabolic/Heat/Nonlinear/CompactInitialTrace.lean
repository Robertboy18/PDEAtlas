/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Nonlinear.DirichletMoment
import PDE.Analysis.Calculus.CompactParametricIntegral.Interval
import PDE.FDeriv.Laplacian.Congruence
import PDE.FDeriv.Laplacian.Continuity
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Compact testing through the initial face

Interior initial continuity and the quadratic heat equation imply the integrated
compact-test identity starting at time zero. The reaction moment is continuous
and therefore integrable up to zero. No lateral values, sign, bound on the full
cylinder, or initial derivative trace are required.

The support of the test stays inside the spatial domain.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE (laplacian)
open scoped Topology

namespace HeatEquation.Nonlinear

variable {n : ℕ} {Ω : Set (ℝ^n)} {T : ℝ} {u : ℝ → ℝ^n → ℝ}

private theorem continuousOn_integral_of_fixed_support
    {K : Set (ℝ^n)} {F : ℝ → ℝ^n → ℝ}
    (hK : IsCompact K) (hc : ContinuousOn F.uncurry (Icc 0 T ×ˢ K))
    (hz : ∀ t x, x ∉ K → F t x = 0) :
    ContinuousOn (fun t ↦ ∫ x, F t x) (Icc 0 T) := by
  have hcont := PDE.continuousOn_setIntegral_of_compact_interval
    (μ := volume) (f := F) hK.isClosed.measurableSet hK.closure hK.measure_lt_top.ne
    (by simpa only [hK.isClosed.closure_eq] using hc)
  have heq (t : ℝ) : (∫ x in K, F t x) = ∫ x, F t x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (hz t)
  simpa only [heq] using hcont

/-- A compact interior moment is continuous at the initial face without any
control at the initial/lateral corner. -/
theorem continuousOn_compact_moment_of_initial_continuity
    (hc : ContinuousOn u.uncurry (Icc 0 T ×ˢ Ω))
    {φ : ℝ^n → ℝ} (hφ : Continuous φ) (hk : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) :
    ContinuousOn (fun t ↦ ∫ x, φ x * u t x) (Icc 0 T) := by
  apply continuousOn_integral_of_fixed_support hk
  · exact (hφ.comp continuous_snd).continuousOn.mul
      (hc.mono (prod_mono Subset.rfl hφΩ))
  · intro t x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- Differentiating a compact moment uses only interior smoothness and the
quadratic heat equation. The Laplacian is transferred to the test. -/
theorem hasDerivAt_compact_moment_of_interior_square_equation
    (hΩ : IsOpen Ω) (hs : ContDiffOn ℝ 2 u.uncurry (Ioo 0 T ×ˢ Ω))
    (heq : ∀ t ∈ Ioo 0 T, ∀ x ∈ Ω,
      deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2)
    {φ : ℝ^n → ℝ} (hφ : ContDiff ℝ 2 φ) (hk : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun r ↦ ∫ x, φ x * u r x)
      ((∫ x, laplacian φ x * u t x) + ∫ x, φ x * u t x ^ 2) t := by
  have hd (r : ℝ) (hr : r ∈ Ioo 0 T) (x : ℝ^n) (hx : x ∈ Ω) :
      HasDerivAt (fun s ↦ u s x) (fderiv ℝ u.uncurry (r, x) (1, 0)) r :=
    ((hs.contDiffAt ((isOpen_Ioo.prod hΩ).mem_nhds ⟨hr, hx⟩)).differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt r
        ((hasDerivAt_id r).prodMk (hasDerivAt_const r x))
  have hD : ContinuousOn (fun q ↦ fderiv ℝ u.uncurry q (1, 0)) (Ioo 0 T ×ˢ Ω) :=
    (hs.continuousOn_fderiv_of_isOpen (isOpen_Ioo.prod hΩ) (by norm_num)).clm_apply
      continuous_const.continuousOn
  let a := t / 2
  let b := (t + T) / 2
  have hab : Icc a b ⊆ Ioo 0 T := by
    apply Icc_subset_Ioo <;> dsimp [a, b] <;> linarith [ht.1, ht.2]
  have hkt : closure (tsupport φ) ⊆ Ω := by
    simpa only [(isClosed_tsupport φ).closure_eq] using hφΩ
  have hf := (hφ.continuous.comp continuous_snd).continuousOn.mul
    (hs.continuousOn.mono (prod_mono hab hkt))
  have hDf := (hφ.continuous.comp continuous_snd).continuousOn.mul
    (hD.mono (prod_mono hab hkt))
  have hder := PDE.hasDerivAt_setIntegral_of_compact_interval
    (μ := volume) (f := fun r x ↦ φ x * u r x)
    (D := fun r x ↦ φ x * fderiv ℝ u.uncurry (r, x) (1, 0))
    (isClosed_tsupport φ).measurableSet hk.closure hk.measure_lt_top.ne hf hDf
    (fun x hx r hr ↦ (hd r (hab (Ioo_subset_Icc_self hr)) x (hφΩ hx)).const_mul (φ x))
    (show t ∈ Ioo a b by dsimp [a, b]; constructor <;> linarith [ht.1, ht.2])
  have hzero {f : ℝ^n → ℝ} (x : ℝ^n) (hx : x ∉ tsupport φ) : φ x * f x = 0 := by
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hext (f : ℝ^n → ℝ) : (∫ x in tsupport φ, φ x * f x) = ∫ x, φ x * f x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  simp_rw [hext] at hder
  have hspace : ContDiffOn ℝ 2 (u t) Ω := fun x hx ↦
    ((hs.contDiffAt ((isOpen_Ioo.prod hΩ).mem_nhds ⟨ht, hx⟩)).comp x
      (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  have hlocal : ContinuousOn (u t) (tsupport φ) := hspace.continuousOn.mono hφΩ
  have hiR : Integrable (fun x ↦ φ x * u t x ^ 2) :=
    ((hφ.continuous.continuousOn.fun_mul (hlocal.fun_pow 2)).integrableOn_compact hk)
      |>.integrable_of_forall_notMem_eq_zero hzero
  have hcL : ContinuousOn (fun x ↦ φ x * laplacian (u t) x) (tsupport φ) := fun x hx ↦
    (hφ.continuous.continuousAt.mul (hspace.contDiffAt
      (hΩ.mem_nhds (hφΩ hx))).continuousAt_coordinate_laplacian).continuousWithinAt
  have hiL : Integrable (fun x ↦ φ x * laplacian (u t) x) :=
    (hcL.integrableOn_compact hk).integrable_of_forall_notMem_eq_zero hzero
  have hid : (∫ x, φ x * fderiv ℝ u.uncurry (t, x) (1, 0)) =
      (∫ x, φ x * laplacian (u t) x) + ∫ x, φ x * u t x ^ 2 := by
    rw [← integral_add hiL hiR]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport φ
    · have h := heq t ht x (hφΩ hx)
      rw [(hd t ht x (hφΩ hx)).deriv] at h
      linear_combination φ x * h
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul, add_zero]
  rwa [hid, integral_mul_laplacian_eq_interior hΩ hφ hk hφΩ hspace] at hder

/-- The compact quadratic reaction is integrable all the way to time zero.
This is derived from local initial continuity, not assumed as a source trace. -/
theorem intervalIntegrable_compact_square_of_initial_continuity
    (hc : ContinuousOn u.uncurry (Icc 0 T ×ˢ Ω))
    {φ : ℝ^n → ℝ} (hφ : Continuous φ) (hk : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) {t : ℝ} (ht : t ∈ Icc 0 T) :
    IntervalIntegrable (fun r ↦ ∫ x, φ x * u r x ^ 2) volume 0 t :=
  ((continuousOn_compact_moment_of_initial_continuity
      (u := fun r x ↦ u r x ^ 2) (T := T) (Ω := Ω)
      (hc.fun_pow 2) hφ hk hφΩ).mono
    (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1

/-- The exact compact-test heat identity reaches the initial face for signed
solutions with only separate initial continuity. No derivative at zero occurs. -/
theorem compact_moment_eq_initial_add_integral
    (hΩ : IsOpen Ω) (hc : ContinuousOn u.uncurry (Icc 0 T ×ˢ Ω))
    (hs : ContDiffOn ℝ 2 u.uncurry (Ioo 0 T ×ˢ Ω))
    (heq : ∀ t ∈ Ioo 0 T, ∀ x ∈ Ω,
      deriv (fun r ↦ u r x) t - laplacian (u t) x = u t x ^ 2)
    {g φ : ℝ^n → ℝ} (hg : ∀ x ∈ Ω, u 0 x = g x)
    (hφ : ContDiff ℝ 2 φ) (hk : HasCompactSupport φ) (hφΩ : tsupport φ ⊆ Ω)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    (∫ x, φ x * u t x) = (∫ x, φ x * g x) +
      ∫ r in 0..t, (∫ x, laplacian φ x * u r x) + ∫ x, φ x * u r x ^ 2 := by
  have hM := continuousOn_compact_moment_of_initial_continuity hc hφ.continuous hk hφΩ
  have hR := continuousOn_compact_moment_of_initial_continuity
      (u := fun r x ↦ u r x ^ 2) (T := T) (Ω := Ω)
      (hc.fun_pow 2)
    hφ.continuous hk hφΩ
  have hL : ContinuousOn (fun r ↦ ∫ x, laplacian φ x * u r x) (Icc 0 T) := by
    apply continuousOn_integral_of_fixed_support hk
    · exact (hφ.continuous_coordinate_laplacian.comp continuous_snd).continuousOn.mul
        (hc.mono (prod_mono Subset.rfl hφΩ))
    · intro r x hx
      rw [EuclideanLaplacian.laplacian_eq_zero_of_notMem_tsupport hx, zero_mul]
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (hM.mono hsub)
    (fun r hr ↦ hasDerivAt_compact_moment_of_interior_square_equation hΩ hs heq hφ hk
      hφΩ (show r ∈ Ioo 0 T from ⟨hr.1, hr.2.trans_le ht.2⟩))
    (((hL.add hR).mono hsub).intervalIntegrable_of_Icc ht.1)
  have hzero : (∫ x, φ x * u 0 x) = ∫ x, φ x * g x := by
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ tsupport φ
    · rw [hg x (hφΩ hx)]
    · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  rw [hzero] at hFTC
  linarith

end HeatEquation.Nonlinear
