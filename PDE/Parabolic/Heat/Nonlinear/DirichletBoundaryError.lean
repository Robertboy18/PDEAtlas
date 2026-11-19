/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.Nonlinear.DirichletMoment
import PDE.FDeriv.Laplacian.Congruence
import PDE.FDeriv.Laplacian.Continuity

/-!
# Signed testing near the lateral boundary

Convex eigenfunction truncations have a uniformly small negative Laplacian
error. Their positive error is confined to a shrinking boundary layer. Zero
lateral values control this layer uniformly on positive-time compact strips,
even when the initial and lateral traces disagree at their omitted corner.
The estimates do not require the solution to be nonnegative.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open PDE (laplacian)
open scoped Topology

namespace HeatEquation.Nonlinear

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Above the transition layer, truncation does not change the Laplacian. -/
theorem laplacian_dirichletTest_of_lt {w : ℝ^n → ℝ} {ε : ℝ}
    (hΩ : IsOpen Ω) (hε : 0 < ε) (hw : ContDiffOn ℝ 2 w Ω)
    {x : ℝ^n} (hx : x ∈ Ω) (hhigh : 2 * ε < w x) :
    laplacian (dirichletTest Ω w ε) x = laplacian w x := by
  have hd : deriv (convexTruncation ε) =ᶠ[𝓝 (w x)] fun _ ↦ (1 : ℝ) := by
    filter_upwards [eventually_gt_nhds hhigh] with r hr
    rw [(hasDerivAt_convexTruncation ε r).deriv]
    exact Real.smoothTransition.one_of_one_le ((one_le_div hε).mpr (by linarith))
  have hdd : deriv (deriv (convexTruncation ε)) (w x) = 0 := by
    rw [hd.deriv_eq, deriv_const]
  rw [EuclideanLaplacian.laplacian_congr_nhds (dirichletTest_eventuallyEq hΩ hx),
    PDE.laplacian_comp_real (contDiff_convexTruncation ε).contDiffAt
      (hw.contDiffAt (hΩ.mem_nhds hx)), hd.eq_of_nhds, hdd]
  simp

/-- The Laplacian of a compact C² test has zero total integral. -/
theorem integral_laplacian_eq_zero {φ : ℝ^n → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, laplacian φ x) = 0 := by
  have h := PDE.DistributionTheory.integral_mul_laplacian_eq (fun _ ↦ 1)
    hφ contDiff_const hc
  simpa only [PDE.laplacian_const, mul_zero, integral_zero, mul_one] using h.symm

/-- A continuous function vanishing on the zero set of a nonnegative continuous
weight is uniformly small where that weight is small on a compact set. -/
theorem exists_pos_weight_layer {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {w v : X → ℝ}
    (hw : ContinuousOn w K) (hv : ContinuousOn v K)
    (hn : ∀ x ∈ K, 0 ≤ w x) (hz : ∀ x ∈ K, w x = 0 → v x = 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε > 0, ∀ x ∈ K, w x ≤ 2 * ε → |v x| < η := by
  by_cases hne : K.Nonempty
  · let f : X → ℝ := fun x ↦ w x + max (η - |v x|) 0
    have hf : ContinuousOn f K := hw.add ((continuousOn_const.sub hv.abs).sup
      continuousOn_const)
    have hpos (x : X) (hx : x ∈ K) : 0 < f x := by
      by_cases h : w x = 0
      · simp [f, h, hz x hx h, hη.le, hη]
      · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hn x hx) (Ne.symm h))
          (le_max_right _ _)
    obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne hf
    refine ⟨f x / 4, div_pos (hpos x hx) (by norm_num), ?_⟩
    intro y hy hsmall
    by_contra h
    have hvy : η ≤ |v y| := le_of_not_gt h
    have hfy : f y = w y := by simp [f, max_eq_right (sub_nonpos.mpr hvy)]
    have hle : f x ≤ f y := hmin hy
    rw [hfy] at hle
    linarith [hpos x hx]
  · exact ⟨1, zero_lt_one, fun x hx ↦ (hne ⟨x, hx⟩).elim⟩

/-- The signed boundary error is controlled by a small negative part and small
values on the support of the positive part. -/
theorem integral_mul_ge_of_boundary_error {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {D v : X → ℝ} {δ η B A : ℝ}
    (hD : Integrable D μ)
    (hDv : Integrable (fun x ↦ D x * v x) μ)
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hB : 0 ≤ B)
    (hlow : ∀ᵐ x ∂μ, -δ ≤ D x)
    (hbound : ∀ᵐ x ∂μ, |v x| ≤ B)
    (hlayer : ∀ᵐ x ∂μ, D x ≤ 0 ∨ |v x| ≤ η)
    (hmass : ∫ x, D x ∂μ ≤ A) :
    -η * A - δ * (η + B) * μ.real univ ≤ ∫ x, D x * v x ∂μ := by
  have hp : ∀ᵐ x ∂μ, -η * (D x + δ) - δ * B ≤ D x * v x := by
    filter_upwards [hlow, hbound, hlayer] with x hx hb hl
    rcases abs_le.mp hb with ⟨hvb, hvB⟩
    rcases hl with hneg | hsmall
    · have h1 := mul_le_mul_of_nonpos_left hvB hneg
      have h2 := mul_le_mul_of_nonneg_right hx hB
      have h3 := mul_nonneg hη (show 0 ≤ D x + δ by linarith)
      nlinarith
    · have hsmall' := (abs_le.mp hsmall).1
      have h1 := mul_le_mul_of_nonneg_left hsmall' (show 0 ≤ D x + δ by linarith)
      have h2 := mul_le_mul_of_nonneg_left hvB hδ
      nlinarith
  have hi : Integrable (fun x ↦ -η * (D x + δ) - δ * B) μ :=
    ((hD.add (integrable_const δ)).const_mul (-η)).sub (integrable_const _)
  have h := integral_mono_ae hi hDv hp
  have hi₁ : Integrable (fun x ↦ -η * (D x + δ)) μ :=
    (hD.add (integrable_const δ)).const_mul (-η)
  have he := integral_sub hi₁ (integrable_const (δ * B))
  have ha := integral_add hD (integrable_const δ)
  rw [he, integral_const_mul, ha, integral_const, integral_const] at h
  simp only [smul_eq_mul] at h
  have hm := mul_le_mul_of_nonpos_left hmass (neg_nonpos.mpr hη)
  nlinarith

/-- A compact Dirichlet test has no more mass than its original weight. -/
theorem integral_dirichletTest_le {w : ℝ^n → ℝ} {ε : ℝ}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hε : 0 < ε)
    (hw : ContDiffOn ℝ 2 w Ω) (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 ≤ w x) :
    (∫ x, dirichletTest Ω w ε x) ≤ ∫ x in Ω, w x := by
  have hφ := contDiff_dirichletTest hΩ hε hw hwc hwzero
  have hs := tsupport_dirichletTest_subset hε hwc hwzero
  have heq : (∫ x in Ω, dirichletTest Ω w ε x) = ∫ x, dirichletTest Ω w ε x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h))
  rw [← heq]
  apply setIntegral_mono_on
    (hφ.continuous.continuousOn.integrableOn_of_subset_isCompact hb.isCompact_closure
      hΩ.measurableSet subset_closure hb.measure_lt_top.ne)
    (hwc.integrableOn_of_subset_isCompact hb.isCompact_closure
      hΩ.measurableSet subset_closure hb.measure_lt_top.ne) hΩ.measurableSet
  intro x hx
  simpa only [indicator_of_mem hx] using (dirichletTest_bounds (ε := ε) hwpos x).2

/-- Separate lateral traces suffice for the truncated Green pairing: no sign
or boundary derivative of the tested function is required. -/
theorem dirichletTest_laplacian_pairing_lower {w v : ℝ^n → ℝ} {ε lambda η B : ℝ}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hε : 0 < ε)
    (hlambda : 0 ≤ lambda) (hη : 0 ≤ η) (hB : 0 ≤ B)
    (hw : ContDiffOn ℝ 2 w Ω) (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 ≤ w x)
    (hunit : ∫ x in Ω, w x ≤ 1)
    (heigen : ∀ x ∈ Ω, laplacian w x = -lambda * w x)
    (hv : ContinuousOn v (closure Ω)) (hvB : ∀ x ∈ Ω, |v x| ≤ B)
    (hsmall : ∀ x ∈ Ω, w x ≤ 2 * ε → |v x| ≤ η) :
    -lambda * (∫ x, dirichletTest Ω w ε x * v x) - η * lambda -
        (2 * lambda * ε) * (η + B) * volume.real Ω ≤
      ∫ x, laplacian (dirichletTest Ω w ε) x * v x := by
  let φ := dirichletTest Ω w ε
  have hφ : ContDiff ℝ 2 φ := contDiff_dirichletTest hΩ hε hw hwc hwzero
  have hc : HasCompactSupport φ := hasCompactSupport_dirichletTest hb hε hwc hwzero
  have hs : tsupport φ ⊆ Ω := tsupport_dirichletTest_subset hε hwc hwzero
  have hint {f : ℝ^n → ℝ} (hf : ContinuousOn f (closure Ω)) : IntegrableOn f Ω :=
    hf.integrableOn_of_subset_isCompact hb.isCompact_closure hΩ.measurableSet
      subset_closure hb.measure_lt_top.ne
  have hout {x : ℝ^n} (hx : x ∉ Ω) : φ x = 0 ∧ laplacian φ x = 0 :=
    ⟨image_eq_zero_of_notMem_tsupport fun h ↦ hx (hs h),
      EuclideanLaplacian.laplacian_eq_zero_of_notMem_tsupport fun h ↦ hx (hs h)⟩
  have hφeq : (∫ x in Ω, φ x) = ∫ x, φ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ (hout hx).1
  have hLeq : (∫ x in Ω, laplacian φ x) = ∫ x, laplacian φ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ (hout hx).2
  have hφveq : (∫ x in Ω, φ x * v x) = ∫ x, φ x * v x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by rw [(hout hx).1, zero_mul]
  have hLveq : (∫ x in Ω, laplacian φ x * v x) = ∫ x, laplacian φ x * v x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by rw [(hout hx).2, zero_mul]
  let D : ℝ^n → ℝ := fun x ↦ laplacian φ x + lambda * φ x
  have hDc : Continuous D := hφ.continuous_coordinate_laplacian.add
    (continuous_const.mul hφ.continuous)
  have hmass : ∫ x in Ω, D x ≤ lambda := by
    change (∫ x in Ω, laplacian φ x + lambda * φ x) ≤ lambda
    rw [integral_add (hint hφ.continuous_coordinate_laplacian.continuousOn)
      ((hint hφ.continuous.continuousOn).const_mul lambda), integral_const_mul,
      hLeq, integral_laplacian_eq_zero hφ hc, zero_add, hφeq]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      ((integral_dirichletTest_le hΩ hb hε hw hwc hwzero hwpos).trans hunit) hlambda
  have : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using (hb.measure_lt_top (μ := volume))⟩
  have h := integral_mul_ge_of_boundary_error (hint hDc.continuousOn)
    (hint (hDc.continuousOn.mul hv)) (by positivity : 0 ≤ 2 * lambda * ε) hη hB
    (by
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      have := neg_mul_dirichletTest_le_laplacian hΩ hε hlambda hw hwc hwzero
        hwpos heigen x
      change -(2 * lambda * ε) ≤ laplacian φ x + lambda * φ x
      linarith)
    ((ae_restrict_mem hΩ.measurableSet).mono hvB)
    (by
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      by_cases hh : w x ≤ 2 * ε
      · exact Or.inr (hsmall x hx hh)
      · left
        change laplacian φ x + lambda * φ x ≤ 0
        rw [laplacian_dirichletTest_of_lt hΩ hε hw hx (lt_of_not_ge hh), heigen x hx]
        have hle : φ x ≤ w x := by
          simpa only [indicator_of_mem hx] using (dirichletTest_bounds (ε := ε) hwpos x).2
        nlinarith [mul_le_mul_of_nonneg_left hle hlambda]) hmass
  have hid : (∫ x in Ω, D x * v x) =
      (∫ x, laplacian φ x * v x) + lambda * (∫ x, φ x * v x) := by
    simp only [D, add_mul, mul_assoc]
    have hiL : IntegrableOn (fun x ↦ laplacian φ x * v x) Ω :=
      hint (hφ.continuous_coordinate_laplacian.continuousOn.mul hv)
    have hiφ : IntegrableOn (fun x ↦ φ x * v x) Ω :=
      hint (hφ.continuous.continuousOn.mul hv)
    rw [integral_add hiL (hiφ.const_mul lambda), integral_const_mul, hLveq, hφveq]
  rw [hid, show (volume.restrict Ω).real univ = volume.real Ω by simp] at h
  change -lambda * (∫ x, φ x * v x) - η * lambda -
    (2 * lambda * ε) * (η + B) * volume.real Ω ≤ _
  linarith

/-- The compact test approximates a signed weighted moment uniformly over
bounded spatial slices. -/
theorem abs_moment_sub_dirichletTest_le {w v : ℝ^n → ℝ} {ε B : ℝ}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hε : 0 < ε)
    (hw : ContDiffOn ℝ 2 w Ω) (hwc : ContinuousOn w (closure Ω))
    (hwzero : ∀ x ∈ frontier Ω, w x = 0) (hwpos : ∀ x ∈ Ω, 0 ≤ w x)
    (hv : ContinuousOn v (closure Ω)) (hvB : ∀ x ∈ Ω, |v x| ≤ B) :
    |(∫ x in Ω, w x * v x) - (∫ x, dirichletTest Ω w ε x * v x)| ≤
      2 * ε * B * volume.real Ω := by
  let φ := dirichletTest Ω w ε
  have hφ : ContDiff ℝ 2 φ := contDiff_dirichletTest hΩ hε hw hwc hwzero
  have hs : tsupport φ ⊆ Ω := tsupport_dirichletTest_subset hε hwc hwzero
  have hint {f : ℝ^n → ℝ} (hf : ContinuousOn f (closure Ω)) : IntegrableOn f Ω :=
    hf.integrableOn_of_subset_isCompact hb.isCompact_closure hΩ.measurableSet
      subset_closure hb.measure_lt_top.ne
  have heq : (∫ x in Ω, φ x * v x) = ∫ x, φ x * v x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hs h)), zero_mul]
  have : IsFiniteMeasure (volume.restrict Ω) := ⟨by simpa using (hb.measure_lt_top (μ := volume))⟩
  have h := norm_integral_le_of_norm_le_const (μ := volume.restrict Ω)
    (f := fun x ↦ (w x - φ x) * v x) (C := 2 * ε * B) (by
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      have hle : φ x ≤ w x := by
        simpa only [indicator_of_mem hx] using (dirichletTest_bounds (ε := ε) hwpos x).2
      have herror : w x - φ x ≤ 2 * ε := by
        linarith [sub_two_mul_le_dirichletTest hε hwpos hx]
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hle), Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (hvB x hx) (sub_nonneg.mpr hle)).trans
        (mul_le_mul_of_nonneg_right herror ((abs_nonneg (v x)).trans (hvB x hx))))
  simp only [sub_mul] at h
  have hiw : IntegrableOn (fun x ↦ w x * v x) Ω := hint (hwc.mul hv)
  have hiφ : IntegrableOn (fun x ↦ φ x * v x) Ω := hint (hφ.continuous.continuousOn.mul hv)
  rw [integral_sub hiw hiφ, heq] at h
  simpa only [Real.norm_eq_abs, Measure.real, Measure.restrict_apply_univ] using h


end HeatEquation.Nonlinear
