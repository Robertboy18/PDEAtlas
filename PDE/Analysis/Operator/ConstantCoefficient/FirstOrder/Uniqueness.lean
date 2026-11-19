/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import PDE.Analysis.Fourier.GaussianRegularization.DecayLimit
public import PDE.Analysis.Fourier.GaussianRegularization.Inversion
public import PDE.Analysis.Operator.ConstantCoefficient.FirstOrder.Localization
public import PDE.Analysis.Operator.ConstantCoefficient.FirstOrder.Regularization

/-!
# Unrestricted classical uniqueness for constant first-order systems

A spatial cutoff reduces a classical solution to a compactly supported forced
system. Gaussian regularization and a distant-source estimate then recover its
value at the cutoff center. All bounds concern a fixed compact spacetime slab;
no temperateness or growth condition is imposed on the original solution.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Complex
open scoped Topology FourierTransform RealInnerProductSpace

namespace PDE.Analysis

open PDE.Analysis.Fourier

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

private theorem eq_zero_of_firstOrder_succ
    (A : Fin (n + 1) → E →L[ℂ] E) {u : ℝ × ℝ^(n + 1) → E} {T : ℝ}
    (hT : 0 ≤ T)
    (hu : ContDiffOn ℝ 1 u (Ioo 0 T ×ˢ univ))
    (huc : ContinuousOn u (Icc 0 T ×ˢ univ))
    (hi : ∀ x, u (0, x) = 0)
    (heq : ∀ t ∈ Ioo 0 T, ∀ x, fderiv ℝ u (t, x) (1, 0) +
      ∑ j, A j (fderiv ℝ u (t, x) (0, EuclideanSpace.single j 1)) = 0)
    (x : ℝ^(n + 1)) : u (T, x) = 0 := by
  let S : ℝ → Fin (n + 1) → E →L[ℂ] E :=
    fun t j ↦ (((T - t : ℝ) : ℂ) * (-(2 * Real.pi * I))) • A j
  have hS (j : Fin (n + 1)) : ContinuousOn (fun t ↦ S t j) (Icc 0 T) := by
    dsimp [S]
    fun_prop
  obtain ⟨R, hR, hgapR⟩ := exists_pos_radius_gaussianExponential_coordinate_gap S hS
  let χ : ContDiffBump x := ⟨R, R + 1, hR, lt_add_one R⟩
  let e : Fin (n + 1) → ℝ^(n + 1) := fun j ↦ EuclideanSpace.single j 1
  let Ar : Fin (n + 1) → E →L[ℝ] E := fun j ↦ (A j).restrictScalars ℝ
  let v : ℝ × ℝ^(n + 1) → E := fun p ↦ χ p.2 • u p
  let F : ℝ × ℝ^(n + 1) → E :=
    fun p ↦ firstOrderCutoffSource e Ar χ (fun y ↦ u (p.1, y)) p.2
  have hK : IsCompact (tsupport χ) := χ.hasCompactSupport
  have hv : ContDiffOn ℝ 1 v (Ioo 0 T ×ˢ univ) :=
    (χ.contDiff.comp contDiff_snd).contDiffOn.smul hu
  have hvc : ContinuousOn v (Icc 0 T ×ˢ univ) :=
    (χ.continuous.comp continuous_snd).continuousOn.smul huc
  have hFc : ContinuousOn F (Icc 0 T ×ˢ univ) :=
    continuousOn_firstOrderCutoffSource_spatial e Ar χ.contDiff huc
  have hsv : ∀ t ∈ Icc 0 T, ∀ y ∉ tsupport χ, v (t, y) = 0 := by
    intro t _ y hy
    simp only [v, image_eq_zero_of_notMem_tsupport hy, zero_smul]
  have hsF : ∀ t ∈ Icc 0 T, ∀ y ∉ tsupport χ, F (t, y) = 0 := by
    intro t _ y hy
    change firstOrderCutoffSource e Ar χ (fun z ↦ u (t, z)) y = 0
    exact image_eq_zero_of_notMem_tsupport
      (fun h ↦ hy (tsupport_firstOrderCutoffSource_subset e Ar χ
        (fun z ↦ u (t, z)) h))
  have hvi : ∀ y, v (0, y) = 0 := by simp only [v, hi, smul_zero, implies_true]
  have hveq : ∀ t ∈ Ioo 0 T, ∀ y, fderiv ℝ v (t, y) (1, 0) +
      ∑ j, A j (fderiv ℝ v (t, y) (0, EuclideanSpace.single j 1)) = F (t, y) := by
    intro t ht y
    have hopen : IsOpen (Ioo 0 T ×ˢ (univ : Set (ℝ^(n + 1)))) :=
      isOpen_Ioo.prod isOpen_univ
    have hp : (t, y) ∈ Ioo 0 T ×ˢ (univ : Set (ℝ^(n + 1))) := ⟨ht, mem_univ y⟩
    have hcd : ContDiffAt ℝ 1 u (t, y) := hu.contDiffAt (hopen.mem_nhds hp)
    have hud : DifferentiableAt ℝ u (t, y) := hcd.differentiableAt one_ne_zero
    exact firstOrder_spatialCutoff_of_eq_zero e Ar
      (χ.contDiffAt.differentiableAt one_ne_zero) hud (heq t ht y)
  have hgap : ∀ t ∈ Icc 0 T, ∀ y, F (t, y) ≠ 0 →
      ∃ i : Fin (n + 1), (∑ j, ‖S t j‖ ^ 2) + 1 ≤
        (2 * Real.pi * (x i - y i)) ^ 2 / 8 := by
    intro t ht y hy
    apply hgapR t ht x y
    by_contra hd
    have hyball : y ∈ Metric.ball x χ.rIn := by
      simpa only [Metric.mem_ball, dist_comm] using lt_of_not_ge hd
    exact hy (firstOrderCutoffSource_eq_zero_of_eventuallyEq e Ar
      (fun z ↦ u (t, z)) (χ.eventuallyEq_one_of_mem_ball hyball))
  have hz := tendsto_intervalIntegral_integral_gaussianExponentialKernel_apply_zero
    S (fun y j ↦ 2 * Real.pi * (x j - y j)) hT zero_lt_one hK hFc hsF hgap
  have hvt : Continuous (fun y ↦ v (T, y)) :=
    hvc.comp_continuous (continuous_const.prodMk continuous_id)
      (fun y ↦ ⟨⟨hT, le_rfl⟩, mem_univ y⟩)
  have hvti : Integrable (fun y ↦ v (T, y)) :=
    hvt.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact hK
        (Function.support_subset_iff'.mpr (hsv T ⟨hT, le_rfl⟩)))
  have hlim : Tendsto (fun b : ℝ ↦ ∫ ξ : ℝ^(n + 1),
      Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2 + 2 * Real.pi * I * ⟪x, ξ⟫) •
        𝓕 (fun y ↦ v (T, y)) ξ) (𝓝[>] 0) (𝓝 (v (T, x))) := by
    have h := (tendsto_integral_gaussian_fourier_smul (v := x)
      hvti hvt.continuousAt).comp
      tendsto_inv_nhdsGT_zero
    simpa only [Function.comp_def, inv_inv] using h
  have hzero : Tendsto (fun b : ℝ ↦ ∫ ξ : ℝ^(n + 1),
      Complex.exp (-(b : ℂ) * ‖ξ‖ ^ 2 + 2 * Real.pi * I * ⟪x, ξ⟫) •
        𝓕 (fun y ↦ v (T, y)) ξ) (𝓝[>] 0) (𝓝 0) := by
    apply hz.congr'
    filter_upwards [self_mem_nhdsWithin] with b hb
    exact (integral_gaussian_fourier_eq_firstOrder_source A hT hb hK
      hv hvc hFc hsv hsF hvi hveq x).symm
  have hvzero := tendsto_nhds_unique hlim hzero
  have hχx : χ x = 1 := χ.eventuallyEq_one.eq_of_nhds
  simpa only [v, hχx, one_smul] using hvzero

/-- A classical solution of a constant first-order system with zero initial
data vanishes. Only interior `C¹` regularity and continuity at the time faces
are required. There is no hypothesis at spatial infinity, on the spectrum,
or on the number of spatial dimensions. -/
theorem eq_zero_of_firstOrder
    (A : Fin n → E →L[ℂ] E) {u : ℝ × ℝ^n → E} {T : ℝ}
    (hT : 0 ≤ T)
    (hu : ContDiffOn ℝ 1 u (Ioo 0 T ×ˢ univ))
    (huc : ContinuousOn u (Icc 0 T ×ˢ univ))
    (hi : ∀ x, u (0, x) = 0)
    (heq : ∀ t ∈ Ioo 0 T, ∀ x, fderiv ℝ u (t, x) (1, 0) +
      ∑ j, A j (fderiv ℝ u (t, x) (0, EuclideanSpace.single j 1)) = 0)
    (x : ℝ^n) : u (T, x) = 0 := by
  cases n with
  | succ n => exact eq_zero_of_firstOrder_succ A hT hu huc hi heq x
  | zero =>
    have hcurve : ContinuousOn (fun t ↦ u (t, x)) (Icc 0 T) :=
      huc.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht ↦ ⟨ht, mem_univ x⟩)
    have hd : ∀ t ∈ Ioo 0 T, HasDerivAt (fun s ↦ u (s, x)) (0 : E) t := by
      intro t ht
      have hopen : IsOpen (Ioo 0 T ×ˢ (univ : Set (ℝ^0))) :=
        isOpen_Ioo.prod isOpen_univ
      have hp : (t, x) ∈ Ioo 0 T ×ˢ (univ : Set (ℝ^0)) := ⟨ht, mem_univ x⟩
      have hcd : ContDiffAt ℝ 1 u (t, x) := hu.contDiffAt (hopen.mem_nhds hp)
      have hud : DifferentiableAt ℝ u (t, x) := hcd.differentiableAt one_ne_zero
      have h := hud.hasFDerivAt.comp_hasDerivAt t
        (hasFDerivAt_prodMk_left t x).hasDerivAt
      have hz : fderiv ℝ u (t, x) (1, 0) = 0 := by simpa using heq t ht x
      simpa only [Function.comp_def, ContinuousLinearMap.inl_apply, hz] using h
    have h := Evolution.eq_exp_apply_add_integral_of_hasDerivAt
      (0 : E →L[ℂ] E) hT hcurve (continuousOn_const (c := (0 : E)))
      (fun t ht ↦ by simpa only [zero_apply, zero_add] using hd t ht)
    simpa only [hi, map_zero, zero_add, intervalIntegral.integral_zero] using h

/-- Two classical solutions of the same constant first-order system with
the same initial data agree, without any condition at spatial infinity. -/
theorem eq_of_firstOrder
    (A : Fin n → E →L[ℂ] E) {u v : ℝ × ℝ^n → E} {T : ℝ}
    (hT : 0 ≤ T)
    (hu : ContDiffOn ℝ 1 u (Ioo 0 T ×ˢ univ))
    (hv : ContDiffOn ℝ 1 v (Ioo 0 T ×ˢ univ))
    (huc : ContinuousOn u (Icc 0 T ×ˢ univ))
    (hvc : ContinuousOn v (Icc 0 T ×ˢ univ))
    (hi : ∀ x, u (0, x) = v (0, x))
    (heu : ∀ t ∈ Ioo 0 T, ∀ x, fderiv ℝ u (t, x) (1, 0) +
      ∑ j, A j (fderiv ℝ u (t, x) (0, EuclideanSpace.single j 1)) = 0)
    (hev : ∀ t ∈ Ioo 0 T, ∀ x, fderiv ℝ v (t, x) (1, 0) +
      ∑ j, A j (fderiv ℝ v (t, x) (0, EuclideanSpace.single j 1)) = 0)
    (x : ℝ^n) : u (T, x) = v (T, x) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_firstOrder A hT (hu.sub hv) (huc.sub hvc)
    (fun y ↦ sub_eq_zero.mpr (hi y)) _ x
  intro t ht y
  have hopen : IsOpen (Ioo 0 T ×ˢ (univ : Set (ℝ^n))) :=
    isOpen_Ioo.prod isOpen_univ
  have hp : (t, y) ∈ Ioo 0 T ×ˢ (univ : Set (ℝ^n)) := ⟨ht, mem_univ y⟩
  have hud : DifferentiableAt ℝ u (t, y) :=
    (hu.contDiffAt (hopen.mem_nhds hp)).differentiableAt one_ne_zero
  have hvd : DifferentiableAt ℝ v (t, y) :=
    (hv.contDiffAt (hopen.mem_nhds hp)).differentiableAt one_ne_zero
  rw [fderiv_fun_sub hud hvd]
  simp only [sub_apply, map_sub, Finset.sum_sub_distrib]
  rw [sub_add_sub_comm, heu t ht y, hev t ht y, sub_self]

end PDE.Analysis
