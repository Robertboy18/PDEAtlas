/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.GaussianRegularization.CoordinateDecay
public import PDE.Common.Euclidean

/-!
# Vanishing of Gaussian-regularized kernels away from the propagation cone

A fixed positive gap in the coordinate estimate defeats the Gaussian
normalization as the regularization parameter tends to zero. The scalar limit
is independent of the operator algebra.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace PDE.Analysis.Fourier

/-- Exponential decay in the inverse regularization parameter dominates
the Gaussian normalization in every finite dimension. -/
theorem tendsto_gaussian_normalization_mul_exp_neg_div
    (d : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun b : ℝ ↦ √(Real.pi / (b / 2)) ^ d * Real.exp (-δ / b))
      (𝓝[>] 0) (𝓝 0) := by
  have h := ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((d : ℝ) / 2) δ hδ).comp tendsto_inv_nhdsGT_zero).const_mul
      (√(2 * Real.pi) ^ d)
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with b hb
  have hb0 : 0 < b := hb
  have hquot : Real.pi / (b / 2) = (2 * Real.pi) * b⁻¹ := by ring
  dsimp only [Function.comp_def]
  conv_rhs =>
    rw [hquot, Real.sqrt_mul (by positivity), mul_pow,
      Real.sqrt_eq_rpow b⁻¹, ← Real.rpow_mul_natCast (inv_nonneg.mpr hb0.le)]
  rw [show (1 / 2 : ℝ) * d = d / 2 by ring]
  simp only [div_eq_mul_inv]
  ring

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
variable {n : ℕ} {α : Type*}

/-- The kernels vanish uniformly over any family with a fixed positive
coordinate gap. The coordinate exhibiting the gap may depend on the parameter. -/
theorem tendstoUniformlyOn_gaussianExponentialKernel_zero
    (h₁ : ‖(1 : A)‖ ≤ 1) (S : α → Fin (n + 1) → A)
    (k : α → Fin (n + 1) → ℝ) (K : Set α) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ x ∈ K, ∃ i : Fin (n + 1),
      (∑ j, ‖S x j‖ ^ 2) + δ ≤ k x i ^ 2 / 8) :
    TendstoUniformlyOn (fun b x ↦ gaussianExponentialKernel (S x) b (k x))
      0 (𝓝[>] 0) K := by
  rw [SeminormedAddGroup.tendstoUniformlyOn_zero]
  intro ε hε
  have hsmall := (tendsto_gaussian_normalization_mul_exp_neg_div (n + 1) hδ).eventually
    (gt_mem_nhds hε)
  filter_upwards [self_mem_nhdsWithin, hsmall] with b hb hbound x hx
  obtain ⟨i, hi⟩ := hgap x hx
  exact (norm_gaussianExponentialKernel_le_of_coordinate_gap h₁ (S x) hb (k x) i hi).trans_lt
    hbound

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [MeasurableSpace α]

/-- The integral action of a separated kernel is bounded by the same scalar
Gaussian decay factor times the `L¹` norm of the source. -/
theorem norm_integral_gaussianExponentialKernel_apply_le_of_coordinate_gap
    {μ : Measure α} (S : α → Fin (n + 1) → E →L[ℂ] E)
    (k : α → Fin (n + 1) → ℝ) {f : α → E} (hf : Integrable f μ)
    {b δ : ℝ} (hb : 0 < b)
    (hgap : ∀ᵐ x ∂μ, f x ≠ 0 →
      ∃ i : Fin (n + 1), (∑ j, ‖S x j‖ ^ 2) + δ ≤ k x i ^ 2 / 8) :
    ‖∫ x, gaussianExponentialKernel (S x) b (k x) (f x) ∂μ‖ ≤
      (√(Real.pi / (b / 2)) ^ (n + 1) * Real.exp (-δ / b)) *
        ∫ x, ‖f x‖ ∂μ := by
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hf.norm.const_mul _)
  filter_upwards [hgap] with x hx
  by_cases hzero : f x = 0
  · simp only [hzero, map_zero, norm_zero, mul_zero, le_refl]
  · obtain ⟨i, hi⟩ := hx hzero
    exact ((gaussianExponentialKernel (S x) b (k x)).le_opNorm (f x)).trans
      (mul_le_mul_of_nonneg_right
        (norm_gaussianExponentialKernel_le_of_coordinate_gap
          (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := E)) (S x) hb (k x) i hi)
        (norm_nonneg (f x)))

/-- A separated integrable source contributes zero in the limit of vanishing
Gaussian regularization. The coefficient family and the gap coordinate may
vary over the integration space. -/
theorem tendsto_integral_gaussianExponentialKernel_apply_zero
    {μ : Measure α} (S : α → Fin (n + 1) → E →L[ℂ] E)
    (k : α → Fin (n + 1) → ℝ) {f : α → E} (hf : Integrable f μ)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᵐ x ∂μ, f x ≠ 0 →
      ∃ i : Fin (n + 1), (∑ j, ‖S x j‖ ^ 2) + δ ≤ k x i ^ 2 / 8) :
    Tendsto (fun b : ℝ ↦ ∫ x, gaussianExponentialKernel (S x) b (k x) (f x) ∂μ)
      (𝓝[>] 0) (𝓝 0) := by
  let q : ℝ → ℝ :=
    fun b ↦ √(Real.pi / (b / 2)) ^ (n + 1) * Real.exp (-δ / b)
  apply squeeze_zero_norm' (a := fun b ↦ q b * ∫ x, ‖f x‖ ∂μ)
  · filter_upwards [self_mem_nhdsWithin] with b hb
    exact norm_integral_gaussianExponentialKernel_apply_le_of_coordinate_gap S k hf hb hgap
  · simpa only [zero_mul] using
      (tendsto_gaussian_normalization_mul_exp_neg_div (n + 1) hδ).mul_const
        (∫ x, ‖f x‖ ∂μ)

open Set

/-- The spacetime source integral vanishes when its kernel has a
uniform coordinate gap on the support of the source. The source assumptions
are only continuity and a common compact spatial support. -/
theorem tendsto_intervalIntegral_integral_gaussianExponentialKernel_apply_zero
    (S : ℝ → Fin (n + 1) → E →L[ℂ] E)
    (k : ℝ^(n + 1) → Fin (n + 1) → ℝ)
    {F : ℝ × ℝ^(n + 1) → E} {a c δ : ℝ} {K : Set (ℝ^(n + 1))}
    (hac : a ≤ c) (hδ : 0 < δ) (hK : IsCompact K)
    (hF : ContinuousOn F (Icc a c ×ˢ univ))
    (hs : ∀ t ∈ Icc a c, ∀ x ∉ K, F (t, x) = 0)
    (hgap : ∀ t ∈ Icc a c, ∀ x, F (t, x) ≠ 0 →
      ∃ i : Fin (n + 1), (∑ j, ‖S t j‖ ^ 2) + δ ≤ k x i ^ 2 / 8) :
    Tendsto (fun b : ℝ ↦ ∫ t in a..c, ∫ x : ℝ^(n + 1),
      gaussianExponentialKernel (S t) b (k x) (F (t, x)))
      (𝓝[>] 0) (𝓝 0) := by
  let q : ℝ → ℝ :=
    fun b ↦ √(Real.pi / (b / 2)) ^ (n + 1) * Real.exp (-δ / b)
  have hr : ContinuousOn (fun t ↦ ∫ x, ‖F (t, x)‖) (Icc a c) := by
    apply continuousOn_integral_of_compact_support hK hF.norm
    intro t x ht hx
    simp only [hs t ht x hx, norm_zero]
  have hri : IntervalIntegrable (fun t ↦ ∫ x, ‖F (t, x)‖) volume a c :=
    hr.intervalIntegrable_of_Icc hac
  apply squeeze_zero_norm'
    (a := fun b ↦ q b * ∫ t in a..c, ∫ x, ‖F (t, x)‖)
  · filter_upwards [self_mem_nhdsWithin] with b hb
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le hac _ (hri.const_mul (q b))
    apply ae_of_all
    intro t ht
    have ht' := Ioc_subset_Icc_self ht
    have hc : Continuous (fun x ↦ F (t, x)) :=
      hF.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x ↦ ⟨ht', mem_univ x⟩)
    have hFi : Integrable (fun x ↦ F (t, x)) :=
      hc.integrable_of_hasCompactSupport
        (HasCompactSupport.of_support_subset_isCompact hK
          (Function.support_subset_iff'.mpr (hs t ht')))
    exact norm_integral_gaussianExponentialKernel_apply_le_of_coordinate_gap
      (fun _ ↦ S t) k hFi hb (ae_of_all _ (hgap t ht'))
  · simpa only [zero_mul] using
      (tendsto_gaussian_normalization_mul_exp_neg_div (n + 1) hδ).mul_const
        (∫ t in a..c, ∫ x, ‖F (t, x)‖)

omit [CompleteSpace E] in
/-- A continuous operator family on a compact time interval admits a spatial
radius outside which its Gaussian kernel has a fixed positive coordinate gap.
The radius depends only on the operator family and interval. -/
theorem exists_pos_radius_gaussianExponential_coordinate_gap
    (S : ℝ → Fin (n + 1) → E →L[ℂ] E) {a c : ℝ}
    (hS : ∀ j, ContinuousOn (fun t ↦ S t j) (Icc a c)) :
    ∃ R > 0, ∀ t ∈ Icc a c, ∀ x y : ℝ^(n + 1), R ≤ dist x y →
      ∃ i : Fin (n + 1), (∑ j, ‖S t j‖ ^ 2) + 1 ≤
        (2 * Real.pi * (x i - y i)) ^ 2 / 8 := by
  have hc : ContinuousOn (fun t ↦ ∑ j, ‖S t j‖ ^ 2) (Icc a c) :=
    continuousOn_finsetSum _ fun j _ ↦ (hS j).norm.pow 2
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  let D : ℝ := 8 * (n + 1 : ℕ) * (max C 0 + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D + 1, by positivity, ?_⟩
  intro t ht x y hxy
  have hsum : (∑ j, ‖S t j‖ ^ 2) ≤ max C 0 := by
    have hc' : |∑ j, ‖S t j‖ ^ 2| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC t ht
    exact (le_abs_self _).trans (hc'.trans (le_max_left C 0))
  have hnorm : D ≤ ‖x - y‖ ^ 2 := by
    rw [dist_eq_norm] at hxy
    nlinarith [sq_nonneg (‖x - y‖ - 1)]
  have hfactor : 1 ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.one_le_pi_div_two]
  have hphase : D ≤ ∑ j, (2 * Real.pi * (x j - y j)) ^ 2 := by
    calc
      D ≤ ‖x - y‖ ^ 2 := hnorm
      _ ≤ (2 * Real.pi) ^ 2 * ‖x - y‖ ^ 2 :=
        le_mul_of_one_le_left (sq_nonneg _) hfactor
      _ = _ := by
        simp only [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply,
          mul_pow, Finset.mul_sum]
  have havg : (∑ _j : Fin (n + 1), 8 * (max C 0 + 1)) ≤
      ∑ j, (2 * Real.pi * (x j - y j)) ^ 2 := by
    calc
      _ = D := by simp [D]; ring
      _ ≤ _ := hphase
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty havg
  refine ⟨i, ?_⟩
  linarith

end PDE.Analysis.Fourier
