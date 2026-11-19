/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.AffineVolume.Product
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Integrals under independent affine dilations

The product of the two scalar Jacobians gives the change of variables formula
for Bochner set integrals over arbitrary sets: the affine map is a measurable equivalence that
scales the Haar measure. No integrability assumption is needed.
The parabolic specialization includes zero spatial dimension.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped Pointwise

namespace PDE.Analysis

/-- Independent nonzero dilations of two real vector spaces have the product
Jacobian in a set integral, followed by an arbitrary translation. The set need not be
measurable: the map is a measurable equivalence that scales the Haar measure, so the set
integral transforms through `setIntegral_map_equiv`. -/
theorem setIntegral_image_const_add_prod_smul
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace (E × F)] [BorelSpace (E × F)]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (μ : Measure (E × F)) [μ.IsAddHaarMeasure]
    (z : E × F) {r s : ℝ} (hr : r ≠ 0) (hs : s ≠ 0)
    {S : Set (E × F)} (f : E × F → G) :
    ∫ q in (fun p : E × F ↦ z + (r • p.1, s • p.2)) '' S, f q ∂μ =
      |r ^ Module.finrank ℝ E * s ^ Module.finrank ℝ F| •
        ∫ p in S, f (z + (r • p.1, s • p.2)) ∂μ := by
  let A : E × F →L[ℝ] E × F :=
    (r • ContinuousLinearMap.id ℝ E).prodMap (s • ContinuousLinearMap.id ℝ F)
  have hA : (A : E × F →ₗ[ℝ] E × F).det =
      r ^ Module.finrank ℝ E * s ^ Module.finrank ℝ F := by
    change ((r • (LinearMap.id : E →ₗ[ℝ] E)).prodMap
      (s • (LinearMap.id : F →ₗ[ℝ] F))).det = _
    simp [LinearMap.det_prodMap, LinearMap.det_smul]
  have hdet : (A : E × F →ₗ[ℝ] E × F).det ≠ 0 := by
    rw [hA]; exact mul_ne_zero (pow_ne_zero _ hr) (pow_ne_zero _ hs)
  -- the affine map as a measurable equivalence
  let e : E × F ≃ᵐ E × F :=
    { toFun := fun p ↦ z + (r • p.1, s • p.2)
      invFun := fun q ↦ (r⁻¹ • (q - z).1, s⁻¹ • (q - z).2)
      left_inv := fun p ↦ by simp [smul_smul, inv_mul_cancel₀ hr, inv_mul_cancel₀ hs]
      right_inv := fun q ↦ by
        ext <;> simp [smul_smul, mul_inv_cancel₀ hr, mul_inv_cancel₀ hs]
      measurable_toFun := (continuous_const.add
        ((continuous_const.smul continuous_fst).prodMk
          (continuous_const.smul continuous_snd))).measurable
      measurable_invFun := ((continuous_const.smul (continuous_id.sub continuous_const).fst).prodMk
        (continuous_const.smul (continuous_id.sub continuous_const).snd)).measurable }
  have he : (e : E × F → E × F) = (z + ·) ∘ A := rfl
  -- `e` scales the Haar measure by `|det A|⁻¹`
  set c : ENNReal := ENNReal.ofReal |(A : E × F →ₗ[ℝ] E × F).det⁻¹|
  have hmap : Measure.map e μ = c • μ := by
    rw [he, ← Measure.map_map (measurable_const_add z) A.continuous.measurable]
    change Measure.map (z + ·) (Measure.map (A : E × F →ₗ[ℝ] E × F) μ) = _
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet,
      Measure.map_smul _ (measurable_const_add z).aemeasurable, map_add_left_eq_self]
  have hc0 : c ≠ 0 := by simp [c, hdet]
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hμ : μ = c⁻¹ • Measure.map e μ := by
    rw [hmap, smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul]
  have himage : (fun p : E × F ↦ z + (r • p.1, s • p.2)) '' S = e '' S := rfl
  calc ∫ q in (fun p : E × F ↦ z + (r • p.1, s • p.2)) '' S, f q ∂μ
      = c⁻¹.toReal • ∫ q in e '' S, f q ∂Measure.map e μ := by
        conv_lhs => rw [hμ]
        rw [himage, Measure.restrict_smul, integral_smul_measure]
    _ = c⁻¹.toReal • ∫ p in S, f (e p) ∂μ := by
        rw [setIntegral_map_equiv, e.preimage_image]
    _ = _ := by
        congr 1
        simp only [c, ENNReal.toReal_inv, abs_inv, hA]
        rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _)), inv_inv]

/-- A parabolic affine substitution contributes exactly `r^(n+2)` to the
spacetime integral. The statement also holds for a zero-dimensional space. -/
theorem setIntegral_image_space_time_dilation
    {n : ℕ} (x : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r)
    {S : Set (ℝ^n × ℝ)} (f : ℝ^n × ℝ → ℝ) :
    ∫ q in (fun p : ℝ^n × ℝ ↦ (x + r • p.1, t + r ^ 2 * p.2)) '' S, f q =
      r ^ (n + 2) * ∫ p in S, f (x + r • p.1, t + r ^ 2 * p.2) := by
  let : (volume : Measure (ℝ^n × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  simpa only [Prod.mk_add_mk, smul_eq_mul, finrank_euclideanSpace_fin,
    Module.finrank_self, pow_one, ← pow_add, abs_of_nonneg (pow_nonneg hr.le _)] using
    setIntegral_image_const_add_prod_smul volume (x, t) hr.ne'
      (pow_ne_zero 2 hr.ne') f

/-- The closed unit backward cylinder maps exactly onto the closed cylinder of
radius `r`, with its top time and spatial center translated independently. -/
theorem image_closedBall_prod_Icc_space_time_dilation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    (fun p : E × ℝ ↦ (x + r • p.1, t + r ^ 2 * p.2)) ''
        (closedBall 0 1 ×ˢ Icc (-1) 0) =
      closedBall x r ×ˢ Icc (t - r ^ 2) t := by
  have hx : (fun y : E ↦ x + r • y) '' closedBall 0 1 = closedBall x r := by
    calc
      _ = (fun y : E ↦ x + y) '' (r • closedBall 0 1) := by
        change _ = (fun y : E ↦ x + y) '' ((fun y : E ↦ r • y) '' closedBall 0 1)
        rw [image_image]
      _ = (fun y : E ↦ x + y) '' closedBall 0 r := by
        rw [smul_closedBall' hr.ne', smul_zero, Real.norm_of_nonneg hr.le, mul_one]
      _ = closedBall x r := by simp [image_add_left]
  have ht : (fun s : ℝ ↦ t + r ^ 2 * s) '' Icc (-1) 0 = Icc (t - r ^ 2) t := by
    simpa [add_comm, sub_eq_add_neg] using image_affine_Icc' (sq_pos_of_pos hr) t (-1) 0
  change (Prod.map (fun y : E ↦ x + r • y) (fun s : ℝ ↦ t + r ^ 2 * s)) '' _ = _
  rw [prodMap_image_prod, hx, ht]

/-- Exact normalization of an L1 integral on a closed backward cylinder. -/
theorem setIntegral_closedBall_prod_Icc_space_time_dilation
    {n : ℕ} (x : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r)
    (f : ℝ^n × ℝ → ℝ) :
    ∫ q in closedBall x r ×ˢ Icc (t - r ^ 2) t, f q =
      r ^ (n + 2) *
        ∫ p in closedBall (0 : ℝ^n) 1 ×ˢ Icc (-1 : ℝ) 0,
          f (x + r • p.1, t + r ^ 2 * p.2) := by
  rw [← image_closedBall_prod_Icc_space_time_dilation x t hr]
  exact setIntegral_image_space_time_dilation x t hr f

end PDE.Analysis
