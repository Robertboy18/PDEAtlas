/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.InnerProductSpace.Calculus.Normalization.Energy
public import PDE.Analysis.Normed.Operator.Energy
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Differentiating the energy of a normalized field

A bounded variation of a unit-length field stays away from zero for small
parameters. We can therefore use a smooth cutoff of normalization. Its
bounded, Lipschitz derivative gives a quadratic bound for the varying energy,
so the weak derivative columns need only be square-integrable.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal InnerProductSpace

namespace NormedSpace

variable {E α : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace α] {μ : Measure α}

/-- The first variation of the normalized energy can be passed through the
integral for square-integrable derivative columns and a bounded variation.
The cutoff equals normalization on the fixed annulus `1/2 ≤ ‖z‖ ≤ 2`. -/
theorem hasDerivAt_integral_normalized_energy
    {G : E → E} {C K M : ℝ≥0}
    (hbound : ∀ z, ‖fderiv ℝ G z‖ ≤ C)
    (hLip : LipschitzWith K (fderiv ℝ G))
    (heq : ∀ z, 1 / 2 ≤ ‖z‖ → ‖z‖ ≤ 2 → G z = normalize z)
    {u v a b : α → E}
    (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ)
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ)
    (hunit : ∀ᵐ x ∂μ, ‖u x‖ = 1)
    (hvbound : ∀ᵐ x ∂μ, ‖v x‖ ≤ M)
    (htangent : ∀ᵐ x ∂μ, ⟪u x, a x⟫_ℝ = 0) :
    Integrable (fun x ↦ ⟪a x, b x⟫_ℝ - ‖a x‖ ^ 2 * ⟪u x, v x⟫_ℝ) μ ∧
      HasDerivAt
        (fun t : ℝ ↦ ∫ x, ‖fderiv ℝ G (u x + t • v x) (a x + t • b x)‖ ^ 2 / 2 ∂μ)
        (∫ x, ⟪a x, b x⟫_ℝ - ‖a x‖ ^ 2 * ⟪u x, v x⟫_ℝ ∂μ) 0 := by
  let F : ℝ → α → ℝ :=
    fun t x ↦ ‖fderiv ℝ G (u x + t • v x) (a x + t • b x)‖ ^ 2 / 2
  let B : α → ℝ := fun x ↦
    (C : ℝ) * ((K : ℝ) * M + C) * (‖a x‖ + ‖b x‖) ^ 2
  have hmeas (t : ℝ) : AEStronglyMeasurable (F t) μ := by
    exact (continuous_id.div_const (2 : ℝ)).comp_aestronglyMeasurable
      (((ContinuousLinearMap.id ℝ (E →L[ℝ] E)).aestronglyMeasurable_comp₂
      (hLip.continuous.comp_aestronglyMeasurable (hu.add (hv.const_smul t)))
      (ha.aestronglyMeasurable.add (hb.aestronglyMeasurable.const_smul t))).norm.pow 2)
  have hF0 : Integrable (F 0) μ := by
    apply (ha.norm.integrable_sq.const_mul ((C : ℝ) ^ 2 / 2)).mono' (hmeas 0)
    filter_upwards [] with x
    have h := (fderiv ℝ G (u x)).le_of_opNorm_le (hbound (u x)) (a x)
    have hs := sq_le_sq₀ (norm_nonneg _) (mul_nonneg C.property (norm_nonneg _)) |>.mpr h
    dsimp [F]
    simp only [zero_smul, add_zero]
    rw [abs_of_nonneg (by positivity)]
    simp only [mul_pow] at hs
    calc
      _ ≤ ((C : ℝ) ^ 2 * ‖a x‖ ^ 2) / 2 := div_le_div_of_nonneg_right hs (by norm_num)
      _ = _ := by ring
  have hB : Integrable B μ :=
    ((ha.norm.add hb.norm).integrable_sq).const_mul _
  have hBnonneg (x : α) : 0 ≤ B x := by dsimp [B]; positivity
  have hderiv_meas : AEStronglyMeasurable
      (fun x ↦ ⟪a x, b x⟫_ℝ - ‖a x‖ ^ 2 * ⟪u x, v x⟫_ℝ) μ :=
    (ha.aestronglyMeasurable.inner hb.aestronglyMeasurable).sub
      ((ha.aestronglyMeasurable.norm.pow 2).mul (hu.inner hv))
  have hlocal : ∀ᵐ x ∂μ,
      LipschitzOnWith (Real.nnabs (B x)) (fun t ↦ F t x) (Icc (-1) 1) := by
    filter_upwards [hvbound] with x hx
    have h := ContinuousLinearMap.lipschitzOnWith_half_norm_sq_apply_affine
      hbound hLip (u x) (v x) (a x) (b x)
    apply h.weaken
    rw [← NNReal.coe_le_coe, Real.coe_nnabs, abs_of_nonneg (hBnonneg x)]
    simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_pow, coe_nnnorm]
    dsimp [B]
    gcongr
  have hderiv : ∀ᵐ x ∂μ, HasDerivAt (fun t ↦ F t x)
      (⟪a x, b x⟫_ℝ - ‖a x‖ ^ 2 * ⟪u x, v x⟫_ℝ) 0 := by
    filter_upwards [hunit, htangent] with x hx ht
    apply (hasDerivAt_normalized_energy hx (v x) (a x) (b x) ht).congr_of_eventuallyEq
    have hnear : ∀ᶠ t in 𝓝 (0 : ℝ),
        1 / 2 < ‖u x + t • v x‖ ∧ ‖u x + t • v x‖ < 2 :=
      (continuous_const.add (continuous_id.smul continuous_const)).norm.continuousAt.eventually
        (Ioo_mem_nhds (by norm_num [hx]) (by norm_num [hx]))
    filter_upwards [hnear] with t ht
    have hgerm : G =ᶠ[𝓝 (u x + t • v x)] normalize :=
      (continuous_norm.continuousAt.eventually (Ioo_mem_nhds ht.1 ht.2)).mono
        fun z hz ↦ heq z hz.1.le hz.2.le
    dsimp [F]
    rw [hgerm.fderiv_eq]
  exact hasDerivAt_integral_of_dominated_loc_of_lip
    (Icc_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall hmeas) hF0 hderiv_meas hlocal hB hderiv

end NormedSpace
