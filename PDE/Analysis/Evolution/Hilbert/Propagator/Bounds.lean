/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.InnerProductSpace.Calculus.Norm
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Hilbert-space bounds for time-dependent linear equations

A quadratic-form bound controls the norm of a forced trajectory, including times at
which the trajectory vanishes. A positive integrating factor absorbs variable growth.
All continuity, positivity and derivative assumptions are confined to the time interval;
neither finite dimension nor completeness of the inner-product space is needed.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped RealInnerProductSpace

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A dissipative equation gains at most the integral of the forcing norm.
The equation only needs right derivatives before the final time. -/
theorem norm_le_initial_add_integral
    {a b : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (hu : ContinuousOn u (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hode : ∀ t ∈ Ico a b,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico a b, ∀ x : H, ⟪x, A t x⟫ ≤ 0) :
    ∀ t ∈ Icc a b, ‖u t‖ ≤ ‖u a‖ + ∫ s in a..t, ‖f s‖ := by
  intro t ht
  have hab := ht.1.trans ht.2
  let B : ℝ → ℝ := fun t ↦ ‖u a‖ + ∫ s in a..t, ‖f s‖
  have hB : ContinuousOn B (Icc a b) :=
    continuousOn_const.add (by
      simpa only [uIcc_of_le hab] using
        intervalIntegral.continuousOn_primitive_interval'
          (hf.norm.intervalIntegrable_of_Icc hab) left_mem_uIcc)
  have hBd (s : ℝ) (hs : s ∈ Ico a b) :
      HasDerivWithinAt B ‖f s‖ (Ici s) s := by
    have hsI := Ico_subset_Icc_self hs
    let : Fact (s ∈ Icc a b) := ⟨hsI⟩
    exact ((intervalIntegral.integral_hasDerivWithinAt_right
      ((hf.norm.mono (Icc_subset_Icc_right hs.2.le)).intervalIntegrable_of_Icc hs.1)
      (hf.norm.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc s)
      (hf.norm s hsI)).const_add ‖u a‖).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hs)
  apply image_le_of_liminf_slope_right_le_deriv_boundary
    (continuous_norm.comp_continuousOn hu) (by simp [B]) hB hBd ?_ ht
  intro s hs r hr
  by_cases hz : u s = 0
  · have hd : HasDerivWithinAt u (f s) (Ici s) s := by
      simpa only [hz, map_zero, zero_add] using hode s hs
    exact hd.liminf_right_slope_norm_le hr
  · have hn := norm_pos_iff.mpr hz
    have hi : ⟪u s, A s (u s) + f s⟫ ≤ ‖u s‖ * ‖f s‖ := by
      rw [inner_add_right]
      exact (add_le_add (hA s hs (u s)) (real_inner_le_norm (u s) (f s))).trans_eq
        (zero_add _)
    have hdiv : ⟪u s, A s (u s) + f s⟫ / ‖u s‖ ≤ ‖f s‖ :=
      (div_le_iff₀ hn).mpr (by simpa only [mul_comm] using hi)
    exact (PDE.Analysis.hasDerivWithinAt_norm_of_ne_zero (hode s hs) hz).liminf_right_slope_le
      (hdiv.trans_lt hr)

/-- A positive integrating factor `W' = growth * W` absorbs the quadratic growth.
The estimate uses the weighted forcing norm and makes no global extension assumptions. -/
theorem weighted_norm_le_initial_add_integral
    {a b : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (growth W : ℝ → ℝ) (hWpos : ∀ t ∈ Icc a b, 0 < W t)
    (hWcont : ContinuousOn W (Icc a b))
    (hW : ∀ t ∈ Ico a b, HasDerivWithinAt W (growth t * W t) (Ici t) t)
    (hu : ContinuousOn u (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hode : ∀ t ∈ Ico a b,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico a b, ∀ x : H, ⟪x, A t x⟫ ≤ growth t * ‖x‖ ^ 2) :
    ∀ t ∈ Icc a b,
      ‖u t‖ / W t ≤ ‖u a‖ / W a + ∫ s in a..t, ‖f s‖ / W s := by
  have hInv (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt (fun s ↦ (W s)⁻¹)
        (-growth t * (W t)⁻¹) (Ici t) t := by
    have hn := (hWpos t (Ico_subset_Icc_self ht)).ne'
    convert! (hW t ht).inv hn using 1
    field_simp
  have hcInv : ContinuousOn (fun t ↦ (W t)⁻¹) (Icc a b) :=
    hWcont.inv₀ fun t ht ↦ (hWpos t ht).ne'
  let v : ℝ → H := fun t ↦ (W t)⁻¹ • u t
  let F : ℝ → H := fun t ↦ (W t)⁻¹ • f t
  let B : ℝ → H →L[ℝ] H := fun t ↦ A t - growth t • ContinuousLinearMap.id ℝ H
  have hvode (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt v (B t (v t) + F t) (Ici t) t := by
    convert! (hInv t ht).smul (hode t ht) using 1
    dsimp [v, F, B]
    simp only [sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_add]
    module
  have hB (t : ℝ) (ht : t ∈ Ico a b) (x : H) : ⟪x, B t x⟫ ≤ 0 := by
    dsimp [B]
    simp only [sub_apply, smul_apply,
      ContinuousLinearMap.id_apply, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq]
    linarith [hA t ht x]
  have hn (t : ℝ) (ht : t ∈ Icc a b) (x : H) :
      ‖(W t)⁻¹ • x‖ = ‖x‖ / W t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hWpos t ht)),
      div_eq_mul_inv, mul_comm]
  intro t ht
  have h := norm_le_initial_add_integral B (hcInv.smul hu) (hcInv.smul hf) hvode hB t ht
  change ‖(W t)⁻¹ • u t‖ ≤ ‖(W a)⁻¹ • u a‖ +
    ∫ s in a..t, ‖(W s)⁻¹ • f s‖ at h
  rw [hn t ht, hn a ⟨le_rfl, ht.1.trans ht.2⟩] at h
  convert h using 1
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  exact (hn s ⟨hs.1, hs.2.trans ht.2⟩ (f s)).symm

end PDE.Analysis.Evolution
