/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Hilbert.Propagator.Bounds
import CAS.ExactTactic

/-!
# Growth envelopes for Hilbert-space evolution

Integrating the scalar quadratic-form bound produces an explicit positive weight.
A prescribed positive reference envelope can instead absorb the principal growth,
leaving a nonnegative error in one exponential factor.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace PDE.Analysis.Evolution

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A continuous quadratic growth rate gives the sharp integrating-factor estimate,
with no sign restriction on the rate and forcing continuous only on the interval. -/
theorem norm_le_exp_integral_mul
    {a b : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    {growth : ℝ → ℝ} (hg : ContinuousOn growth (Icc a b))
    (hu : ContinuousOn u (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hode : ∀ t ∈ Ico a b,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico a b, ∀ x : H, ⟪x, A t x⟫ ≤ growth t * ‖x‖ ^ 2) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ≤ Real.exp (∫ s in a..t, growth s) *
        (‖u a‖ + ∫ s in a..t, Real.exp (-(∫ r in a..s, growth r)) * ‖f s‖) := by
  intro t ht
  have hab := ht.1.trans ht.2
  let I : ℝ → ℝ := fun t ↦ ∫ s in a..t, growth s
  let W : ℝ → ℝ := fun t ↦ Real.exp (I t)
  have hI : ContinuousOn I (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval'
        (hg.intervalIntegrable_of_Icc hab) left_mem_uIcc
  have hW (s : ℝ) (hs : s ∈ Ico a b) :
      HasDerivWithinAt W (growth s * W s) (Ici s) s := by
    have hsI := Ico_subset_Icc_self hs
    let : Fact (s ∈ Icc a b) := ⟨hsI⟩
    have hd : HasDerivWithinAt I (growth s) (Icc a b) s :=
      intervalIntegral.integral_hasDerivWithinAt_right
        ((hg.mono (Icc_subset_Icc_right hs.2.le)).intervalIntegrable_of_Icc hs.1)
        (hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc s) (hg s hsI)
    simpa only [W, mul_comm] using
      hd.exp.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hs)
  have h := weighted_norm_le_initial_add_integral A growth W
    (fun _ _ ↦ Real.exp_pos _) (Real.continuous_exp.comp_continuousOn hI) hW
    hu hf hode hA t ht
  simp only [W, I, intervalIntegral.integral_same, Real.exp_zero, div_one] at h
  have heq (s : ℝ) : ‖f s‖ / Real.exp (∫ r in a..s, growth r) =
      Real.exp (-(∫ r in a..s, growth r)) * ‖f s‖ := by
    rw [Real.exp_neg, div_eq_mul_inv, mul_comm]
  simpa only [heq, mul_comm] using
    (div_le_iff₀ (Real.exp_pos (∫ s in a..t, growth s))).mp h

/-- A positive reference envelope absorbs the variable rate. A nonnegative error
contributes at most `exp (μ * (t-a))`. Every analytic hypothesis is interval-local. -/
theorem norm_le_envelope_mul_integral
    {a b : ℝ} {u f : ℝ → H} (A : ℝ → H →L[ℝ] H)
    (rate P : ℝ → ℝ) {μ : ℝ} (hμ : 0 ≤ μ)
    (hPpos : ∀ t ∈ Icc a b, 0 < P t) (hPcont : ContinuousOn P (Icc a b))
    (hP : ∀ t ∈ Ico a b, HasDerivWithinAt P (rate t * P t) (Ici t) t)
    (hu : ContinuousOn u (Icc a b)) (hf : ContinuousOn f (Icc a b))
    (hode : ∀ t ∈ Ico a b,
      HasDerivWithinAt u (A t (u t) + f t) (Ici t) t)
    (hA : ∀ t ∈ Ico a b, ∀ x : H, ⟪x, A t x⟫ ≤ (rate t + μ) * ‖x‖ ^ 2) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ≤ Real.exp (μ * (t - a)) * P t *
        (‖u a‖ / P a + ∫ s in a..t, ‖f s‖ / P s) := by
  let W : ℝ → ℝ := fun t ↦ P t * Real.exp (μ * (t - a))
  have hWpos (t : ℝ) (ht : t ∈ Icc a b) : 0 < W t :=
    mul_pos (hPpos t ht) (Real.exp_pos _)
  have hExp (t : ℝ) : HasDerivAt (fun s : ℝ ↦ Real.exp (μ * (s - a)))
      (μ * Real.exp (μ * (t - a))) t := by
    cas
  have hW (t : ℝ) (ht : t ∈ Ico a b) :
      HasDerivWithinAt W ((rate t + μ) * W t) (Ici t) t := by
    convert! (hP t ht).mul (hExp t).hasDerivWithinAt using 1
    dsimp [W]
    ring
  have hcW : ContinuousOn W (Icc a b) :=
    hPcont.mul ((Real.continuous_exp.comp
      (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn)
  have hF := hf.norm.div hPcont (fun t ht ↦ (hPpos t ht).ne')
  have hFW := hf.norm.div hcW (fun t ht ↦ (hWpos t ht).ne')
  have hbase := weighted_norm_le_initial_add_integral A (fun t ↦ rate t + μ) W
    hWpos hcW hW hu hf hode hA
  intro t ht
  have hint : (∫ s in a..t, ‖f s‖ / W s) ≤ ∫ s in a..t, ‖f s‖ / P s := by
    apply intervalIntegral.integral_mono_on ht.1
      ((hFW.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1)
      ((hF.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1)
    intro s hs
    have hsI : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
    have he : 1 ≤ Real.exp (μ * (s - a)) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hμ (sub_nonneg.mpr hs.1))
    have hPW : P s ≤ W s := by
      simpa only [W, mul_one] using mul_le_mul_of_nonneg_left he (hPpos s hsI).le
    exact div_le_div_of_nonneg_left (norm_nonneg _) (hPpos s hsI) hPW
  have h := hbase t ht
  rw [show W a = P a by simp [W]] at h
  have hout := h.trans (add_le_add_right hint (‖u a‖ / P a))
  calc
    ‖u t‖ ≤ (‖u a‖ / P a + ∫ s in a..t, ‖f s‖ / P s) * W t :=
      (div_le_iff₀ (hWpos t ht)).mp hout
    _ = _ := by dsimp [W]; ring

end PDE.Analysis.Evolution
