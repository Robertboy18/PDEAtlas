/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Prod
public import PDE.Analysis.MeasureTheory.Integral.Reaction.Superlevel
import CAS.ExactTactic

/-!
# Reaction bounds on a spacetime cylinder

A Lipschitz L² trace limits the spacetime distance from the initial datum. The
superlevel estimate then forces a lower bound for the squared reaction integral.
The spatial measure may already be restricted to a small superlevel set.
-/

@[expose] public section

open MeasureTheory Filter Set

namespace MeasureTheory

/-- A linear L² trace bound gives a cubic bound for the spacetime integral of
its squared distance. The estimate uses only `t ≤ τ` on the time interval. -/
theorem integral_prod_sq_sub_le_of_integral_sq_sub_le
    {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν]
    {u : ℝ × X → ℝ} {g : X → ℝ} {K τ : ℝ} (hτ : 0 ≤ τ)
    (hu : Integrable (fun z ↦ (u z - g z.2) ^ 2)
      ((volume.restrict (Ioc 0 τ)).prod ν))
    (hdist : ∀ᵐ t ∂volume.restrict (Ioc 0 τ),
      (∫ x, (u (t, x) - g x) ^ 2 ∂ν) ≤ K ^ 2 * t ^ 2) :
    (∫ z, (u z - g z.2) ^ 2 ∂(volume.restrict (Ioc 0 τ)).prod ν) ≤
      K ^ 2 * τ ^ 3 := by
  rw [integral_prod _ hu]
  have hbound : ∀ᵐ t ∂volume.restrict (Ioc 0 τ),
      (∫ x, (u (t, x) - g x) ^ 2 ∂ν) ≤ K ^ 2 * τ ^ 2 := by
    filter_upwards [hdist, ae_restrict_mem measurableSet_Ioc] with t ht htmem
    exact ht.trans (mul_le_mul_of_nonneg_left
      (sq_le_sq₀ htmem.1.le hτ |>.2 htmem.2) (sq_nonneg K))
  have hi := integral_mono_ae hu.integral_prod_left
    (integrable_const (K ^ 2 * τ ^ 2)) hbound
  have hm : (volume.restrict (Ioc 0 τ)).real univ = τ := by
    rw [measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le hτ, sub_zero]
  simp only [integral_const, smul_eq_mul, hm] at hi
  calc
    _ ≤ τ * (K ^ 2 * τ ^ 2) := hi
    _ = K ^ 2 * τ ^ 3 := by cas

/-- An initial superlevel set forces a reaction integral unless the L² trace
moves far enough from its initial value. This bound uses the actual product
measure and the actual reaction; no evolution equation is assumed. -/
theorem mul_sub_le_integral_prod_reaction_sq
    {X : Type*} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν]
    {u : ℝ × X → ℝ} {g : X → ℝ} {f : ℝ → ℝ} {a b d K τ : ℝ}
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hτ : 0 ≤ τ)
    (hg : ∀ᵐ x ∂ν, a + d ≤ g x) (hf : ∀ z : ℝ, a ≤ z → b ≤ |f z|)
    (hu : Integrable (fun z ↦ (u z - g z.2) ^ 2)
      ((volume.restrict (Ioc 0 τ)).prod ν))
    (hr : Integrable (fun z ↦ (f (u z)) ^ 2)
      ((volume.restrict (Ioc 0 τ)).prod ν))
    (hdist : ∀ᵐ t ∂volume.restrict (Ioc 0 τ),
      (∫ x, (u (t, x) - g x) ^ 2 ∂ν) ≤ K ^ 2 * t ^ 2) :
    b ^ 2 * (d ^ 2 * τ * ν.real univ - K ^ 2 * τ ^ 3) ≤
      d ^ 2 * (∫ z, (f (u z)) ^ 2 ∂(volume.restrict (Ioc 0 τ)).prod ν) := by
  have hprod : ∀ᵐ z ∂(volume.restrict (Ioc 0 τ)).prod ν,
      a + d ≤ g z.2 := Measure.quasiMeasurePreserving_snd.ae hg
  have hi := mul_measure_le_integral_sq_sub_add_reaction hb hd hprod hf hu hr
  have htrace := integral_prod_sq_sub_le_of_integral_sq_sub_le hτ hu hdist
  have hm : ((volume.restrict (Ioc 0 τ)).prod ν).real univ = τ * ν.real univ := by
    rw [← univ_prod_univ, measureReal_prod_prod, measureReal_restrict_apply_univ,
      Real.volume_real_Ioc_of_le hτ, sub_zero]
  rw [hm] at hi
  nlinarith [mul_le_mul_of_nonneg_left htrace (sq_nonneg b)]

end MeasureTheory
