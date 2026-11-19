/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Integral.Reaction.Cylinder
public import PDE.Analysis.MeasureTheory.Lp.Distance
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Reaction estimates from L²-valued traces

The spacetime estimate depends only on the L² classes and almost-everywhere
agreement with their joint representatives. A finite spatial submeasure can
select the superlevel set without changing the ambient L² trace bound.
-/

@[expose] public section

open MeasureTheory Filter Set

namespace MeasureTheory

/-- Restricting the spatial measure only decreases the squared distance between
representatives of two L² classes. -/
theorem integral_sq_sub_le_dist_sq_of_ae_eq
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X} (hν : ν ≤ μ)
    (F G : Lp ℝ 2 μ) {f g : X → ℝ}
    (hf : (F : X → ℝ) =ᵐ[μ] f) (hg : (G : X → ℝ) =ᵐ[μ] g) :
    (∫ x, (f x - g x) ^ 2 ∂ν) ≤ dist F G ^ 2 := by
  rw [dist_sq_eq_integral_sq_sub_of_ae_eq F G hf hg]
  exact integral_mono_measure hν (.of_forall (fun x ↦ sq_nonneg (f x - g x)))
    (((Lp.memLp F).ae_eq hf).sub ((Lp.memLp G).ae_eq hg)).integrable_sq

/-- A joint representative of an L² trace with a linear distance bound has a
square-integrable displacement on every finite spatial submeasure. -/
theorem integrable_sq_sub_of_lp_trace_bound
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X} [IsFiniteMeasure ν]
    (hν : ν ≤ μ) {U : ℝ → Lp ℝ 2 μ} {G : Lp ℝ 2 μ}
    {u : ℝ × X → ℝ} {g : X → ℝ} {K τ : ℝ} (hτ : 0 ≤ τ)
    (hmeas : AEStronglyMeasurable (fun z ↦ u z - g z.2)
      ((volume.restrict (Ioc 0 τ)).prod ν))
    (hsection : ∀ᵐ t ∂volume.restrict (Ioc 0 τ),
      (U t : X → ℝ) =ᵐ[μ] fun x ↦ u (t, x))
    (hg : (G : X → ℝ) =ᵐ[μ] g)
    (hdist : ∀ᵐ t ∂volume.restrict (Ioc 0 τ), dist (U t) G ≤ K * t) :
    Integrable (fun z ↦ (u z - g z.2) ^ 2)
      ((volume.restrict (Ioc 0 τ)).prod ν) := by
  apply (integrable_prod_iff (hmeas.pow 2)).2
  constructor
  · filter_upwards [hsection] with t ht
    exact ((((Lp.memLp (U t)).ae_eq ht).sub ((Lp.memLp G).ae_eq hg)).integrable_sq).mono_measure hν
  · apply (integrable_const (K ^ 2 * τ ^ 2)).mono'
      ((hmeas.pow 2).norm.integral_prod_right')
    filter_upwards [hsection, hdist, ae_restrict_mem measurableSet_Ioc] with t ht hdt htm
    simp only [Pi.pow_apply, Real.norm_of_nonneg (sq_nonneg _),
      Real.norm_of_nonneg (integral_nonneg fun x ↦ sq_nonneg (u (t, x) - g x))]
    calc
      (∫ x, (u (t, x) - g x) ^ 2 ∂ν) ≤ dist (U t) G ^ 2 :=
        integral_sq_sub_le_dist_sq_of_ae_eq hν (U t) G ht hg
      _ ≤ (K * t) ^ 2 := pow_le_pow_left₀ dist_nonneg hdt 2
      _ = K ^ 2 * t ^ 2 := mul_pow _ _ _
      _ ≤ K ^ 2 * τ ^ 2 := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ htm.1.le hτ).2 htm.2) (sq_nonneg K)

/-- An L²-valued trace bounds the reaction on every finite spatial superlevel
set. Spacetime integrability of the displacement is a conclusion of the trace
bound, rather than an additional premise. -/
theorem mul_sub_le_integral_reaction_sq_of_lp_trace_bound
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X} [IsFiniteMeasure ν]
    (hν : ν ≤ μ) {U : ℝ → Lp ℝ 2 μ} {G : Lp ℝ 2 μ}
    {u : ℝ × X → ℝ} {g : X → ℝ} {f : ℝ → ℝ} {a b d K τ : ℝ}
    (hb : 0 ≤ b) (hd : 0 ≤ d) (hτ : 0 ≤ τ)
    (hlevel : ∀ᵐ x ∂ν, a + d ≤ g x) (hf : ∀ z : ℝ, a ≤ z → b ≤ |f z|)
    (hmeas : AEStronglyMeasurable (fun z ↦ u z - g z.2)
      ((volume.restrict (Ioc 0 τ)).prod ν))
    (hsection : ∀ᵐ t ∂volume.restrict (Ioc 0 τ),
      (U t : X → ℝ) =ᵐ[μ] fun x ↦ u (t, x))
    (hg : (G : X → ℝ) =ᵐ[μ] g)
    (hdist : ∀ᵐ t ∂volume.restrict (Ioc 0 τ), dist (U t) G ≤ K * t)
    (hr : Integrable (fun z ↦ (f (u z)) ^ 2)
      ((volume.restrict (Ioc 0 τ)).prod ν)) :
    b ^ 2 * (d ^ 2 * τ * ν.real univ - K ^ 2 * τ ^ 3) ≤
      d ^ 2 * (∫ z, (f (u z)) ^ 2 ∂(volume.restrict (Ioc 0 τ)).prod ν) := by
  apply mul_sub_le_integral_prod_reaction_sq hb hd hτ hlevel hf
    (integrable_sq_sub_of_lp_trace_bound hν hτ hmeas hsection hg hdist) hr
  filter_upwards [hsection, hdist] with t ht hdt
  calc
    (∫ x, (u (t, x) - g x) ^ 2 ∂ν) ≤ dist (U t) G ^ 2 :=
      integral_sq_sub_le_dist_sq_of_ae_eq hν (U t) G ht hg
    _ ≤ (K * t) ^ 2 := pow_le_pow_left₀ dist_nonneg hdt 2
    _ = K ^ 2 * t ^ 2 := mul_pow _ _ _

end MeasureTheory
