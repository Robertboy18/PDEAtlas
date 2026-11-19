/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.ConvolutionTime.SourceDerivatives
import PDE.Parabolic.Heat.ConvolutionSpace.JointContinuity
import PDE.Analysis.Integration.ParametricInterval
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Time differentiation from spatial source derivatives

The heat equation supplies the time derivative of each source slice’s evolution.
A uniform Lipschitz bound permits differentiation under the integral; the moving endpoint
then contributes the source itself. No source-time derivative enters this argument.
-/

@[expose] public section

open Set MeasureTheory Filter PDE.Common
open scoped Interval Topology

namespace HeatEquation

variable {n : ℕ}

/-- The time derivative is the source at the moving endpoint plus the heat evolution of its
Laplacian. Only continuity in source time is required. -/
theorem hasDerivAt_integral_initialValueSolution_of_spatial_jets
    (g : ℝ → ℝ^n → ℝ)
    (hg : Continuous (Function.uncurry g))
    (hg2 : ∀ s, ContDiff ℝ 2 (g s)) (hgc : ∀ s, HasCompactSupport (g s))
    {M : ℝ} (hbound : ∀ s x, ‖g s x‖ ≤ M)
    (hsecond : ∀ i : Fin n, Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (∂[i] (g p.1))) p.2))
    (C : Fin n → ℝ)
    (hC : ∀ i s x, ‖(∂[i] (∂[i] (g s))) x‖ ≤ C i)
    (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (fun τ ↦ ∫ s in 0..τ, initialValueSolution (g s) x (τ - s))
      (g t x + ∫ s in 0..t,
        ∑ i : Fin n, initialValueSolution (∂[i] (∂[i] (g s)))
          x (t - s)) t := by
  let H : ℝ → ℝ → ℝ := fun τ s ↦ initialValueSolution (g s) x (τ - s)
  let D : ℝ → ℝ := fun s ↦
    ∑ i : Fin n, initialValueSolution (∂[i] (∂[i] (g s))) x (t - s)
  have hheat := continuous_initialValueSolution_family hg (fun p ↦ hbound p.1 p.2)
  have hH : Continuous (Function.uncurry H) :=
    hheat.comp (continuous_snd.prodMk
      (continuous_const.prodMk (continuous_fst.sub continuous_snd)))
  have hH_slice (τ : ℝ) : Continuous (H τ) :=
    hH.comp (continuous_const.prodMk continuous_id)
  have hD : Continuous D := by
    apply continuous_finsetSum
    intro i _
    exact (continuous_initialValueSolution_family (hsecond i)
      (fun p ↦ hC i p.1 p.2)).comp
        (continuous_id.prodMk (continuous_const.prodMk (continuous_const.sub continuous_id)))
  have hslice_lipschitz (s : ℝ) :
      LipschitzWith (Real.nnabs (∑ i, C i))
        (fun r ↦ initialValueSolution (g s) x r) :=
    lipschitzWith_initialValueSolution_time_of_second_bound
      (g s) (hg2 s) (hgc s) C
      (fun i y ↦ by simpa only [Real.norm_eq_abs] using hC i s y) x
  have hfixed :
      HasDerivAt (fun τ ↦ ∫ s in 0..t, H τ s) (∫ s in 0..t, D s) t := by
    apply (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
      (F := H) (F' := D) (bound := fun _ : ℝ ↦ ∑ i, C i)
      (x₀ := t) (s := univ) (a := 0) (b := t)
      Filter.univ_mem
      (Eventually.of_forall fun τ ↦ (hH_slice τ).aestronglyMeasurable.restrict)
      ((hH_slice t).intervalIntegrable 0 t)
      hD.aestronglyMeasurable.restrict
      (by
        filter_upwards with s _
        rw [lipschitzOnWith_iff_dist_le_mul]
        intro τ₁ _ τ₂ _
        simpa [H, Real.dist_eq] using
          (hslice_lipschitz s).dist_le_mul (τ₁ - s) (τ₂ - s))
      (continuous_const.intervalIntegrable 0 t)
      (by
        filter_upwards [volume.ae_ne t] with s hst
        intro hs
        have hsIoc : s ∈ Ioc (0 : ℝ) t := by simpa [uIoc_of_le ht.le] using hs
        have hst' : s < t := lt_of_le_of_ne hsIoc.2 hst
        simpa [H, D] using
          (hasDerivAt_initialValueSolution_time_sourceSecond
            (g s) (hg2 s) (hgc s) x (t - s) (sub_pos.mpr hst')).comp_sub_const t s)).2
  have hmoving :=
    (PDE.Analysis.hasFDerivAt_intervalIntegral_moving_right
      H 0 id t (hasFDerivAt_id t) hfixed.hasFDerivAt hH.continuousAt
      (hH_slice t).aestronglyMeasurable.stronglyMeasurableAtFilter
      (Eventually.of_forall fun τ ↦
        ⟨(hH_slice τ).intervalIntegrable 0 t, (hH_slice τ).intervalIntegrable t τ,
          (hH_slice t).intervalIntegrable t τ⟩)).hasDerivAt
  simpa [H, D, initialValueSolution_of_t_eq_zero] using hmoving

/-- The time derivative formula with the finite Laplacian sum taken outside the integral. -/
theorem hasDerivAt_integral_initialValueSolution_of_spatial_jets_sum
    (g : ℝ → ℝ^n → ℝ)
    (hg : Continuous (Function.uncurry g))
    (hg2 : ∀ s, ContDiff ℝ 2 (g s)) (hgc : ∀ s, HasCompactSupport (g s))
    {M : ℝ} (hbound : ∀ s x, ‖g s x‖ ≤ M)
    (hsecond : ∀ i : Fin n, Continuous
      (fun p : ℝ × ℝ^n ↦ (∂[i] (∂[i] (g p.1))) p.2))
    (C : Fin n → ℝ)
    (hC : ∀ i s x, ‖(∂[i] (∂[i] (g s))) x‖ ≤ C i)
    (x : ℝ^n) (t : ℝ) (ht : 0 < t) :
    HasDerivAt
      (fun τ ↦ ∫ s in 0..τ, initialValueSolution (g s) x (τ - s))
      (g t x + ∑ i : Fin n, ∫ s in 0..t,
        initialValueSolution (∂[i] (∂[i] (g s)))
          x (t - s)) t := by
  have hint (i : Fin n) : IntervalIntegrable
      (fun s ↦ initialValueSolution (∂[i] (∂[i] (g s)))
        x (t - s)) volume 0 t :=
    ((continuous_initialValueSolution_family (hsecond i) (fun p ↦ hC i p.1 p.2)).comp
      (continuous_id.prodMk
        (continuous_const.prodMk (continuous_const.sub continuous_id)))).intervalIntegrable 0 t
  simpa only [intervalIntegral.integral_finsetSum (fun i _ ↦ hint i)] using
    hasDerivAt_integral_initialValueSolution_of_spatial_jets
      g hg hg2 hgc hbound hsecond C hC x t ht

end HeatEquation
