/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import PDE.Parabolic.Heat.Duhamel.Representation
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import PDE.Analysis.Integration.ParametricInterval
import PDE.Parabolic.Heat.ConvolutionTime

/-!
# Time differentiation of Duhamel's formula

The moving endpoint contributes the current source value `f(t, x)`. We obtain the
remaining term by differentiating the heat evolution under the source-time integral.
Local domination and continuity at the singular corner supply the hypotheses of the
shared moving-interval integration theorem.
-/

@[expose] public section

namespace HeatEquation

open scoped Pointwise Topology Interval
open PDE.Common
open MeasureTheory

variable {n : ℕ}

/-- The moving-boundary derivative in Duhamel's formula follows from dominated
differentiation on the fixed interval and continuity at the singular corner.

The local Lipschitz majorant is the domination condition for differentiating the
homogeneous heat evolution in its positive time variable. This proves the Leibniz identity
that `nonhomogeneousSolution_positive_time_residual` takes as the hypothesis `hleibniz`. -/
theorem hasDerivAt_nonhomogeneousSolution_of_dominated
    (f : ℝ^(n + 1) → ℝ)
    (x : ℝ^n) (t : ℝ) (ht : 0 < t)
    (hf_cont : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      Continuous fun y : ℝ^n ↦
        f (timeSpaceCons (n := n) s y))
    (hf_bdd : ∀ s ∈ Set.Ioo (0 : ℝ) t,
      ∃ M : ℝ, ∀ y : ℝ^n,
        |f (timeSpaceCons (n := n) s y)| ≤ M)
    (S : Set ℝ) (hS : S ∈ 𝓝 t) (bound : ℝ → ℝ)
    (hH_meas : ∀ᶠ τ in 𝓝 t,
      AEStronglyMeasurable
        (fun s ↦
          initialValueSolution (n := n)
            (fun y : ℝ^n ↦
              f (timeSpaceCons (n := n) s y))
            x (τ - s))
        (volume.restrict (Ι (0 : ℝ) t)))
    (hH_int : IntervalIntegrable
      (fun s ↦
        initialValueSolution (n := n)
          (fun y : ℝ^n ↦
            f (timeSpaceCons (n := n) s y))
          x (t - s))
      volume 0 t)
    (hD_meas : AEStronglyMeasurable
      (fun s ↦
        deriv
          (fun r ↦
            initialValueSolution (n := n)
              (fun y : ℝ^n ↦
                f (timeSpaceCons (n := n) s y))
              x r)
          (t - s))
      (volume.restrict (Ι (0 : ℝ) t)))
    (h_lipsch : ∀ᵐ s ∂volume, s ∈ Ι (0 : ℝ) t →
      LipschitzOnWith (Real.nnabs (bound s))
        (fun τ ↦
          initialValueSolution (n := n)
            (fun y : ℝ^n ↦
              f (timeSpaceCons (n := n) s y))
            x (τ - s))
        S)
    (hbound : IntervalIntegrable bound volume 0 t)
    (hcorner : ContinuousAt
      (fun p : ℝ × ℝ ↦
        initialValueSolution (n := n)
          (fun y : ℝ^n ↦
            f (timeSpaceCons (n := n) p.2 y))
          x (p.1 - p.2))
      (t, t))
    (hcorner_meas : StronglyMeasurableAtFilter
      (fun s ↦
        initialValueSolution (n := n)
          (fun y : ℝ^n ↦
            f (timeSpaceCons (n := n) s y))
          x (t - s))
      (𝓝 t) volume)
    (htail : ∀ᶠ τ in 𝓝 t,
      IntervalIntegrable
          (fun s ↦
            initialValueSolution (n := n)
              (fun y : ℝ^n ↦
                f (timeSpaceCons (n := n) s y))
              x (τ - s))
          volume 0 t ∧
        IntervalIntegrable
          (fun s ↦
            initialValueSolution (n := n)
              (fun y : ℝ^n ↦
                f (timeSpaceCons (n := n) s y))
              x (τ - s))
          volume t τ ∧
        IntervalIntegrable
          (fun s ↦
            initialValueSolution (n := n)
              (fun y : ℝ^n ↦
                f (timeSpaceCons (n := n) s y))
              x (t - s))
          volume t τ) :
    HasDerivAt (fun τ ↦ nonhomogeneousSolution (n := n) f x τ)
      (f (timeSpaceCons (n := n) t x) +
        ∫ s in Set.Icc 0 t,
          deriv
            (fun r ↦
              initialValueSolution (n := n)
                (fun y : ℝ^n ↦
                  f (timeSpaceCons (n := n) s y))
                x r)
            (t - s))
      t := by
  let H : ℝ → ℝ → ℝ := fun τ s ↦
    initialValueSolution (n := n) (fun y : ℝ^n ↦ f (timeSpaceCons (n := n) s y)) x (τ - s)
  let D : ℝ → ℝ := fun s ↦ deriv (fun r ↦ initialValueSolution (n := n)
    (fun y : ℝ^n ↦ f (timeSpaceCons (n := n) s y)) x r) (t - s)
  have hdiff : ∀ᵐ s ∂volume, s ∈ Ι (0 : ℝ) t → HasDerivAt (H · s) (D s) t := by
    filter_upwards [volume.ae_ne t] with s hst hs
    rw [Set.uIoc_of_le ht.le] at hs
    have hs' : s ∈ Set.Ioo (0 : ℝ) t := ⟨hs.1, hs.2.lt_of_ne hst⟩
    have htime := hasDerivAt_initialValueSolution_time (n := n) _ x (t - s)
      (sub_pos.mpr hs'.2) (hf_cont s hs') (hf_bdd s hs')
    simpa only [H, D, Function.comp_def, htime.deriv] using htime.comp_sub_const t s
  have hfixed := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip (F := H) (F' := D)
    hS hH_meas hH_int hD_meas h_lipsch hbound hdiff).2
  have hmoving : HasDerivAt (fun τ ↦ ∫ s in (0 : ℝ)..τ, H τ s)
      (H t t + ∫ s in (0 : ℝ)..t, D s) t := by
    simpa using (PDE.Analysis.hasFDerivAt_intervalIntegral_moving_right (H := H) (a := 0)
      (g := id) (p := t) (hg := hasFDerivAt_id t) (hfixed := hfixed.hasFDerivAt)
      (hcorner := hcorner) (hcorner_meas := hcorner_meas) (hint := htail)).hasDerivAt
  have hsolution : (fun τ ↦ nonhomogeneousSolution (n := n) f x τ) =ᶠ[𝓝 t]
      fun τ ↦ ∫ s in (0 : ℝ)..τ, H τ s := by
    filter_upwards [eventually_gt_nhds ht] with τ hτ
    rw [nonhomogeneousSolution_eq_integral_initialValueSolution (n := n) f x τ hτ,
      intervalIntegral.integral_of_le hτ.le, ← integral_Icc_eq_integral_Ioc]
  simpa [H, D, initialValueSolution_of_t_eq_zero, intervalIntegral.integral_of_le ht.le,
    ← integral_Icc_eq_integral_Ioc] using hmoving.congr_of_eventuallyEq hsolution

end HeatEquation
