/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.CompactEnergy.Integration
public import PDE.Analysis.Integration.CompactByParts
import PDE.FDeriv.Calculus

/-! # Compact cutoffs for time derivatives and spatial divergence -/

@[expose] public noncomputable section

open MeasureTheory Set PDE.Common
open scoped ContDiff

namespace PDE.Analysis

variable {n : ℕ}

/-- A fixed compact cutoff supplies continuity without support conditions on the field. -/
theorem continuousOn_cutoffPairing {χ : ℝ^n → ℝ} {v : ℝ^(n + 1) → ℝ} {I : Set ℝ}
    (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hv : ∀ r ∈ I, ∀ x, ContinuousAt v (timeSpaceCons r x)) :
    ContinuousOn (fun r ↦ ∫ x, χ x * v (timeSpaceCons r x)) I := by
  apply continuousOn_integral_of_compact_support (f := fun r x ↦ χ x * v (timeSpaceCons r x))
    hc.isCompact
  · intro p hp
    exact ((hχ.continuousAt.comp continuous_snd.continuousAt).mul
      ((hv p.1 hp.1 p.2).comp (f := fun z : ℝ × ℝ^n ↦ timeSpaceCons z.1 z.2)
        (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.continuousAt)).continuousWithinAt
  · intro r x _ hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]

/-- Time differentiation only needs continuity of the spatial cutoff. -/
theorem hasDerivAt_cutoffPairing {χ : ℝ^n → ℝ} {v : ℝ^(n + 1) → ℝ} {I : Set ℝ}
    (hI : IsOpen I) (hχ : Continuous χ) (hc : HasCompactSupport χ)
    (hv : ∀ r ∈ I, ∀ x, ContDiffAt ℝ 1 v (timeSpaceCons r x))
    {r : ℝ} (hr : r ∈ I) :
    HasDerivAt (fun s ↦ ∫ x, χ x * v (timeSpaceCons s x))
      (∫ x, χ x * (∂[0] v) (timeSpaceCons r x)) r := by
  apply hasDerivAt_integral_of_locally_uniform_compact_support
    (f := fun r x ↦ χ x * v (timeSpaceCons r x))
    (D := fun r x ↦ χ x * (∂[0] v) (timeSpaceCons r x)) hI hc.isCompact
  · intro p hp
    exact ((hχ.continuousAt.comp continuous_snd.continuousAt).mul
      ((hv p.1 hp.1 p.2).continuousAt.comp (f := fun z : ℝ × ℝ^n ↦ timeSpaceCons z.1 z.2)
        (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.continuousAt)).continuousWithinAt
  · intro p hp
    exact ((hχ.continuousAt.comp continuous_snd.continuousAt).mul
      ((contDiffAt_partialDeriv 0 (hv p.1 hp.1 p.2) 0).continuousAt.comp
        (f := fun z : ℝ × ℝ^n ↦ timeSpaceCons z.1 z.2)
        (contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.continuousAt)).continuousWithinAt
  · intro s hs x
    exact (hasDerivAt_timeSpaceCons v s x
      ((hv s hs x).differentiableAt one_ne_zero)).const_mul (χ x)
  · intro s _ x hx
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  · exact hr

/-- Spatial integration by parts moves the full divergence onto the compact cutoff. -/
theorem integral_cutoff_spatialDivergence {χ : ℝ^n → ℝ}
    {F : Fin n → ℝ^(n + 1) → ℝ} (r : ℝ)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (hF : ∀ j x, ContDiffAt ℝ 1 (F j) (timeSpaceCons r x)) :
    (∫ x, χ x * ∑ j : Fin n, (∂[j.succ] (F j)) (timeSpaceCons r x)) =
      -∑ j : Fin n, ∫ x, (∂[j] χ) x * F j (timeSpaceCons r x) := by
  have hs (j : Fin n) : ContDiff ℝ 1 (fun x ↦ F j (timeSpaceCons r x)) :=
    contDiff_iff_contDiffAt.mpr fun x ↦ (hF j x).comp x
      (contDiff_timeSpaceCons_spatial n r).contDiffAt
  have hd (j : Fin n) (x : ℝ^n) := partialDeriv_timeSpaceCons_spatial j (F j) r x
    ((hF j x).differentiableAt one_ne_zero)
  simp_rw [← hd, Finset.mul_sum]
  rw [integral_finsetSum]
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact integral_mul_partialDeriv_eq_neg j hχ (hs j) hc
  · intro j _
    have hdj : Continuous (∂[j] (fun x ↦ F j (timeSpaceCons r x))) :=
      ((hs j).partialDeriv j (k := 0) (by norm_num)).continuous
    exact (hχ.continuous.mul hdj).integrable_of_hasCompactSupport hc.mul_right

end PDE.Analysis
