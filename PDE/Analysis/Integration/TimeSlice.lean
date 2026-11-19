/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.SpaceTime
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import PDE.Analysis.Integration.CompactByParts
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.PartialDeriv.Support

/-!
# Spatial integrals over time slices

For a function on spacetime whose time slices vanish outside one compact spatial set, the
spatial integral changes in time by the time integral of the spatial integral of its time
derivative. On one time slice, spatial derivatives integrate by parts and slice divergences
integrate to zero. Regularity is needed only at the points of the slices involved.
-/

@[expose] public section

namespace PDE.Analysis

open EuclideanSpace MeasureTheory PDE.Common

set_option linter.missingDocs true

variable {n : ℕ}

/-- A function continuous at every point of a slice and vanishing off a compact spatial set
is integrable on that slice. -/
theorem integrable_timeSlice_of_continuousAt {E : Type*} [NormedAddCommGroup E]
    {F : ℝ^(n + 1) → E} {K : Set (ℝ^n)} (hK : IsCompact K) (τ : ℝ)
    (hF : ∀ x, ContinuousAt F (timeSpaceCons τ x))
    (hFK : ∀ x, x ∉ K → F (timeSpaceCons τ x) = 0) :
    Integrable fun x ↦ F (timeSpaceCons τ x) := by
  have hc : ContinuousOn (fun x ↦ F (timeSpaceCons τ x)) K := fun x _ ↦
    ((hF x).comp (contDiff_timeSpaceCons_spatial n τ (m := 0)).continuous.continuousAt)
      |>.continuousWithinAt
  exact (hc.integrableOn_compact hK).integrable_of_forall_notMem_eq_zero hFK

/-- The fundamental theorem of calculus for spatial integrals over time slices. -/
theorem integral_timeSlice_sub_eq_intervalIntegral {G : ℝ^(n + 1) → ℝ} {K : Set (ℝ^n)}
    (hK : IsCompact K) (hGK : ∀ τ x, x ∉ K → G (timeSpaceCons τ x) = 0) {s t : ℝ}
    (hst : s ≤ t) (hG : ∀ τ ∈ Set.Icc s t, ∀ x, ContDiffAt ℝ 1 G (timeSpaceCons τ x)) :
    (∫ x, G (timeSpaceCons t x)) - ∫ x, G (timeSpaceCons s x) =
      ∫ τ in s..t, ∫ x, (∂[0] G) (timeSpaceCons τ x) := by
  have hderiv : ∀ τ ∈ Set.Icc s t, ∀ x,
      HasDerivAt (fun σ ↦ G (timeSpaceCons σ x)) ((∂[0] G) (timeSpaceCons τ x)) τ :=
    fun τ hτ x ↦ hasDerivAt_timeSpaceCons G τ x ((hG τ hτ x).differentiableAt one_ne_zero)
  have hD : ∀ τ ∈ Set.Icc s t, ∀ x, ContinuousAt (∂[0] G) (timeSpaceCons τ x) :=
    fun τ hτ x ↦ (hG τ hτ x).continuousAt_partialDeriv 0
  have hDK : ∀ τ ∈ Set.Icc s t, ∀ x, x ∉ K → (∂[0] G) (timeSpaceCons τ x) = 0 := by
    intro τ hτ x hx
    have hzero : (fun σ ↦ G (timeSpaceCons σ x)) = fun _ ↦ 0 :=
      funext fun σ ↦ hGK σ x hx
    have h0 : HasDerivAt (fun σ ↦ G (timeSpaceCons σ x)) 0 τ := by
      rw [hzero]
      exact hasDerivAt_const τ 0
    exact (hderiv τ hτ x).unique h0
  have hFTC : ∀ x, ∫ τ in s..t, (∂[0] G) (timeSpaceCons τ x) =
      G (timeSpaceCons t x) - G (timeSpaceCons s x) := by
    intro x
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro τ hτ
      rw [Set.uIcc_of_le hst] at hτ
      exact hderiv τ hτ x
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hst]
      intro τ hτ
      exact ((hD τ hτ x).comp (f := fun σ ↦ timeSpaceCons σ x)
        (hasDerivAt_timeSpaceCons_time n τ x).continuousAt).continuousWithinAt
  have hcont : ContinuousOn (Function.uncurry fun τ x ↦ (∂[0] G) (timeSpaceCons τ x))
      (Set.Icc s t ×ˢ Set.univ) := by
    rintro ⟨τ, x⟩ ⟨hτ, -⟩
    exact ((hD τ hτ x).comp (f := fun p : ℝ × ℝ^n ↦ timeSpaceCons p.1 p.2) (x := (τ, x))
      (contDiff_timeSpaceCons_uncurry n (m := 0)).continuous.continuousAt).continuousWithinAt
  have hint : Integrable (Function.uncurry fun τ x ↦ (∂[0] G) (timeSpaceCons τ x))
      ((volume.restrict (Set.uIoc s t)).prod volume) := by
    have hcompact : IntegrableOn (Function.uncurry fun τ x ↦ (∂[0] G) (timeSpaceCons τ x))
        (Set.Icc s t ×ˢ K) (volume.prod volume) :=
      (hcont.mono (Set.prod_mono subset_rfl (Set.subset_univ K))).integrableOn_compact
        (isCompact_Icc.prod hK)
    have hslab : IntegrableOn (Function.uncurry fun τ x ↦ (∂[0] G) (timeSpaceCons τ x))
        (Set.Icc s t ×ˢ Set.univ) (volume.prod volume) := by
      refine hcompact.of_forall_sdiff_eq_zero (measurableSet_Icc.prod MeasurableSet.univ) ?_
      rintro ⟨τ, x⟩ ⟨⟨hτ, -⟩, hx⟩
      exact hDK τ hτ x fun hxK ↦ hx ⟨hτ, hxK⟩
    rw [Set.uIoc_of_le hst, ← Measure.restrict_univ (μ := volume (α := ℝ^n)),
      Measure.prod_restrict]
    exact hslab.mono_set (Set.prod_mono Set.Ioc_subset_Icc_self subset_rfl)
  rw [intervalIntegral_integral_swap hint]
  simp_rw [hFTC]
  rw [integral_sub
    (integrable_timeSlice_of_continuousAt hK t (fun x ↦ (hG t ⟨hst, le_rfl⟩ x).continuousAt)
      fun x hx ↦ hGK t x hx)
    (integrable_timeSlice_of_continuousAt hK s (fun x ↦ (hG s ⟨le_rfl, hst⟩ x).continuousAt)
      fun x hx ↦ hGK s x hx)]

/-- Integration by parts in a spatial direction on one time slice. -/
theorem integral_timeSlice_partialDeriv_mul_eq_neg {f g : ℝ^(n + 1) → ℝ} (τ : ℝ) (j : Fin n)
    (hf : ∀ x, ContDiffAt ℝ 1 f (timeSpaceCons τ x))
    (hg : ∀ x, ContDiffAt ℝ 1 g (timeSpaceCons τ x))
    (hc : HasCompactSupport fun x ↦ g (timeSpaceCons τ x)) :
    (∫ x, (∂[j.succ] f) (timeSpaceCons τ x) * g (timeSpaceCons τ x)) =
      -∫ x, f (timeSpaceCons τ x) * (∂[j.succ] g) (timeSpaceCons τ x) := by
  have hf' : ∀ x, ContDiffAt ℝ 1 (fun y ↦ f (timeSpaceCons τ y)) x :=
    fun x ↦ (hf x).comp x (contDiff_timeSpaceCons_spatial n τ).contDiffAt
  have hg' : ContDiff ℝ 1 (fun y ↦ g (timeSpaceCons τ y)) :=
    contDiff_iff_contDiffAt.2 fun x ↦
      (hg x).comp x (contDiff_timeSpaceCons_spatial n τ).contDiffAt
  have ef : ∀ x, (∂[j.succ] f) (timeSpaceCons τ x) = (∂[j] fun y ↦ f (timeSpaceCons τ y)) x :=
    fun x ↦ (partialDeriv_timeSpaceCons_spatial j f τ x
      ((hf x).differentiableAt one_ne_zero)).symm
  have eg : ∀ x, (∂[j.succ] g) (timeSpaceCons τ x) = (∂[j] fun y ↦ g (timeSpaceCons τ y)) x :=
    fun x ↦ (partialDeriv_timeSpaceCons_spatial j g τ x
      ((hg x).differentiableAt one_ne_zero)).symm
  calc (∫ x, (∂[j.succ] f) (timeSpaceCons τ x) * g (timeSpaceCons τ x)) =
        ∫ x, g (timeSpaceCons τ x) * (∂[j] fun y ↦ f (timeSpaceCons τ y)) x := by
          congr 1
          funext x
          rw [ef, mul_comm]
    _ = -∫ x, (∂[j] fun y ↦ g (timeSpaceCons τ y)) x * f (timeSpaceCons τ x) :=
          integral_mul_partialDeriv_eq_neg_of_contDiffAt j hg' (fun x _ ↦ hf' x) hc
    _ = -∫ x, f (timeSpaceCons τ x) * (∂[j.succ] g) (timeSpaceCons τ x) := by
          congr 2
          funext x
          rw [eg, mul_comm]

/-- A slice divergence of compactly supported fields integrates to zero. -/
theorem integral_timeSlice_sum_partialDeriv_eq_zero {V : Fin n → ℝ^(n + 1) → ℝ} (τ : ℝ)
    (hV : ∀ j x, ContDiffAt ℝ 1 (V j) (timeSpaceCons τ x))
    (hc : ∀ j, HasCompactSupport fun x ↦ V j (timeSpaceCons τ x)) :
    (∫ x, ∑ j, (∂[j.succ] (V j)) (timeSpaceCons τ x)) = 0 := by
  have hone : ∀ x, ContDiffAt ℝ 1 (fun _ : ℝ^(n + 1) ↦ (1 : ℝ)) (timeSpaceCons τ x) :=
    fun _ ↦ contDiffAt_const
  have hzero : ∀ j, (∫ x, (∂[j.succ] (V j)) (timeSpaceCons τ x)) = 0 := by
    intro j
    have h := integral_timeSlice_partialDeriv_mul_eq_neg τ j hone (hV j) (hc j)
    simpa using h.symm
  have hint : ∀ j ∈ Finset.univ,
      Integrable fun x ↦ (∂[j.succ] (V j)) (timeSpaceCons τ x) := by
    intro j _
    have hslice : ContDiff ℝ 1 (fun y ↦ V j (timeSpaceCons τ y)) :=
      contDiff_iff_contDiffAt.2 fun x ↦
        (hV j x).comp x (contDiff_timeSpaceCons_spatial n τ).contDiffAt
    have heq : (fun x ↦ (∂[j.succ] (V j)) (timeSpaceCons τ x)) =
        ∂[j] fun y ↦ V j (timeSpaceCons τ y) :=
      funext fun x ↦ (partialDeriv_timeSpaceCons_spatial j (V j) τ x
        ((hV j x).differentiableAt one_ne_zero)).symm
    rw [heq]
    exact (hslice.continuous_partialDeriv j).integrable_of_hasCompactSupport
      ((hc j).partialDeriv j)
  rw [integral_finsetSum Finset.univ hint]
  exact Finset.sum_eq_zero fun j _ ↦ hzero j

/-- Spatial integrals of a function continuous on a closed slab and vanishing off a compact
spatial set depend continuously on time. -/
theorem continuousOn_integral_timeSlice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ^(n + 1) → E} {K : Set (ℝ^n)} (hK : IsCompact K) {s t : ℝ}
    (hF : ∀ τ ∈ Set.Icc s t, ∀ x, ContinuousAt F (timeSpaceCons τ x))
    (hFK : ∀ τ x, x ∉ K → F (timeSpaceCons τ x) = 0) :
    ContinuousOn (fun τ ↦ ∫ x, F (timeSpaceCons τ x)) (Set.Icc s t) := by
  have hcont : ContinuousOn (Function.uncurry fun τ x ↦ F (timeSpaceCons τ x))
      (Set.Icc s t ×ˢ Set.univ) := by
    rintro ⟨τ, x⟩ ⟨hτ, -⟩
    exact ((hF τ hτ x).comp (f := fun p : ℝ × ℝ^n ↦ timeSpaceCons p.1 p.2) (x := (τ, x))
      (contDiff_timeSpaceCons_uncurry n (m := 0)).continuous.continuousAt).continuousWithinAt
  exact continuousOn_integral_of_compact_support hK hcont fun τ x _ hx ↦ hFK τ x hx

end PDE.Analysis
