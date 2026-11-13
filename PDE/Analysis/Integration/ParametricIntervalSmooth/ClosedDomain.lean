/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Integration.ParametricIntervalSmooth.Local
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Parameter integrals on closed convex domains

Continuous integrands on a closed strip have continuous parameter integrals.
For smooth integrands, the interior derivative formula extends to the boundary
by the mean value theorem on a convex domain. This gives relative smoothness
without assuming a smooth extension outside the domain.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Interval Topology

namespace PDE.Analysis

universe u v

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {Y : Type v} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {S : Set X} {a b : ℝ}

/-- The parameter derivative of an interval integral extends to a closed convex
domain with nonempty interior when both the integrand and its derivative are
continuous on the closed strip. -/
theorem hasFDerivWithinAt_intervalIntegral_of_continuousOn
    (hS : IsClosed S) (hconv : Convex ℝ S) (hne : (interior S).Nonempty)
    {H : X × ℝ → Y} {D : X × ℝ → X →L[ℝ] Y}
    (hH : ContinuousOn H (S ×ˢ uIcc a b))
    (hD : ContinuousOn D (S ×ˢ uIcc a b))
    (hd : ∀ x ∈ S, ∀ t ∈ uIcc a b,
      HasFDerivWithinAt (fun y ↦ H (y, t)) (D (x, t)) S x)
    {x : X} (hx : x ∈ S) :
    HasFDerivWithinAt (fun y ↦ ∫ t in a..b, H (y, t))
      (∫ t in a..b, D (x, t)) S x := by
  have hcl : closure (interior S) = S :=
    (hconv.closure_interior_eq_closure_of_nonempty_interior hne).trans hS.closure_eq
  have hi (y : X) (hy : y ∈ interior S) :
      HasFDerivAt (fun z ↦ ∫ t in a..b, H (z, t)) (∫ t in a..b, D (y, t)) y :=
    hasFDerivAt_intervalIntegral_of_continuousOn
      (F := fun y t ↦ H (y, t)) (D := fun y t ↦ D (y, t)) isOpen_interior
      (hH.mono (prod_mono interior_subset subset_rfl))
      (hD.mono (prod_mono interior_subset subset_rfl))
      (fun z hz t ht ↦ (hd z (interior_subset hz) t ht).hasFDerivAt
        (mem_of_superset (isOpen_interior.mem_nhds hz) interior_subset)) hy
  rw [← hcl]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy ↦ (hi y hy).differentiableAt.differentiableWithinAt)
    hconv.interior isOpen_interior
  · intro y hy
    exact (continuousOn_intervalIntegral hH y (hcl ▸ hy)).mono interior_subset
  · apply ((continuousOn_intervalIntegral hD x hx).mono interior_subset).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hi y hy).fderiv.symm

/-- Finite smoothness of interval integrals on a closed convex parameter domain. -/
private theorem contDiffOn_intervalIntegral_closed_nat
    {Y : Type (max u v)} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (hS : IsClosed S) (hconv : Convex ℝ S) (hne : (interior S).Nonempty)
    (hab : a ≠ b) {k : ℕ} {H : X × ℝ → Y}
    (hH : ContDiffOn ℝ k H (S ×ˢ uIcc a b)) :
    ContDiffOn ℝ k (fun x ↦ ∫ t in a..b, H (x, t)) S := by
  induction k generalizing Y with
  | zero => exact contDiffOn_zero.mpr (continuousOn_intervalIntegral hH.continuousOn)
  | succ k ih =>
    let D : X × ℝ → X →L[ℝ] Y := fun p ↦
      (fderivWithin ℝ H (S ×ˢ uIcc a b) p).comp (ContinuousLinearMap.inl ℝ X ℝ)
    have hs := uniqueDiffOn_convex hconv hne
    have hprod := hs.prod (uniqueDiffOn_uIcc hab)
    have hD : ContDiffOn ℝ k D (S ×ˢ uIcc a b) :=
      (hH.fderivWithin hprod (by simp)).clm_comp contDiffOn_const
    have hi (x : X) (hx : x ∈ S) :
        HasFDerivWithinAt (fun y ↦ ∫ t in a..b, H (y, t))
          (∫ t in a..b, D (x, t)) S x := by
      apply hasFDerivWithinAt_intervalIntegral_of_continuousOn hS hconv hne
        hH.continuousOn hD.continuousOn ?_ hx
      intro y hy t ht
      have hp : HasFDerivWithinAt (fun z : X ↦ (z, t))
          (ContinuousLinearMap.inl ℝ X ℝ) S y :=
        (hasFDerivAt_prodMk_left (𝕜 := ℝ) y t).hasFDerivWithinAt
      have hd := (hH.differentiableOn (by simp) (y, t) ⟨hy, ht⟩).hasFDerivWithinAt
      exact hd.comp y hp (show MapsTo (fun z : X ↦ (z, t)) S (S ×ˢ uIcc a b) from
        fun _ hz ↦ ⟨hz, ht⟩)
    rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderivWithin hs]
    refine ⟨fun x hx ↦ (hi x hx).differentiableWithinAt, by simp, ?_⟩
    exact (ih hD).congr fun x hx ↦ (hi x hx).fderivWithin (hs x hx)

/-- Integration preserves every finite order and infinite smoothness relative
to a closed convex parameter domain with nonempty interior. The integrand is
required to be smooth only on the closed strip. -/
theorem contDiffOn_intervalIntegral_closed
    [CompleteSpace Y] (hS : IsClosed S) (hconv : Convex ℝ S)
    (hne : (interior S).Nonempty) {n : ℕ∞} {H : X × ℝ → Y}
    (hH : ContDiffOn ℝ n H (S ×ˢ uIcc a b)) :
    ContDiffOn ℝ n (fun x ↦ ∫ t in a..b, H (x, t)) S := by
  by_cases hab : a = b
  · subst b
    simpa only [intervalIntegral.integral_same] using
      (contDiffOn_const : ContDiffOn ℝ n (fun _ : X ↦ (0 : Y)) S)
  let e : ULift.{u} Y ≃ₗᵢ[ℝ] Y := LinearIsometryEquiv.ulift ℝ Y
  have hlift : ContDiffOn ℝ n (fun x ↦ ∫ t in a..b, e.symm (H (x, t))) S := by
    have hH := e.symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hH
    induction n using ENat.recTopCoe with
    | top =>
      rw [contDiffOn_infty] at hH ⊢
      exact fun k ↦ contDiffOn_intervalIntegral_closed_nat hS hconv hne hab (hH k)
    | coe k => exact contDiffOn_intervalIntegral_closed_nat hS hconv hne hab hH
  apply (e.toContinuousLinearEquiv.contDiff.comp_contDiffOn hlift).congr
  intro x _
  simpa only [Function.comp_apply, LinearIsometryEquiv.coe_toLinearIsometry,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, e.apply_symm_apply] using
    e.toLinearIsometry.intervalIntegral_comp_comm
      (fun t ↦ e.symm (H (x, t))) (a := a) (b := b) (μ := volume)

end PDE.Analysis
