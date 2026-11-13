/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SpaceTime.Support
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import PDE.FDeriv.PartialDeriv.Regularity
import PDE.FDeriv.SpaceTime

/-!
# Actual Schwartz data at an interior time

Smoothness on an open forward band and speed-one support give compact smooth
displacement and velocity at each positive time. The same construction applies
to every actual coordinate derivative without a separate derivative-support assumption.
-/

@[expose] public noncomputable section

open Set PDE PDE.Common PDE.Analysis
open scoped ContDiff SchwartzMap

namespace PDE.Analysis

/-- Interior Cauchy data of a smooth field with forward support are actual Schwartz
functions, including its time velocity. No smoothness at the terminal time is needed. -/
theorem exists_schwartz_cauchyData_of_forward_support
    {n : ℕ} {u : ℝ^(n + 1) → ℝ} {T R t : ℝ}
    (hu : ContDiffOn ℝ ∞ u {p | 0 < p 0 ∧ p 0 < T})
    (hsupport : ∀ q ∈ Ioo 0 T, ∀ x : ℝ^n,
      R + q < ‖x‖ → u (timeSpaceCons q x) = 0)
    (ht : t ∈ Ioo 0 T) :
    ∃ g h : 𝓢(ℝ^n, ℝ),
      (∀ x, u (timeSpaceCons t x) = g x) ∧
      ∀ x, (∂[0] u) (timeSpaceCons t x) = h x := by
  have hopen : IsOpen {p : ℝ^(n + 1) | 0 < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hv : ContDiffOn ℝ ∞ (∂[0] u) {p | 0 < p 0 ∧ p 0 < T} :=
    hu.partialDeriv 0 hopen (by simp)
  have hg : ContDiff ℝ ∞ (fun x ↦ u (timeSpaceCons t x)) :=
    hu.comp_contDiff (contDiff_timeSpaceCons_spatial n t) (fun _ ↦ by simpa using ht)
  have hh : ContDiff ℝ ∞ (fun x ↦ (∂[0] u) (timeSpaceCons t x)) :=
    hv.comp_contDiff (contDiff_timeSpaceCons_spatial n t) (fun _ ↦ by simpa using ht)
  have hcompact (f : ℝ^n → ℝ) (hf : ∀ x, R + T < ‖x‖ → f x = 0) :
      HasCompactSupport f := by
    apply (isCompact_closedBall (0 : ℝ^n) (R + T)).of_isClosed_subset
      (isClosed_tsupport _)
    apply closure_minimal ?_ Metric.isClosed_closedBall
    intro x hx
    by_contra hnot
    have hx' : R + T < ‖x‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hnot
    exact hx (hf x hx')
  have hgc := hcompact _ (fun x hx ↦ hsupport t ht x (by linarith [ht.2]))
  have hhc := hcompact _ (fun _ hx ↦ partialDeriv_eq_zero_of_forward_support
    hsupport ht 0 hx)
  exact ⟨hgc.toSchwartzMap hg, hhc.toSchwartzMap hh, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- The same data construction applies to every actual coordinate derivative.
Its support follows from the original field, including for the time derivative. -/
theorem exists_schwartz_partialDeriv_cauchyData_of_forward_support
    {n : ℕ} {u : ℝ^(n + 1) → ℝ} {T R t : ℝ}
    (hu : ContDiffOn ℝ ∞ u {p | 0 < p 0 ∧ p 0 < T})
    (hsupport : ∀ q ∈ Ioo 0 T, ∀ x : ℝ^n,
      R + q < ‖x‖ → u (timeSpaceCons q x) = 0)
    (ht : t ∈ Ioo 0 T) (i : Fin (n + 1)) :
    ∃ g h : 𝓢(ℝ^n, ℝ),
      (∀ x, (∂[i] u) (timeSpaceCons t x) = g x) ∧
      ∀ x, (∂[0] (∂[i] u)) (timeSpaceCons t x) = h x := by
  have hopen : IsOpen {p : ℝ^(n + 1) | 0 < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  apply exists_schwartz_cauchyData_of_forward_support
    (hu.partialDeriv i hopen (by simp)) (R := R + T) ?_ ht
  intro q hq x hx
  exact partialDeriv_eq_zero_of_forward_support hsupport hq i
    (by linarith [hq.1])

end PDE.Analysis
