/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Common.Euclidean

/-!
# Spacetime domains for incompressible flow

Finite-time and nonnegative-time subsets of `ℝ^(n + 1)`. Coordinate `0` is time. The canonical
strictly positive domain is `PDE.Common.positiveTimeDomain`. These domains are shared by Euler and
Navier–Stokes initial-value problems. Slices at times in `(0,T)` lie in the finite-time slab, and
the spatial shadow of a compactly supported spacetime function is compact.
-/

@[expose] public section

namespace IncompressibleFlow

open EuclideanSpace
open scoped Topology

set_option linter.missingDocs true

/-- Positive-time finite slab `(0,T) × ℝ^n`. -/
def finiteTimeDomain (n : ℕ) (T : ℝ) : Set (ℝ^(n + 1)) :=
  {x | 0 < x 0 ∧ x 0 < T}

/-- Closed physical spacetime domain `[0,∞) × ℝ^n`. -/
def globalDomain (n : ℕ) : Set (ℝ^(n + 1)) :=
  {x | 0 ≤ x 0}

/-- Membership in a finite-time slab implies strictly positive time. -/
theorem finiteTimeDomain.time_pos {n : ℕ} {T : ℝ}
    {x : ℝ^(n + 1)} (hx : x ∈ finiteTimeDomain n T) :
    0 < x 0 :=
  hx.1

/-- Membership in a finite-time slab places time below the horizon. -/
theorem finiteTimeDomain.time_lt {n : ℕ} {T : ℝ}
    {x : ℝ^(n + 1)} (hx : x ∈ finiteTimeDomain n T) :
    x 0 < T :=
  hx.2

/-- Every finite-time slab is open. -/
theorem isOpen_finiteTimeDomain (n : ℕ) (T : ℝ) :
    IsOpen (finiteTimeDomain n T) := by
  change IsOpen
    (((EuclideanSpace.proj (0 : Fin (n + 1)) : ℝ^(n + 1) →L[ℝ] ℝ) ⁻¹'
      Set.Ioi 0) ∩
      ((EuclideanSpace.proj (0 : Fin (n + 1)) : ℝ^(n + 1) →L[ℝ] ℝ) ⁻¹'
        Set.Iio T))
  exact
    (isOpen_Ioi.preimage
      (EuclideanSpace.proj (0 : Fin (n + 1)) : ℝ^(n + 1) →L[ℝ] ℝ).continuous).inter
      (isOpen_Iio.preimage
        (EuclideanSpace.proj (0 : Fin (n + 1)) : ℝ^(n + 1) →L[ℝ] ℝ).continuous)

/-- At a strictly positive time, the closed physical domain is a neighborhood. -/
theorem globalDomain_mem_nhds {n : ℕ} {x : ℝ^(n + 1)}
    (hx : x ∈ PDE.Common.positiveTimeDomain (n := n)) :
    globalDomain n ∈ 𝓝 x := by
  apply Filter.mem_of_superset (PDE.Common.isOpen_positiveTimeDomain.mem_nhds hx)
  intro y hy
  change 0 ≤ y 0
  exact (show 0 < y 0 from hy).le

/-- Membership in the closed physical domain implies nonnegative time. -/
theorem globalDomain.time_nonneg {n : ℕ}
    {x : ℝ^(n + 1)} (hx : x ∈ globalDomain n) :
    0 ≤ x 0 :=
  hx

/-- Every finite-time slab lies in the closed physical domain. -/
theorem finiteTimeDomain.subset_global {n : ℕ} (T : ℝ) :
    finiteTimeDomain n T ⊆ globalDomain n := by
  intro x hx
  exact (finiteTimeDomain.time_pos hx).le

/-- Every initial-time point belongs to the closed physical domain. -/
theorem timeSpaceCons_zero_mem_globalDomain {n : ℕ} (x : ℝ^n) :
    PDE.Common.timeSpaceCons 0 x ∈ globalDomain n := by
  change 0 ≤ (PDE.Common.timeSpaceCons 0 x) 0
  simp

/-- Points of a slice at a time in `(0,T)` lie in the open slab. -/
theorem timeSpaceCons_mem_finiteTimeDomain {n : ℕ} {T τ : ℝ} (hτ : τ ∈ Set.Ioo 0 T)
    (x : ℝ^n) : PDE.Common.timeSpaceCons τ x ∈ finiteTimeDomain n T := by
  simpa [finiteTimeDomain] using hτ

/-- The spatial shadow of the support of a compactly supported spacetime function is compact. -/
theorem isCompact_spatialPart_image_tsupport {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {φ : ℝ^(n + 1) → E} (hφ : HasCompactSupport φ) :
    IsCompact (PDE.Common.spatialPart '' tsupport φ) := by
  have h : (PDE.Common.spatialPart : ℝ^(n + 1) → ℝ^n) = PDE.Common.spatialPartCLM n :=
    funext fun z ↦ (PDE.Common.spatialPartCLM_eq_spatialPart n z).symm
  rw [h]
  exact hφ.isCompact.image (PDE.Common.spatialPartCLM n).continuous

/-- A spatial point outside the shadow of the support gives slice points outside the
support. -/
theorem timeSpaceCons_notMem_tsupport {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {φ : ℝ^(n + 1) → E} {x : ℝ^n} (hx : x ∉ PDE.Common.spatialPart '' tsupport φ) (τ : ℝ) :
    PDE.Common.timeSpaceCons τ x ∉ tsupport φ :=
  fun h ↦ hx ⟨_, h, PDE.Common.spatialPart_timeSpaceCons τ x⟩

end IncompressibleFlow
