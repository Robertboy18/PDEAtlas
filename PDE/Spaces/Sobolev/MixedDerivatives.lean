/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Weighted.MixedDerivatives.Basic

/-!
# Calculus of mixed planar derivatives

Linearity and the coordinate-multiplier Leibniz rule for curried mixed derivatives.
The statements require only the displayed one-variable regularity at the point.
-/

@[expose] public section

open Filter
open scoped Topology
open PDE.Analysis (derivY)

namespace SobolevSpace.Weighted

/-- Exact Leibniz rule for a positive number of radial derivatives falling on
the coordinate multiplier `r`.  The coefficient is the radial derivative
count, and no higher multiplier terms occur because all derivatives of `r`
above order one vanish. -/
theorem mixedIteratedDeriv2D_radial_mul_succ
    (q ell : ℕ) (f : ℝ → ℝ → ℝ) (r z : ℝ)
    (hf : ContDiffAt ℝ (q + 1)
      (fun rho ↦ iteratedDeriv ell (f rho) z) r) :
    mixedIteratedDeriv2D (q + 1) ell (fun rho xi ↦ rho * f rho xi) r z =
      r * mixedIteratedDeriv2D (q + 1) ell f r z +
        (q + 1 : ℝ) * mixedIteratedDeriv2D q ell f r z := by
  simp only [mixedIteratedDeriv2D]
  have haxial :
      (fun rho ↦ iteratedDeriv ell (fun xi ↦ rho * f rho xi) z) =
        fun rho ↦ rho * iteratedDeriv ell (f rho) z := by
    funext rho
    exact iteratedDeriv_const_mul_field rho (f rho)
  rw [haxial]
  change iteratedDeriv (q + 1)
      (id * fun rho ↦ iteratedDeriv ell (f rho) z) r = _
  rw [iteratedDeriv_mul (n := q + 1)
    (contDiff_id.contDiffAt) hf]
  simp only [iteratedDeriv_id]
  rw [show q + 1 + 1 = q + 2 by omega]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem
    (show 0 ∈ Finset.range (q + 2) by simp)]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem
    (show 1 ∈ Finset.range (q + 2) \ {0} by simp)]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul,
    Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
  have hrest :
      ∑ i ∈ (Finset.range (q + 2) \ {0}) \ {1},
          (q + 1).choose i *
            (if i = 0 then r else if i = 1 then 1 else 0) *
              iteratedDeriv (q + 1 - i)
                (fun rho ↦ iteratedDeriv ell (f rho) z) r = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp_all
  rw [hrest, add_zero]
  simp

/-- With no radial derivatives, the radial coordinate remains an undifferentiated
multiplier. -/
theorem mixedIteratedDeriv2D_radial_mul_zero
    (ell : ℕ) (f : ℝ → ℝ → ℝ) (r z : ℝ) :
    mixedIteratedDeriv2D 0 ell (fun rho xi ↦ rho * f rho xi) r z =
      r * mixedIteratedDeriv2D 0 ell f r z := by
  simp [mixedIteratedDeriv2D, iteratedDeriv_const_mul_field]

/-- Mixed derivatives distribute over a sum under the precise one-variable
regularity needed by the curried definition. -/
theorem mixedIteratedDeriv2D_add
    (q ell : ℕ) (f g : ℝ → ℝ → ℝ) (r z : ℝ)
    (hfz : ∀ rho, ContDiffAt ℝ ell (f rho) z)
    (hgz : ∀ rho, ContDiffAt ℝ ell (g rho) z)
    (hfr : ContDiffAt ℝ q (fun rho ↦ iteratedDeriv ell (f rho) z) r)
    (hgr : ContDiffAt ℝ q (fun rho ↦ iteratedDeriv ell (g rho) z) r) :
    mixedIteratedDeriv2D q ell (fun rho xi ↦ f rho xi + g rho xi) r z =
      mixedIteratedDeriv2D q ell f r z +
        mixedIteratedDeriv2D q ell g r z := by
  simp only [mixedIteratedDeriv2D]
  have haxial :
      (fun rho ↦ iteratedDeriv ell (fun xi ↦ f rho xi + g rho xi) z) =
        fun rho ↦ iteratedDeriv ell (f rho) z + iteratedDeriv ell (g rho) z := by
    funext rho
    exact iteratedDeriv_add (hfz rho) (hgz rho)
  rw [haxial]
  exact iteratedDeriv_add hfr hgr

/-- At radial order zero, mixed-derivative additivity only needs axial
regularity, since no radial differentiation is performed. -/
theorem mixedIteratedDeriv2D_add_zero
    (ell : ℕ) (f g : ℝ → ℝ → ℝ) (r z : ℝ)
    (hfz : ContDiffAt ℝ ell (f r) z)
    (hgz : ContDiffAt ℝ ell (g r) z) :
    mixedIteratedDeriv2D 0 ell (fun rho xi ↦ f rho xi + g rho xi) r z =
      mixedIteratedDeriv2D 0 ell f r z +
        mixedIteratedDeriv2D 0 ell g r z := by
  simp only [mixedIteratedDeriv2D, iteratedDeriv_zero]
  exact iteratedDeriv_add hfz hgz

/-- Mixed derivatives commute with scalar negation. -/
theorem mixedIteratedDeriv2D_neg
    (q ell : ℕ) (f : ℝ → ℝ → ℝ) (r z : ℝ) :
    mixedIteratedDeriv2D q ell (fun rho xi ↦ -f rho xi) r z =
      -mixedIteratedDeriv2D q ell f r z := by
  simp [mixedIteratedDeriv2D]

/-- Two explicit axial derivatives can be absorbed into the axial count of a
mixed derivative. -/
theorem mixedIteratedDeriv2D_axial_two
    (q ell : ℕ) (f : ℝ → ℝ → ℝ) (r z : ℝ) :
    mixedIteratedDeriv2D q ell
        (derivY (derivY f)) r z =
      mixedIteratedDeriv2D q (ell + 2) f r z := by
  simp only [mixedIteratedDeriv2D, iteratedDeriv_eq_iterate]
  congr 2

end SobolevSpace.Weighted
