/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import PDE.Hyperbolic.Classical.EnergyIdentity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import PDE.FDeriv.Calculus
import PDE.FDeriv.SpaceTime
import Mathlib.Data.Nat.Choose.Multinomial
import PDE.Analysis.Integration.CompactByParts

/-!
# Spatial integration by parts for semilinear wave virial identities

On a compactly supported fixed-time slice, coordinatewise integration by
parts identifies the spatial Laplacian term with minus the squared spatial
gradient:

`∫ u(t, x) Δₓu(t, x) dx = -∫ ‖Dₓu(t, x)‖² dx`.

This is the integration by parts in (4) of the proof of Evans, §12.5.1, Theorem 1, which uses the
compact support of `u(t, ·)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.5.1, proof of Theorem 1, equation (4).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter Finset MeasureTheory Set
open scoped BigOperators

namespace WaveEquation

variable {n : ℕ}

/-- Spatial integration by parts on a fixed-time slice:

`∫ u(t, x) Δₓu(t, x) dx = -∫ ‖Dₓu(t, x)‖² dx`.

The Laplacian is written as the coordinate sum appearing in
`waveOperator`. Compact support of the slice removes every boundary term. -/
theorem integral_mul_sum_spatial_secondDeriv_eq_neg_gradient_sq {u : ℝ^(n + 1) → ℝ} (t : ℝ)
    (hu : ∀ x : ℝ^n, ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) t x))
    (hcompact : HasCompactSupport (fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons (n := n) t x))) :
    (∫ x : ℝ^n, u (PDE.Common.timeSpaceCons (n := n) t x) *
      ∑ i : Fin n, (∂[i.succ] (fun p ↦ (∂[i.succ] u) p)) (PDE.Common.timeSpaceCons (n := n) t x)) =
      -∫ x : ℝ^n,
        ‖classicalWaveSpatialGradient (n := n) u (PDE.Common.timeSpaceCons (n := n) t x)‖ ^ 2 := by
  have hv : ContDiff ℝ 2 fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons t x) :=
    contDiff_iff_contDiffAt.mpr fun x ↦ (hu x).comp x
      (PDE.Common.contDiff_timeSpaceCons_spatial n t).contDiffAt
  have hd (i : Fin n) : ContDiff ℝ 1 fun x : ℝ^n ↦ (∂[i.succ] u) (PDE.Common.timeSpaceCons t x) :=
    contDiff_iff_contDiffAt.mpr fun x ↦ (PDE.contDiffAt_partialDeriv 1 (hu x) i.succ).comp x
      (PDE.Common.contDiff_timeSpaceCons_spatial n t).contDiffAt
  have hpartial (i : Fin n) : (∂[i] fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons t x)) =
      fun x ↦ (∂[i.succ] u) (PDE.Common.timeSpaceCons t x) :=
    funext fun x ↦ PDE.partialDeriv_timeSpaceCons_spatial i u t x
      ((hu x).differentiableAt (by norm_num))
  have hsecond (i : Fin n) (x : ℝ^n) :
      (∂[i] fun x ↦ (∂[i.succ] u) (PDE.Common.timeSpaceCons t x)) x =
        (∂[i.succ] fun p ↦ (∂[i.succ] u) p) (PDE.Common.timeSpaceCons t x) :=
    PDE.partialDeriv_timeSpaceCons_spatial i (fun p ↦ (∂[i.succ] u) p) t x
      ((PDE.contDiffAt_partialDeriv 1 (hu x) i.succ).differentiableAt one_ne_zero)
  have hsupp (i : Fin n) :
      HasCompactSupport fun x ↦ (∂[i.succ] u) (PDE.Common.timeSpaceCons t x) := by
    rw [← hpartial i]
    exact hcompact.fderiv_apply ℝ _
  simp only [mul_sum, ← hsecond]
  rw [integral_finsetSum _ fun i _ ↦ by exact (hv.continuous.mul (PDE.contDiff_partialDeriv_of_succ
    (m := 0) (hd i)).continuous).integrable_of_hasCompactSupport (μ := volume) hcompact.mul_right]
  simp only [PDE.Analysis.integral_mul_partialDeriv_eq_neg _ (hv.of_le (by norm_num)) (hd _)
    hcompact, hpartial, sum_neg_distrib]
  rw [← integral_finsetSum _ fun i _ ↦ by
    exact ((hd i).continuous.mul (hd i).continuous).integrable_of_hasCompactSupport (μ := volume)
      (hsupp i).mul_right]
  congr 2 with x
  simp only [← pow_two, EuclideanSpace.real_norm_sq_eq, classicalWaveSpatialGradient_apply]

end WaveEquation
