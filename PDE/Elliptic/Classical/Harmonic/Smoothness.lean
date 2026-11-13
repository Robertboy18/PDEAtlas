/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.Harmonic.PoissonRepresentation

/-!
# Interior smoothness of harmonic functions

A classical harmonic function starts with only two continuous derivatives.
On a small ball, uniqueness identifies it with its Poisson extension. The
extension is smooth away from the boundary, so the original function has every
interior derivative as well. This is the regularity step behind the derivative
estimates in Evans, §2.2.3. Evans proves smoothness (his Theorem 6) by mollifying with a radial
kernel and using the mean-value property; we use the Poisson representation
`IsHarmonicPDE.exists_poisson_representation` instead.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.3, Theorem 6 (Smoothness), p. 28; §2.2.4, Theorem 15
  (Poisson's formula for ball), p. 41.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

namespace LaplacianEquation

open Filter Metric Set
open scoped Topology ContDiff

/-- A `C²` harmonic function on an open set has every derivative order there.
In particular, `m = ∞` gives interior smoothness from the original harmonicity
hypothesis alone. -/
theorem IsHarmonicPDE.contDiffOn_of_isOpen {m : ℕ∞} {n : ℕ} [Fact (0 < n)]
    {u : ℝ^n → ℝ} {U : Set (ℝ^n)} (hu : IsHarmonicPDE n u U) (hU : IsOpen U) :
    ContDiffOn ℝ m u U := by
  intro x hx
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hr : 0 < R / 2 := half_pos hR
  have hclosed : closedBall x (R / 2) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hR)).trans hball
  obtain ⟨g, _, hrepresentation⟩ := hu.exists_poisson_representation hr hclosed
  have hpoisson : ContDiffAt ℝ m (GreenFunction.poissonBallExtension (R / 2) g) (x - x) := by
    simpa only [sub_self] using
      GreenFunction.contDiffAt_poissonBallExtension hr g.continuous.continuousOn
        (mem_ball_self hr)
  have hsmooth : ContDiffAt ℝ m
      (fun y ↦ GreenFunction.poissonBallExtension (R / 2) g (y - x)) x :=
    hpoisson.comp (f := fun y : ℝ^n ↦ y - x) x
      (contDiffAt_id.sub contDiffAt_const)
  apply (hsmooth.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [ball_mem_nhds x hr] with y hy
  have hshift : y - x ∈ ball (0 : ℝ^n) (R / 2) := by
    simpa only [mem_ball, dist_eq_norm, sub_zero] using hy
  simpa [add_sub_assoc, add_comm x y] using hrepresentation hshift

end LaplacianEquation
