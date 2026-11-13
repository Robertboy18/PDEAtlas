/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.FixedPoint.Schauder
public import PDE.Analysis.Normed.Module.Ball.RadialProjection
public import PDE.Analysis.Topology.Compactness.BoundedImages

/-!
# Schaefer fixed points for continuous nonlinear compact maps

Let `A` be a continuous, not necessarily linear, self-map of a real normed space that takes
bounded sets to sets with compact closure. If the solutions of `x = t • A x` with `0 ≤ t ≤ 1`
form a bounded set, then `A` has a fixed point. This is Schaefer's fixed point theorem,
Evans, §9.2.2, Theorem 4, stated there in a Banach space.

## Main results

* `exists_isFixedPt_of_bounded_homotopy`: Schaefer's theorem, with compactness stated for
  images of bounded sets.
* `exists_isFixedPt_of_bounded_homotopy_of_subsequence`: the same with compactness stated for
  bounded sequences, as in Evans's definition of a compact mapping.

## How it works

We follow Evans's proof. We choose `R > 0` with `‖x‖ < R` for every solution of
`x = t • A x`, as in his (17), and compose `A` with the radial projection onto the closed ball
of radius `R`, his (18). Evans applies Schauder's theorem to the closed convex hull of the
image of the ball; we apply `exists_isFixedPt_of_isClosed_convex_of_isCompact_closure_image`
to the ball itself, so we do not need that hull to be compact. If the fixed point `x` had
`‖A x‖ > R`, it would solve `x = t • A x` with `t = R / ‖A x‖ < 1` and have `‖x‖ = R`,
contradicting the choice of `R`, as in (20).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §9.2.2, the definition of a compact mapping and
  Theorem 4 (Schaefer's fixed point theorem), p. 539, and its proof, (17)-(20), p. 540.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Metric Function Bornology Filter
open scoped Topology

namespace PDE.FixedPoint

open Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : E → E}

/-- Schaefer's fixed point theorem for a continuous nonlinear map taking every bounded
set into a set with compact closure. -/
theorem exists_isFixedPt_of_bounded_homotopy (hA : Continuous A)
    (hcompact : ∀ s : Set E, IsBounded s → IsCompact (closure (A '' s)))
    (hbound : IsBounded {x : E | ∃ t ∈ Icc (0 : ℝ) 1, x = t • A x}) :
    ∃ x, IsFixedPt A x := by
  obtain ⟨R, hR, hstrict⟩ := hbound.exists_pos_norm_lt
  let B := closedBall (0 : E) R
  let T : E → E := fun x ↦ radialProjection R (A x)
  have hT : Continuous T := (continuous_radialProjection hR).comp hA
  have hTB : MapsTo T B B := fun x _ ↦ radialProjection_mem_closedBall hR (A x)
  have hTC : IsCompact (closure (T '' B)) := by
    have hC := (hcompact B isBounded_closedBall).image (continuous_radialProjection hR)
    apply hC.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hC.isClosed
    rintro _ ⟨x, hx, rfl⟩
    exact mem_image_of_mem _ (subset_closure (mem_image_of_mem A hx))
  obtain ⟨x, _, hx⟩ := exists_isFixedPt_of_isClosed_convex_of_isCompact_closure_image
    (nonempty_closedBall.mpr hR.le) isClosed_closedBall (convex_closedBall (0 : E) R)
    hT.continuousOn hTB hTC
  change radialProjection R (A x) = x at hx
  refine ⟨x, ?_⟩
  by_cases hinside : ‖A x‖ ≤ R
  · rwa [radialProjection_eq_self hR hinside] at hx
  · have hout : R < ‖A x‖ := lt_of_not_ge hinside
    have hnorm : ‖x‖ = R := by
      rw [← hx]
      exact norm_radialProjection_of_le hR hout.le
    have hhom : x ∈ {y : E | ∃ t ∈ Icc (0 : ℝ) 1, y = t • A y} := by
      refine ⟨R / ‖A x‖, ⟨(div_pos hR (hR.trans hout)).le, ?_⟩, ?_⟩
      · exact (div_le_one (hR.trans hout)).mpr hout.le
      · rw [← radialProjection_eq_smul_of_le hout.le]
        exact hx.symm
    have := hstrict x hhom
    rw [hnorm] at this
    exact (lt_irrefl R this).elim

/-- Schaefer's theorem with compactness in the sense of Evans's definition: every bounded
sequence has a subsequence whose images converge. The space need not be complete. -/
theorem exists_isFixedPt_of_bounded_homotopy_of_subsequence (hA : Continuous A)
    (hcompact : ∀ u : ℕ → E, IsBounded (range u) →
      ∃ (y : E) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (A ∘ u ∘ φ) atTop (𝓝 y))
    (hbound : IsBounded {x : E | ∃ t ∈ Icc (0 : ℝ) 1, x = t • A x}) :
    ∃ x, IsFixedPt A x :=
  exists_isFixedPt_of_bounded_homotopy hA
    (isCompact_closure_image_bounded_iff_subsequence.mpr hcompact) hbound

end PDE.FixedPoint
