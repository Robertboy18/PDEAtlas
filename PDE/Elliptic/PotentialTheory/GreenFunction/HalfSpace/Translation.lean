/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GreenPotential

/-!
# Tangential translations of the half-space Green potential

A translation `y ↦ y + a` with `aₙ = 0` maps the upper half-space onto itself and commutes with the
reflection in its boundary, so the method-of-images Green function is invariant and the Green
potential commutes with the translation. The identity is one of total integrals and needs no
integrability of the source.

## Main results

* `halfSpaceGreenFunction_add_add`: `G(x + a, y + a) = G(x, y)` for `aₙ = 0`.
* `halfSpaceGreenPotential_comp_add`: for every source `f` and `aₙ = 0`, the potential of
  `f(· + a)` at `x` is the potential of `f` at `x + a`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open SobolevSpace

namespace GreenFunction

variable {n : ℕ} [Fact (0 < n)] {a : ℝ^n}

/-- The Green function of the half-space is invariant under translations parallel to the
boundary. -/
theorem halfSpaceGreenFunction_add_add (ha : a (PDE.Common.lastIndex (n := n)) = 0)
    (x y : ℝ^n) :
    halfSpaceGreenFunction (x + a) (y + a) = halfSpaceGreenFunction x y := by
  have hr : HalfSpace.reflect n (x + a) = HalfSpace.reflect n x + a := by
    rw [← HalfSpace.reflectLinearEquiv_apply, map_add, HalfSpace.reflectLinearEquiv_apply,
      HalfSpace.reflectLinearEquiv_apply, HalfSpace.reflect_eq_self_of_mem_boundary n ha]
  rw [halfSpaceGreenFunction, halfSpaceGreenFunction, hr, add_sub_add_right_eq_sub,
    add_sub_add_right_eq_sub]

/-- **The Green potential commutes with tangential translations**: for every source `f` and
`aₙ = 0`, the potential of `f(· + a)` at `x` is the potential of `f` at `x + a`. -/
theorem halfSpaceGreenPotential_comp_add (ha : a (PDE.Common.lastIndex (n := n)) = 0)
    (f : ℝ^n → ℝ) (x : ℝ^n) :
    halfSpaceGreenPotential (fun y ↦ f (y + a)) x = halfSpaceGreenPotential f (x + a) := by
  unfold halfSpaceGreenPotential
  symm
  rw [← (measurePreserving_add_right volume a).setIntegral_preimage_emb
    (MeasurableEquiv.addRight a).measurableEmbedding
    (fun y ↦ halfSpaceGreenFunction y (x + a) * f y),
    HalfSpace.preimage_add_eq_upper_of_last_eq_zero n a ha]
  refine setIntegral_congr_fun (HalfSpace.measurableSet_upper (n := n)) fun y _ ↦ ?_
  simp only [halfSpaceGreenFunction_add_add ha]

end GreenFunction
