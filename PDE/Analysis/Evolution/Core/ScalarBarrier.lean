/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Scalar barriers with an end condition at negative infinity

Let `u : ℝ → ℝ` be differentiable with `u' = v` and `u(t) → a` as `t → -∞`. If
`a < c` and `v(t) < 0` whenever `u(t) = c`, then `u ≤ c` everywhere. The proof
picks a time at which `u < c` and applies the finite-interval first-contact
theorem. The symmetric statement holds for `c < a` with `v > 0` on the level.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace PDE.Analysis.Evolution.Scalar

/-- A strictly negative velocity at a level prevents a complete differentiable
curve with a lower left limit from crossing that level upwards. -/
theorem le_of_tendsto_atBot_of_deriv_neg_at_level
    {u v : ℝ → ℝ} {a c : ℝ} (hu : ∀ t, HasDerivAt u (v t) t)
    (ha : Tendsto u atBot (𝓝 a)) (hac : a < c)
    (hlevel : ∀ t, u t = c → v t < 0) (t : ℝ) : u t ≤ c := by
  obtain ⟨s, hs, hst⟩ :=
    ((ha.eventually_lt_const hac).and (eventually_le_atBot t)).exists
  apply image_le_of_deriv_right_lt_deriv_boundary
    (fun x _ ↦ (hu x).continuousAt.continuousWithinAt)
    (fun x _ ↦ (hu x).hasDerivWithinAt) hs.le
    (fun x ↦ hasDerivAt_const x c)
    (fun x _ hx ↦ hlevel x hx) ⟨hst, le_rfl⟩

/-- A strictly positive velocity at a level prevents a complete differentiable
curve with a higher left limit from crossing that level downwards. -/
theorem le_of_tendsto_atBot_of_deriv_pos_at_level
    {u v : ℝ → ℝ} {a c : ℝ} (hu : ∀ t, HasDerivAt u (v t) t)
    (ha : Tendsto u atBot (𝓝 a)) (hca : c < a)
    (hlevel : ∀ t, u t = c → 0 < v t) (t : ℝ) : c ≤ u t := by
  have h := le_of_tendsto_atBot_of_deriv_neg_at_level
    (fun s ↦ (hu s).neg) ha.neg (neg_lt_neg hca) (fun s hs ↦
      neg_neg_of_pos (hlevel s (neg_injective hs))) t
  exact neg_le_neg_iff.mp h

end PDE.Analysis.Evolution.Scalar
