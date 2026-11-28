/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.Trilinear
public import PDE.Fluid.NavierStokes.Stationary.WeakUniqueness

/-!
# Skew symmetry of the convection form on `H¹(ℝ³)³`

For an advecting field `u` in `H¹(ℝ³)³` with zero weak divergence, the convection form
`b(u, v, w) = ∫ (u·∇)v·w` vanishes on the diagonal, `b(u, v, v) = 0`, and changes sign when `v`
and `w` are exchanged. No field has to be bounded, compactly supported or zero anywhere. The
statements are in dimension three, the dimension of `mulH1`; the product of two `H¹` functions is
in `L²` up to dimension four.

## Main results

All for fields of `H¹(ℝ³)³`.

* `integral_convectionTerm`, `convectionTrilinear_eq_sum_inner`: the form as a sum of `L²`
  pairings, `b(u, v, w) = ∑ₖ ∑ᵢ ⟪uᵢ wₖ, ∂ᵢvₖ⟫`.
* `convectionTrilinear_self_eq_zero`: `b(u, v, v) = 0` for a divergence-free `u`.
* `convectionTrilinear_skew`: `b(u, v, w) = -b(u, w, v)` for a divergence-free `u`.

## How it works

Each term `∫ uᵢ ∂ᵢvₖ wₖ` of the form is the `L²` pairing of the product `uᵢ wₖ` with `∂ᵢvₖ`. For
`w = v` the sum over `i` of these pairings is `∫ u·∇(vₖ² / 2)`, which vanishes for a
divergence-free `u` (`sum_inner_mulH1_partial_self_eq_zero`: first for smooth compactly supported
`vₖ`, from the weak divergence of `u`, then for all of `H¹(ℝ³)` by density). Expanding
`b(u, v + w, v + w) = 0` gives `b(u, v, w) = -b(u, w, v)`. On a bounded domain the same
cancellation is `IncompressibleFlow.l4Convection_energy_eq_zero_of_sobolev`, for a transported
field with zero boundary values, and `Euler.sobolevConvectionPairing_skew` is the case of an
advecting field in `W^{1,∞}`.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev SobolevSpace.WholeSpaceHilbert

namespace NavierStokes.Stationary

set_option linter.missingDocs true

local notation "E" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))

/-- The `(k, i)` term of the convection form is integrable and is the `L²` pairing of the
product `uᵢ wₖ` with `∂ᵢvₖ`. -/
theorem integral_convectionTerm (u v w : E) (k i : Fin 3) :
    Integrable (fun x ↦ representative u x i * gradientRepresentative v x k i *
      representative w x k) volume ∧
    ∫ x, representative u x i * gradientRepresentative v x k i * representative w x k =
      inner ℝ (mulH1 (u i) (w k)) (gradientCLM v k i) := by
  refine integrable_and_integral_eq_inner (mulH1_ae (u i) (w k)) Filter.EventuallyEq.rfl ?_
  filter_upwards with x
  simp only [representative_apply, massCLM_apply, baseRepresentative, wkpBaseCoordinateCLM_apply,
    gradientRepresentative]
  ring

/-- The convection form as a sum of `L²` pairings:
`b(u, v, w) = ∑ₖ ∑ᵢ ⟪uᵢ wₖ, ∂ᵢvₖ⟫`. -/
theorem convectionTrilinear_eq_sum_inner (u v w : E) :
    convectionTrilinear u v w =
      ∑ k : Fin 3, ∑ i : Fin 3, inner ℝ (mulH1 (u i) (w k)) (gradientCLM v k i) := by
  rw [convectionTrilinear_eq_integral, integral_finsetSum _ fun k _ ↦
    integrable_finsetSum _ fun i _ ↦ (integral_convectionTerm u v w k i).1]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_finsetSum _ fun i _ ↦ (integral_convectionTerm u v w k i).1]
  exact Finset.sum_congr rfl fun i _ ↦ (integral_convectionTerm u v w k i).2

/-- **The energy cancellation of the convection form.** For a divergence-free advecting field
`u` in `H¹(ℝ³)³` and every `v` in `H¹(ℝ³)³`, `b(u, v, v) = ∫ (u·∇)v·v = 0`. No field has to be
bounded or compactly supported. -/
theorem convectionTrilinear_self_eq_zero {u : E} (hu : divergenceCLM u = 0) (v : E) :
    convectionTrilinear u v v = 0 := by
  rw [convectionTrilinear_eq_sum_inner]
  exact Finset.sum_eq_zero fun k _ ↦ sum_inner_mulH1_partial_self_eq_zero u hu (v k)

/-- **Skew symmetry of the convection form.** For a divergence-free advecting field `u` in
`H¹(ℝ³)³`, `b(u, v, w) = -b(u, w, v)` for all `v`, `w` in `H¹(ℝ³)³`. -/
theorem convectionTrilinear_skew {u : E} (hu : divergenceCLM u = 0) (v w : E) :
    convectionTrilinear u v w = -convectionTrilinear u w v := by
  have h := convectionTrilinear_self_eq_zero hu (v + w)
  simp only [map_add, add_apply] at h
  rw [convectionTrilinear_self_eq_zero hu v, convectionTrilinear_self_eq_zero hu w] at h
  linarith only [h]

end NavierStokes.Stationary
