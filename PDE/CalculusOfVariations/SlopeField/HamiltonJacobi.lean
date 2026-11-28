/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.CalculusOfVariations.SlopeField.Basic

/-!
# The eikonal of a slope field and the Hamilton–Jacobi equation

## Motivation

What equation does the eikonal `S` of a slope field solve, and does a solution of that equation
give a slope field back?

## The idea

The differential of an eikonal is the form of the field, so `S_y = L_q(x, y, p)` and
`S_x = L(x, y, p) - L_q(x, y, p) p`. When `L` is convex in the slope, the tangent plane at the
slope `p` lies below the graph, so `q ↦ S_y q - L(x, y, q)` is largest at `q = p`. Its largest
value is `-S_x`. With the Hamiltonian `H(x, y, π) = sup_q (π q - L(x, y, q))` this is the
Hamilton–Jacobi equation `S_x + H(x, y, S_y) = 0`.

Conversely, take a differentiable `S` and a slope function `Q` with `L_q(x, y, Q) = S_y`
(the momentum equation) and `S_x + S_y Q - L(x, y, Q) = 0`. Then `Q` is a slope field with
eikonal `S`: the two equations say that the differential of `S` is the form of `Q`.

## Main results

* `IsEikonal.isGreatest_hamiltonian` (all eikonals, Lagrangians that are convex in the slope
  and differentiable at the slope of the field): `-S_x` is the largest value of
  `q ↦ S_y q - L(x, y, q)`, attained at the slope of the field.
* `IsEikonal.hamiltonJacobi` (all, same premises): `S_x + sup_q (S_y q - L(x, y, q)) = 0`.
* `isEikonal_of_hamiltonJacobi` (construction): a solution of the momentum equation and of the
  Hamilton–Jacobi equation is the eikonal of the slope field `Q`.

## Relations

* `IsEikonal.hamiltonJacobi` is `IsEikonal.isGreatest_hamiltonian` read as a supremum.
* `isEikonal_of_hamiltonJacobi` produces the premise `IsEikonal` of the theorems of
  `PDE.CalculusOfVariations.SlopeField.Basic`; `isEikonal_centralField` in
  `PDE.Examples.CalculusOfVariations.CentralField` is an eikonal checked by hand.
* `PDE.CalculusOfVariations.legendreHamiltonian` is the Hamiltonian `⟪p, Q⟫ - L(Q, x)` of an
  inverse momentum map `Q` for a Lagrangian on a Hilbert space that does not depend on time;
  here the Hamiltonian is the supremum, and no inverse momentum map is assumed.

## What stays open

Existence of solutions of the Hamilton–Jacobi equation with given data on a curve transversal
to the field, which is how a field is built around a family of extremals.
-/

@[expose] public noncomputable section

open Set

namespace PDE.CalculusOfVariations.SlopeField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {L : ℝ × E → E → ℝ} {p : ℝ × E → E} {D : Set (ℝ × E)} {S : ℝ × E → ℝ} {z : ℝ × E}

/-- For the eikonal `S` of a slope field and a Lagrangian that is convex in the slope and
differentiable at the slope of the field, `-S_x` is the largest value of
`q ↦ S_y q - L(z, q)`, and it is attained at the slope of the field. The
derivative of `S` in `y` is the momentum of the field, and convexity puts the tangent plane of
`L` at the slope of the field below its graph. -/
theorem IsEikonal.isGreatest_hamiltonian (hS : IsEikonal L p D S) (hz : z ∈ D)
    (hconvex : ConvexOn ℝ univ (L z)) (hdiff : DifferentiableAt ℝ (L z) (p z)) :
    IsGreatest (range fun q : E ↦ fderiv ℝ S z (0, q) - L z q) (-fderiv ℝ S z (1, 0)) := by
  have hy (q : E) : fderiv ℝ S z (0, q) = momentum L p z q := by
    rw [(hS z hz).fderiv, beltramiForm_apply]
    simp
  have hx : fderiv ℝ S z (1, 0) = -energy L p z := by
    rw [(hS z hz).fderiv, beltramiForm_apply]
    simp
  constructor
  · exact ⟨p z, by simp only [hy, hx, energy]; ring⟩
  · rintro _ ⟨q, rfl⟩
    have h := weierstrassExcess_nonneg_of_convexOn hconvex hdiff q
    rw [weierstrassExcess, map_sub] at h
    change 0 ≤ L z q - L z (p z) - (momentum L p z q - momentum L p z (p z)) at h
    simp only [hy, hx, energy]
    linarith

/-- The eikonal of a slope field solves the Hamilton–Jacobi equation
`S_x + sup_q (S_y q - L(z, q)) = 0`, when the Lagrangian is convex in the slope and
differentiable at the slope of the field. -/
theorem IsEikonal.hamiltonJacobi (hS : IsEikonal L p D S) (hz : z ∈ D)
    (hconvex : ConvexOn ℝ univ (L z)) (hdiff : DifferentiableAt ℝ (L z) (p z)) :
    fderiv ℝ S z (1, 0) + ⨆ q : E, (fderiv ℝ S z (0, q) - L z q) = 0 := by
  have h := hS.isGreatest_hamiltonian hz hconvex hdiff
  rw [iSup, h.isLUB.csSup_eq h.nonempty]
  ring

/-- A differentiable function `S` and a slope function `Q` that solve the momentum equation
`L_q(z, Q) = S_y` and the equation `S_x + S_y Q - L(z, Q) = 0` on a region: `Q` is a slope
field with eikonal `S`. -/
theorem isEikonal_of_hamiltonJacobi {Q : ℝ × E → E}
    (hS : ∀ z ∈ D, DifferentiableAt ℝ S z)
    (hmomentum : ∀ z ∈ D, ∀ q : E, fderiv ℝ (L z) (Q z) q = fderiv ℝ S z (0, q))
    (hHJ : ∀ z ∈ D, fderiv ℝ S z (1, 0) + (fderiv ℝ S z (0, Q z) - L z (Q z)) = 0) :
    IsEikonal L Q D S := by
  intro z hz
  refine (hS z hz).hasFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v ↦ ?_)
  have hv : fderiv ℝ S z v = v.1 * fderiv ℝ S z (1, 0) + fderiv ℝ S z (0, v.2) := by
    rw [← smul_eq_mul, ← map_smul, ← map_add]
    simp
  rw [beltramiForm_apply, energy, momentum, hmomentum z hz, hmomentum z hz, hv]
  linear_combination v.1 * hHJ z hz

end PDE.CalculusOfVariations.SlopeField
