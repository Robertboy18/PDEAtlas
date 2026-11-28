/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Analysis.Variational.ValidatedNonlinear

/-!
# Validated solutions when the nonlinearity is quadratic: the explicit radius

A coercive bilinear form with constant `κ`, a load of size `β` and a nonlinearity bounded by
`a ‖u‖²` give the scalar inequality `κ ‖u*‖ ≤ β + a ‖u‖²` for the iteration `u ↦ u*` of
`exists_solution_of_compact_embedding`. The ball of radius `r` is kept as soon as
`β + a r² ≤ κ r`, and the smallest such `r` is the smaller root of `a r² - κ r + β`, which is
real when `κ² - 4 β a ≥ 0`. This is the radius of Theorem 3 of Hou, Wang and Yang, and with it
the equation has a solution in that ball. `exists_solution_near_quadratic` is the case of a
nonlinearity given by a bounded bilinear map, with the scalar inequality as a hypothesis.

## Main results

* `quadraticRadius κ a β`: the smaller root `(κ - √(κ² - 4 β a)) / (2 a)`.
* `quadraticRadius_budget`: for `a ≠ 0` and `κ² - 4 β a ≥ 0` the radius is a root,
  `β + a r² = κ r`.
* `exists_solution_of_quadratic_bound`: on a real Hilbert space with a compact injective map into
  a normed space, the equation `B u + N u = ℓ` has a solution with
  `‖u‖ ≤ quadraticRadius κ a β`.

## How it works

With that radius, `exists_solution_of_compact_embedding` applies with the identity as
reconstruction. The bound `|N u w| ≤ a ‖u‖² ‖w‖` gives the dual norm of `N u` on the ball, the
continuity estimate in the weaker norm gives the Lipschitz bound there, and the budget
`‖ℓ‖ + a r² ≤ κ r` holds because `r` is a root.

## References

* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 3.2.3, Theorem 3,
  (3.17) and (3.18). <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

namespace PDE.Analysis.Variational

/-- The smaller root of `a r² - κ r + β`: the radius `(κ - √(κ² - 4 β a)) / (2 a)` of the
smallest ball that the scalar inequality `κ r* ≤ β + a r²` keeps. -/
def quadraticRadius (κ a β : ℝ) : ℝ :=
  (κ - √(κ ^ 2 - 4 * β * a)) / (2 * a)

/-- The radius is a root: `β + a r² = κ r`. -/
theorem quadraticRadius_budget {κ a β : ℝ} (ha : a ≠ 0) (hdisc : 0 ≤ κ ^ 2 - 4 * β * a) :
    β + a * quadraticRadius κ a β ^ 2 = κ * quadraticRadius κ a β := by
  have hr : 2 * a * quadraticRadius κ a β = κ - √(κ ^ 2 - 4 * β * a) :=
    mul_div_cancel₀ _ (mul_ne_zero two_ne_zero ha)
  have hs : √(κ ^ 2 - 4 * β * a) ^ 2 = κ ^ 2 - 4 * β * a := Real.sq_sqrt hdisc
  have key : 4 * a * (β + a * quadraticRadius κ a β ^ 2 - κ * quadraticRadius κ a β) = 0 := by
    linear_combination (2 * a * quadraticRadius κ a β - κ - √(κ ^ 2 - 4 * β * a)) * hr + hs
  have h := (mul_eq_zero.mp key).resolve_left (mul_ne_zero four_ne_zero ha)
  linarith

/-- The radius is nonnegative when `κ`, `a` are positive and `β` is nonnegative. -/
theorem quadraticRadius_nonneg {κ a β : ℝ} (hκ : 0 ≤ κ) (ha : 0 < a) (hβ : 0 ≤ β) :
    0 ≤ quadraticRadius κ a β := by
  refine div_nonneg (sub_nonneg.mpr (Real.sqrt_le_iff.mpr ⟨hκ, ?_⟩)) (by positivity)
  nlinarith [mul_nonneg hβ ha.le]

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Validated solutions for a quadratic nonlinearity, with the explicit radius.** Let `B` be
a bounded bilinear form on a real Hilbert space `V`, coercive with constant `κ > 0`, let `ℓ` be
a load with `‖ℓ‖ ≤ β`, and let `N` satisfy `|N u w| ≤ a ‖u‖² ‖w‖` with `a > 0` and, for a compact
injective map `e` into a normed space, the continuity estimate
`|N u w - N v w| ≤ C (‖u‖ + ‖v‖) ‖e (u - v)‖ ‖e w‖`. If `κ² - 4 β a ≥ 0`, the equation
`B u + N u = ℓ` has a solution with `‖u‖ ≤ (κ - √(κ² - 4 β a)) / (2 a)`.

The iteration `u ↦ B⁻¹(ℓ - N u)` keeps the ball of that radius, because the radius is a root of
`a r² - κ r + β`, and it is Lipschitz there for `‖e ·‖`. Schauder's theorem gives the fixed
point, through `exists_solution_of_compact_embedding`. -/
theorem exists_solution_of_quadratic_bound (B : V →L[ℝ] StrongDual ℝ V) (e : V →L[ℝ] W)
    (he : Function.Injective e) (hcompact : IsCompactOperator e)
    (N : V → StrongDual ℝ V) (ell : StrongDual ℝ V) {κ a β C : ℝ} (hκ : 0 < κ) (ha : 0 < a)
    (hcoercive : ∀ u, κ * ‖u‖ * ‖u‖ ≤ B u u) (hell : ‖ell‖ ≤ β)
    (hN : ∀ u w, |N u w| ≤ a * ‖u‖ ^ 2 * ‖w‖)
    (hNcontinuous : ∀ u v w, |N u w - N v w| ≤ C * (‖u‖ + ‖v‖) * ‖e (u - v)‖ * ‖e w‖)
    (hdisc : 0 ≤ κ ^ 2 - 4 * β * a) :
    ∃ u, ‖u‖ ≤ quadraticRadius κ a β ∧ ∀ v, B u v + N u v = ell v := by
  set r := quadraticRadius κ a β with hrdef
  have hr : 0 ≤ r := quadraticRadius_nonneg hκ.le ha ((norm_nonneg _).trans hell)
  -- The bound of `N u` on the ball.
  have hNball (u : V) (hu : ‖u‖ ≤ ((1 : NNReal) : ℝ) * r) : ‖N u‖ ≤ a * r ^ 2 := by
    rw [NNReal.coe_one, one_mul] at hu
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
    rw [Real.norm_eq_abs]
    exact (hN u w).trans (by gcongr)
  -- The continuity estimate on the ball: `N` is Lipschitz there for the weaker norm.
  have hC : 0 ≤ max C 0 * (2 * r) * ‖e‖ := by positivity
  have hNlip (u : V) (hu : ‖u‖ ≤ ((1 : NNReal) : ℝ) * r) (v : V)
      (hv : ‖v‖ ≤ ((1 : NNReal) : ℝ) * r) :
      ‖N u - N v‖ ≤ ((⟨_, hC⟩ : NNReal) : ℝ) * ‖e (u - v)‖ := by
    rw [NNReal.coe_one, one_mul] at hu hv
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w ↦ ?_
    rw [sub_apply, Real.norm_eq_abs]
    change |N u w - N v w| ≤ max C 0 * (2 * r) * ‖e‖ * ‖e (u - v)‖ * ‖w‖
    calc |N u w - N v w| ≤ C * (‖u‖ + ‖v‖) * ‖e (u - v)‖ * ‖e w‖ := hNcontinuous u v w
      _ ≤ max C 0 * (2 * r) * ‖e (u - v)‖ * (‖e‖ * ‖w‖) := by
        gcongr
        · exact le_max_left C 0
        · linarith
        · exact e.le_opNorm w
      _ = max C 0 * (2 * r) * ‖e‖ * ‖e (u - v)‖ * ‖w‖ := by ring
  -- The budget: the radius is a root of `a r² - κ r + β`.
  have hbudget : ‖ell‖ + a * r ^ 2 ≤ κ * r := by
    have hb := quadraticRadius_budget ha.ne' hdisc
    rw [← hrdef] at hb
    linarith
  obtain ⟨u, hu, heq⟩ := exists_solution_of_compact_embedding B B (ContinuousLinearMap.id ℝ V)
    (ContinuousLinearMap.comp_id B).symm e he hcompact N ell hκ hr hcoercive (g := 1) (γ := 1)
    (by simpa using ContinuousLinearMap.norm_id_le) (fun u ↦ by simp) hNball hNlip hbudget
  exact ⟨u, by simpa using hu, heq⟩

end PDE.Analysis.Variational
