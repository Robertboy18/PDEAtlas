/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import PDE.Analysis.Evolution.Core.WeakEvolution
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import PDE.Analysis.Evolution.Core.EnergyIdentity

/-!
# Coercive energy estimates for weak evolutions

For a trajectory `u` in a Hilbert space `V` satisfying the weak evolution
equation `⟪u', v⟫ + B(u, v) = ℓ(v)` for all `v`, testing with `v = u` and
using coercivity `C ‖u‖² ≤ B(u, u)` together with Young's inequality
`ℓ(u) ≤ ‖ℓ‖ ‖u‖ ≤ ‖ℓ‖² / (2C) + (C/2) ‖u‖²` gives the differential inequality

`d/dt (½ ‖u‖²) + (C/2) ‖u‖² ≤ ‖ℓ‖² / (2C)`.

Integrating over `[a, t]` with `‖ℓ(t)‖ ≤ M` yields the a priori bound
`½ ‖u(t)‖² ≤ ½ ‖u(a)‖² + M² (t - a) / (2C)`. These are the Hilbert-space
energy estimates for the Galerkin approximations in Evans's existence proof
for second-order parabolic equations. Here the trajectory is differentiable in
`V` and the form is coercive.

## Main results

* `mul_le_sq_div_add_mul_sq_half`: Young's inequality
  `ab ≤ a² / (2C) + (C/2) b²`.
* `weakEvolution_coercive_energy_inequality`: the pointwise differential
  inequality.
* `weakEvolution_energy_bound`: the integrated bound on `[a, b]`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 2 (energy estimates for the Galerkin
  approximations). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Set

namespace PDE.Analysis.Evolution

open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Young's inequality `ab ≤ a² / (2C) + (C/2) b²` for `C > 0`. -/
theorem mul_le_sq_div_add_mul_sq_half {C : ℝ} (hC : 0 < C) (a b : ℝ) :
    a * b ≤ a ^ 2 / (2 * C) + (C / 2) * b ^ 2 := by
  have h := two_mul_le_add_mul_sq (a := b) (b := a) hC
  calc
    a * b ≤ (C * b ^ 2 + C⁻¹ * a ^ 2) / 2 := by nlinarith
    _ = a ^ 2 / (2 * C) + (C / 2) * b ^ 2 := by
      field_simp
      ring

/-- Pointwise coercive energy inequality. If `C ‖u‖² ≤ B(u, u)` with `C > 0` and
`⟪u', v⟫ + B(u, v) = ℓ(v)` for all `v`, then
`⟪u', u⟫ + (C/2) ‖u‖² ≤ ‖ℓ‖² / (2C)`. -/
theorem weakEvolution_coercive_energy_inequality
    (B : V →L[ℝ] StrongDual ℝ V) (ell : StrongDual ℝ V)
    {C : ℝ} (hC : 0 < C)
    {u du : V}
    (hcoercive : C * ‖u‖ ^ 2 ≤ B u u)
    (heq : SatisfiesWeakEvolutionAt B ell u du) :
    inner ℝ du u + (C / 2) * ‖u‖ ^ 2 ≤ ‖ell‖ ^ 2 / (2 * C) := by
  have heqSelf := heq u
  have hellNorm : ell u ≤ ‖ell‖ * ‖u‖ := by
    exact (le_abs_self (ell u)).trans (ell.le_opNorm u)
  have hyoung := mul_le_sq_div_add_mul_sq_half hC ‖ell‖ ‖u‖
  nlinarith

/-- Integrated a priori energy bound on `[a, b]` (Evans §7.1.2). If `u` is
differentiable within `[a, b]`, solves the weak equation with
`C ‖u(t)‖² ≤ B(t)(u(t), u(t))` for some `C > 0`, and `‖ℓ(t)‖ ≤ M`, then
`½ ‖u(t)‖² ≤ ½ ‖u(a)‖² + M² (t - a) / (2C)`. -/
theorem weakEvolution_energy_bound
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) {a b : ℝ} (hab : a ≤ b)
    (ell : ℝ → StrongDual ℝ V) (u du : ℝ → V)
    {C M : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hu : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt u (du t) (Set.Icc a b) t)
    (hcoercive : ∀ t ∈ Set.Icc a b, C * ‖u t‖ ^ 2 ≤ B t (u t) (u t))
    (hell : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ M)
    (heq : ∀ t ∈ Set.Icc a b,
      SatisfiesWeakEvolutionAt (B t) (ell t) (u t) (du t)) :
    ∀ t ∈ Set.Icc a b,
      (1 / 2 : ℝ) * ‖u t‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖u a‖ ^ 2 + (M ^ 2 / (2 * C)) * (t - a) := by
  let E : ℝ → ℝ := fun t ↦ (1 / 2 : ℝ) * ‖u t‖ ^ 2
  have hEderivWithin (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivWithinAt E (inner ℝ (du t) (u t)) (Set.Icc a b) t :=
    hasDerivWithinAt_half_norm_sq (hu t ht)
  have hEcont : ContinuousOn E (Set.Icc a b) := by
    intro t ht
    exact (hEderivWithin t ht).continuousWithinAt
  have hEdiff : DifferentiableOn ℝ E (interior (Set.Icc a b)) := by
    intro t ht
    exact ((hEderivWithin t (interior_subset ht)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)).differentiableAt.differentiableWithinAt
  have hEderivLe (t : ℝ) (ht : t ∈ interior (Set.Icc a b)) :
      deriv E t ≤ M ^ 2 / (2 * C) := by
    have htIcc := interior_subset ht
    have hpoint := weakEvolution_coercive_energy_inequality (B t) (ell t) hC
      (hcoercive t htIcc) (heq t htIcc)
    have hsquare : ‖ell t‖ ^ 2 ≤ M ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg _) hM).2 (hell t htIcc)
    rw [((hEderivWithin t htIcc).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)).deriv]
    have hdiv : ‖ell t‖ ^ 2 / (2 * C) ≤ M ^ 2 / (2 * C) := by
      exact div_le_div_of_nonneg_right hsquare (by positivity)
    nlinarith [mul_nonneg (le_of_lt hC) (sq_nonneg ‖u t‖)]
  intro t ht
  have hEa : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hmv := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
    hEcont hEdiff hEderivLe a hEa t ht ht.1
  dsimp [E] at hmv ⊢
  linarith

end PDE.Analysis.Evolution
