/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic

public import PDE.Analysis.Evolution.Gelfand.Equation
public import PDE.Analysis.Evolution.Gelfand.PivotDerivative
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import PDE.Analysis.Evolution.Core.EnergyEstimate
import PDE.Analysis.Evolution.Core.EnergyIdentity

/-!
# Energy estimates for smooth Gelfand evolutions

Energy estimates for a differentiable weak evolution in a Gelfand triple
`V ↪ H ↪ V*`. The equation `⟨u', v⟩ + B(u, v) = ℓ(v)` is posed with `u' ∈ V*`. The
trajectory is differentiable after inclusion into the pivot space `H`, and its
`V*`-derivative is represented by the `H`-derivative through the pivot pairing
(`RepresentsPivotDerivative`).

Testing with `v = u(t)` gives the pivot-energy identity `d/dt (½ ‖u‖²_H) = ℓ(u) - B(u, u)`.
Coercivity `C ‖u‖²_V ≤ B(u, u)` and Young's inequality give
`d/dt (½ ‖u‖²_H) + (C/2) ‖u‖²_V ≤ ‖ℓ‖²_{V*} / (2C)`, and integrating with `‖ℓ(t)‖ ≤ M`
gives the linear growth bound `½ ‖u(t)‖²_H ≤ ½ ‖u(a)‖²_H + M² (t - a) / (2C)` on `[a, b]`.
The differentiated energy is the pivot norm while coercivity controls the energy norm, as in
the argument for Galerkin approximants in Evans.

## Main results

* `gelfandWeakEvolution_energy_identity`: the pivot-energy identity.
* `gelfandWeakEvolution_coercive_energy_inequality`: the pointwise coercive
  inequality.
* `gelfandWeakEvolution_energy_bound`: the integrated bound on `[a, b]`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, proof of Theorem 2 (energy estimates for the
  Galerkin approximations), and §5.9.2, Theorem 3 (`d/dt ‖u‖² = 2 ⟨u', u⟩` for
  `u ∈ L²(0, T; H¹₀)` with `u' ∈ L²(0, T; H⁻¹)`). <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section


open MeasureTheory Set

namespace PDE.Analysis.Evolution

open Function Filter
open scoped Topology InnerProductSpace

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Pivot-energy identity for a Gelfand weak evolution whose trajectory is
differentiable after inclusion into `H`: testing the equation with `u(t)`
gives `d/dt (½ ‖u‖²_H) = ℓ(u) - B(u, u)`.  This is the differentiable-in-time
core of the Lions–Magenes identity `d/dt ‖u‖²_H = 2 ⟨u', u⟩` for
`u ∈ L²(V)`, `u' ∈ L²(V*)`, which Evans proves for `V = H¹₀` (§5.9.2, Theorem 3). -/
theorem gelfandWeakEvolution_energy_identity
    (T : GelfandTriple (V := V) (H := H))
    (B : V →L[ℝ] StrongDual ℝ V) (ell : StrongDual ℝ V)
    {u : ℝ → V} {du : StrongDual ℝ V} {duH : H} {t : ℝ}
    (hu : HasDerivAt (fun s ↦ T.inclusion (u s)) duH t)
    (hrep : RepresentsPivotDerivative T du duH)
    (heq : SatisfiesGelfandWeakEvolutionAt B ell (u t) du) :
    HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ‖T.inclusion (u s)‖ ^ 2)
      (ell (u t) - B (u t) (u t)) t := by
  have henergy := hasDerivAt_half_norm_sq hu
  have htest := heq (u t)
  have hpivot := hrep (u t)
  convert henergy using 1
  linarith

/-- Coercive pointwise energy inequality: if `C ‖u‖²_V ≤ B(u, u)` with `C > 0`, then
`⟪u'_H, u⟫_H + (C/2) ‖u‖²_V ≤ ‖ℓ‖²_{V*} / (2C)`. -/
theorem gelfandWeakEvolution_coercive_energy_inequality
    (T : GelfandTriple (V := V) (H := H))
    (B : V →L[ℝ] StrongDual ℝ V) (ell : StrongDual ℝ V)
    {C : ℝ} (hC : 0 < C) {u : V} {du : StrongDual ℝ V} {duH : H}
    (hrep : RepresentsPivotDerivative T du duH)
    (hcoercive : C * ‖u‖ ^ 2 ≤ B u u)
    (heq : SatisfiesGelfandWeakEvolutionAt B ell u du) :
    inner ℝ duH (T.inclusion u) + (C / 2) * ‖u‖ ^ 2 ≤
      ‖ell‖ ^ 2 / (2 * C) := by
  have heqSelf := heq u
  have hpivot := hrep u
  have hellNorm : ell u ≤ ‖ell‖ * ‖u‖ :=
    (le_abs_self (ell u)).trans (ell.le_opNorm u)
  have hyoung := mul_le_sq_div_add_mul_sq_half hC ‖ell‖ ‖u‖
  nlinarith

/-- Integrated pivot-energy estimate: if the equation holds on `[a, b]` with
`C ‖u(t)‖²_V ≤ B(t)(u(t), u(t))` and `‖ℓ(t)‖ ≤ M`, then
`½ ‖u(t)‖²_H ≤ ½ ‖u(a)‖²_H + M² (t - a) / (2C)` for every `t ∈ [a, b]`. -/
theorem gelfandWeakEvolution_energy_bound
    (T : GelfandTriple (V := V) (H := H))
    (B : ℝ → V →L[ℝ] StrongDual ℝ V) {a b : ℝ} (hab : a ≤ b)
    (ell du : ℝ → StrongDual ℝ V) (u : ℝ → V) (duH : ℝ → H)
    {C M : ℝ} (hC : 0 < C) (hM : 0 ≤ M)
    (hu : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (fun s ↦ T.inclusion (u s)) (duH t) (Set.Icc a b) t)
    (hrep : ∀ t ∈ Set.Icc a b, RepresentsPivotDerivative T (du t) (duH t))
    (hcoercive : ∀ t ∈ Set.Icc a b, C * ‖u t‖ ^ 2 ≤ B t (u t) (u t))
    (hell : ∀ t ∈ Set.Icc a b, ‖ell t‖ ≤ M)
    (heq : ∀ t ∈ Set.Icc a b,
      SatisfiesGelfandWeakEvolutionAt (B t) (ell t) (u t) (du t)) :
    ∀ t ∈ Set.Icc a b,
      (1 / 2 : ℝ) * ‖T.inclusion (u t)‖ ^ 2 ≤
        (1 / 2 : ℝ) * ‖T.inclusion (u a)‖ ^ 2 +
          (M ^ 2 / (2 * C)) * (t - a) := by
  let E : ℝ → ℝ := fun t ↦ (1 / 2 : ℝ) * ‖T.inclusion (u t)‖ ^ 2
  have hEderivWithin (t : ℝ) (ht : t ∈ Set.Icc a b) :
      HasDerivWithinAt E (inner ℝ (duH t) (T.inclusion (u t)))
        (Set.Icc a b) t :=
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
    have hpoint := gelfandWeakEvolution_coercive_energy_inequality
      T (B t) (ell t) hC (hrep t htIcc) (hcoercive t htIcc) (heq t htIcc)
    have hsquare : ‖ell t‖ ^ 2 ≤ M ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hM).2 (hell t htIcc)
    rw [((hEderivWithin t htIcc).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)).deriv]
    have hdiv : ‖ell t‖ ^ 2 / (2 * C) ≤ M ^ 2 / (2 * C) :=
      div_le_div_of_nonneg_right hsquare (by positivity)
    nlinarith [mul_nonneg (le_of_lt hC) (sq_nonneg ‖u t‖)]
  intro t ht
  have hEa : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hmv := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
    hEcont hEdiff hEderivLe a hEa t ht ht.1
  simpa [E, add_comm] using hmv

end PDE.Analysis.Evolution
