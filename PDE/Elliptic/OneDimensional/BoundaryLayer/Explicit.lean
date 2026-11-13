/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import CAS.ExactTactic

/-!
# An explicit convection-diffusion boundary layer

For `ε > 0` and `b > 0`, the equation `εu″ + bu′ = f` on `[0, L]` takes two boundary conditions,
while the reduced equation `bu′ = f` takes only one. We keep the right boundary condition in the
outer solution `outer` (`outer_equation`) and correct the left boundary value with the decaying
exponential `layer` in the stretched coordinate `x / ε`. For constant forcing and arbitrary real
endpoint values, the normalized layer `profile` gives the smooth solution `solution` of the
two-point problem (`solution_equation`, `solution_zero`, `solution_right`, `solution_contDiff`). The
asymptotic estimates are in `BoundaryLayer.Asymptotics`.

In the terms of Evans's §4.5.1, `εu″ + bu′ = f` is a singular perturbation of `bu′ = f`: a small
multiple `ε` of a higher-order term is added. Evans's Example 1 in that subsection treats formally
the transport of dye with small diffusion in `ℝ²`, his (1)-(2), with rescaled variables (9) across
the plume about the transport curve. The subsection contains no boundary-layer example.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.5.1 (Singular perturbations), Example 1 (Transport and
  small diffusion), (1)-(2) and (9), pp. 211-214.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Elliptic.BoundaryLayer

/-- The solution of the reduced equation satisfying the right boundary condition. -/
def outer (b L B f x : ℝ) : ℝ :=
  B + f / b * (x - L)

/-- The left boundary value missing from the reduced solution. -/
def mismatch (b L A B f : ℝ) : ℝ :=
  A - outer b L B f 0

/-- The exponentially decaying correction in the stretched coordinate `x / ε`. -/
def layer (ε b x : ℝ) : ℝ :=
  Real.exp (-b * x / ε)

/-- Normalization enforces both endpoint values exactly. -/
def profile (ε b L x : ℝ) : ℝ :=
  (layer ε b x - layer ε b L) / (1 - layer ε b L)

/-- The exact solution of the constant-coefficient two-point problem. -/
def solution (ε b L A B f x : ℝ) : ℝ :=
  outer b L B f x + mismatch b L A B f * profile ε b L x

/-- The matched composite approximation retains only the left exponential layer. -/
def composite (ε b L A B f x : ℝ) : ℝ :=
  outer b L B f x + mismatch b L A B f * layer ε b x

/-- The normalization denominator is strictly positive on a nondegenerate interval. -/
theorem denominator_pos {ε b L : ℝ} (hε : 0 < ε) (hb : 0 < b) (hL : 0 < L) :
    0 < 1 - layer ε b L := by
  apply sub_pos.mpr
  exact Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
    (neg_neg_of_pos hb) hL) hε)

/-- The left boundary condition holds exactly. -/
theorem solution_zero {ε b L : ℝ} (hε : 0 < ε) (hb : 0 < b) (hL : 0 < L)
    (A B f : ℝ) : solution ε b L A B f 0 = A := by
  have hd := (denominator_pos hε hb hL).ne'
  have hz : layer ε b 0 = 1 := by simp [layer]
  simp only [solution, profile, hz, div_self hd, mul_one, mismatch, add_sub_cancel]

/-- The right boundary condition holds even before imposing positivity assumptions. -/
theorem solution_right (ε b L A B f : ℝ) : solution ε b L A B f L = B := by
  simp [solution, profile, outer]

/-- The explicit solution is smooth for every fixed choice of parameters. -/
theorem solution_contDiff (ε b L A B f : ℝ) :
    ContDiff ℝ ⊤ (solution ε b L A B f) := by
  unfold solution outer profile layer
  fun_prop

/-- The reduced equation is satisfied with the derivative. -/
theorem outer_equation {b : ℝ} (hb : b ≠ 0) (L B f x : ℝ) :
    b * deriv (outer b L B f) x = f := by
  have hd : HasDerivAt (outer b L B f) (f / b) x := by
    unfold outer
    cas
  rw [hd.deriv]
  cas using hb

/-- The first derivative of the exact solution. -/
theorem solution_hasDerivAt {ε b L : ℝ} (hε : 0 < ε) (hb : 0 < b) (hL : 0 < L)
    (A B f x : ℝ) :
    HasDerivAt (solution ε b L A B f)
      (f / b - mismatch b L A B f * (b / ε) *
        layer ε b x / (1 - layer ε b L)) x := by
  have hd := (denominator_pos hε hb hL).ne'
  have he := hε.ne'
  unfold solution outer profile layer
  cas using And.intro hd he

/-- The second derivative of the exact solution. -/
theorem solution_second_deriv {ε b L : ℝ} (hε : 0 < ε) (hb : 0 < b) (hL : 0 < L)
    (A B f x : ℝ) :
    deriv (deriv (solution ε b L A B f)) x =
      mismatch b L A B f * (b / ε) ^ 2 * layer ε b x / (1 - layer ε b L) := by
  have hfirst : deriv (solution ε b L A B f) =
      fun y ↦ f / b - mismatch b L A B f * (b / ε) *
        layer ε b y / (1 - layer ε b L) :=
    funext fun y ↦ (solution_hasDerivAt hε hb hL A B f y).deriv
  rw [hfirst]
  have hd := (denominator_pos hε hb hL).ne'
  have he := hε.ne'
  unfold layer
  cas using And.intro hd he

/-- Both derivatives are those of the constructed function, not supplied solution data. -/
theorem solution_equation {ε b L : ℝ} (hε : 0 < ε) (hb : 0 < b) (hL : 0 < L)
    (A B f x : ℝ) :
    ε * deriv (deriv (solution ε b L A B f)) x +
      b * deriv (solution ε b L A B f) x = f := by
  rw [solution_second_deriv hε hb hL, (solution_hasDerivAt hε hb hL A B f x).deriv]
  have hd := (denominator_pos hε hb hL).ne'
  have he := hε.ne'
  have hbn := hb.ne'
  cas using [hd, he, hbn]

end PDE.Elliptic.BoundaryLayer
