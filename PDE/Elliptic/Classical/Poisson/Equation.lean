/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.LinearPDE
public import PDE.FDeriv.Operators
import PDE.Elliptic.Classical.Laplace.Equation
import PDE.FDeriv.Calculus

/-!
# Poisson equation

We define `poissonEquation`, the whole-space `LinearPDE` for Poisson's equation `-Δu = f`,
with the sign convention of Evans's equation (2) in §2.2. The Laplacian `Δ` is LeanPDE's totalized
iterated-coordinate expression, which agrees with Mathlib's canonical Laplacian on `C²` fields.
We identify the formal residual with the pointwise expression and record the corresponding
superposition, scaling, subtraction, and linear-combination rules.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2, Poisson's equation (2), p. 20.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv laplacian LinearPDE euclideanLaplacianJet)

namespace PoissonEquation


/-- Poisson's equation `-Δu = f` on all of `ℝ^n`, as a second-order `LinearPDE` with operator
`u ↦ -Δu` and right-hand side `f`. -/
noncomputable def poissonEquation (n : ℕ)
    (f : ℝ^n → ℝ) :
    LinearPDE ℝ (ℝ^n) ℝ 2 where
  operator := fun u x ↦ -laplacian u x
  map_zero := by simp [laplacian, partialDeriv]
  map_add := by
    intro u v hu hv x
    change -laplacian (n := n) (fun y ↦ u y + v y) x =
      -laplacian (n := n) u x + -laplacian (n := n) v x
    rw [PDE.laplacian_add u v x hu.contDiffAt hv.contDiffAt]
    ring
  map_smul := by
    intro c u hu x
    change -laplacian (n := n) (fun y ↦ c * u y) x =
      c * -laplacian (n := n) u x
    rw [PDE.laplacian_const_smul c u x]
    ring
  congr_jet := by
    intro u v x hu hv hjet
    rw [← PDE.euclideanLaplacianJet_ftaylorSeries_eq u x hu,
      ← PDE.euclideanLaplacianJet_ftaylorSeries_eq v x hv]
    unfold euclideanLaplacianJet ftaylorSeries
    rw [hjet 2 le_rfl]
  rhs := f
  domain := Set.univ

/-- The elliptic Poisson `LinearPDE` evaluates to the totalized expression `-Δu - f`.

This identity alone does not supply the `C²` regularity required of a classical solution. -/
theorem poissonEquation_residual (n : ℕ)
    (f u : ℝ^n → ℝ) (x : ℝ^n) :
    (poissonEquation n f).residual u x = -laplacian u x - f x :=
  rfl

/-- Vanishing of the Poisson residual is exactly the textbook sign convention `-Δu = f`. -/
theorem poissonEquation_residual_eq_zero_iff (n : ℕ)
    (f u : ℝ^n → ℝ) (x : ℝ^n) :
    (poissonEquation n f).residual u x = 0 ↔ -laplacian u x = f x := by
  simp only [poissonEquation_residual, sub_eq_zero]

/-- Vanishing of the Poisson residual on its domain is exactly the pointwise equation
`-Δu = f` everywhere.

This is a residual characterization only. It does not by itself assert the `C²` regularity
required of a classical solution. -/
theorem poissonEquation_residual_zero_iff (n : ℕ)
    (f u : ℝ^n → ℝ) :
    (∀ x ∈ (poissonEquation n f).domain,
      (poissonEquation n f).residual u x = 0) ↔
      ∀ x : ℝ^n, -laplacian u x = f x := by
  constructor
  · intro h x
    exact (poissonEquation_residual_eq_zero_iff n f u x).1
      (h x (by simp [poissonEquation]))
  · intro h x hx
    exact (poissonEquation_residual_eq_zero_iff n f u x).2 (h x)

/--
Superposition for the pointwise Poisson equation.

If `-Δu = f` and `-Δv = g`, then `-Δ(u+v)=f+g`. The `C²` assumptions are exactly the
regularity needed to split the Laplacian.
-/
theorem poissonEquation_solution_add (n : ℕ)
    {f g u v : ℝ^n → ℝ}
    (hu : ∀ x : ℝ^n, -laplacian u x = f x)
    (hv : ∀ x : ℝ^n, -laplacian v x = g x)
    (hcu : ContDiff ℝ 2 u) (hcv : ContDiff ℝ 2 v) :
    ∀ x : ℝ^n,
      -laplacian (fun y ↦ u y + v y) x = f x + g x := by
  intro x
  have hcu_x : ContDiffAt ℝ 2 u x := hcu.contDiffAt
  have hcv_x : ContDiffAt ℝ 2 v x := hcv.contDiffAt
  rw [PDE.laplacian_add u v x hcu_x hcv_x]
  calc
    -(laplacian u x + laplacian v x)
        = -laplacian u x + -laplacian v x := by ring
    _ = f x + g x := by rw [hu x, hv x]

/--
Scalar multiplication for the pointwise Poisson equation.

If `-Δu = f`, then `-Δ(cu)=c f`.
-/
theorem poissonEquation_solution_const_mul (n : ℕ)
    (c : ℝ)
    {f u : ℝ^n → ℝ}
    (hu : ∀ x : ℝ^n, -laplacian u x = f x) :
    ∀ x : ℝ^n,
      -laplacian (fun y ↦ c * u y) x = c * f x := by
  intro x
  rw [PDE.laplacian_const_smul c u x]
  calc
    -(c * laplacian u x) = c * (-laplacian u x) := by ring
    _ = c * f x := by rw [hu x]

/--
Subtraction for the pointwise Poisson equation.

If `-Δu = f` and `-Δv = g`, then `-Δ(u-v)=f-g`.
-/
theorem poissonEquation_solution_sub (n : ℕ)
    {f g u v : ℝ^n → ℝ}
    (hu : ∀ x : ℝ^n, -laplacian u x = f x)
    (hv : ∀ x : ℝ^n, -laplacian v x = g x)
    (hcu : ContDiff ℝ 2 u) (hcv : ContDiff ℝ 2 v) :
    ∀ x : ℝ^n,
      -laplacian (fun y ↦ u y - v y) x = f x - g x := by
  intro x
  have hcu_x : ContDiffAt ℝ 2 u x := hcu.contDiffAt
  have hcv_x : ContDiffAt ℝ 2 v x := hcv.contDiffAt
  have hneg_x : ContDiffAt ℝ 2 (-v) x := hcv_x.neg
  have hadd := PDE.laplacian_add u (-v) x hcu_x hneg_x
  change -laplacian (fun y ↦ u y + (-v) y) x = f x - g x
  rw [hadd, PDE.laplacian_neg]
  calc
    -(laplacian u x + -laplacian v x)
        = -laplacian u x - -laplacian v x := by ring
    _ = f x - g x := by rw [hu x, hv x]

/--
Linear combinations for the pointwise Poisson equation.

If `-Δu = f` and `-Δv = g`, then `-Δ(au+bv)=af+bg`.
-/
theorem poissonEquation_solution_linear_combination (n : ℕ)
    (a b : ℝ)
    {f g u v : ℝ^n → ℝ}
    (hu : ∀ x : ℝ^n, -laplacian u x = f x)
    (hv : ∀ x : ℝ^n, -laplacian v x = g x)
    (hcu : ContDiff ℝ 2 u) (hcv : ContDiff ℝ 2 v) :
    ∀ x : ℝ^n,
      -laplacian (fun y ↦ a * u y + b * v y) x = a * f x + b * g x :=
  poissonEquation_solution_add n
    (poissonEquation_solution_const_mul n a hu)
    (poissonEquation_solution_const_mul n b hv)
    (contDiff_const.mul hcu) (contDiff_const.mul hcv)

end PoissonEquation
