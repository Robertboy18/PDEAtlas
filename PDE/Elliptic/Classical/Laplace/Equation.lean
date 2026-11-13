/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.LinearPDE
public import PDE.FDeriv.Operators
import PDE.FDeriv.Calculus

/-!
# The Euclidean Laplace equation

We write LeanPDE's iterated-coordinate Laplacian as a second-order `LinearPDE`. The
jet-trace identities connect the concrete totalized expression to the finite-order locality
that `LinearPDE` requires. Its classical interpretation requires `C²` regularity; under that
hypothesis it agrees with Mathlib's canonical Laplacian.

The sign-free Laplace equation `Δu = 0` and the sign convention `-Δu = f` for Poisson's equation
follow Evans, §2.2, (1)-(2).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2, Laplace's equation (1) and Poisson's equation (2),
  p. 20.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv laplacian)

noncomputable section

namespace PDE

/-- Evaluation of the trace of the second Fréchet derivative on Euclidean coordinate vectors. -/
def euclideanLaplacianJet (n : ℕ)
    (J : FormalMultilinearSeries ℝ (ℝ^n) ℝ) : ℝ :=
  ∑ i : Fin n, J 2 (fun _ : Fin 2 ↦ EuclideanSpace.single i (1 : ℝ))

/-- The second Fréchet derivative in one coordinate agrees with the iterated coordinate partial
for a `C²` function. -/
theorem ftaylorSeries_second_coordinate_eq
    {n : ℕ} (u : ℝ^n → ℝ)
    (x : ℝ^n) (i : Fin n) (hu : ContDiffAt ℝ 2 u x) :
    (ftaylorSeries ℝ u x) 2
        (fun _ : Fin 2 ↦ EuclideanSpace.single i (1 : ℝ)) =
      (∂[i] (fun y ↦ (∂[i] u) y)) x := by
  change iteratedFDeriv ℝ 2 u x
      (fun _ : Fin 2 ↦ EuclideanSpace.single i (1 : ℝ)) = _
  simpa [Function.iterate_succ_apply] using
    (iterate_partialDeriv_eq_iteratedFDeriv_single i 2 hu).symm

/-- The jet trace is the coordinate Laplacian on `C²` functions. -/
theorem euclideanLaplacianJet_ftaylorSeries_eq
    {n : ℕ} (u : ℝ^n → ℝ)
    (x : ℝ^n) (hu : ContDiffAt ℝ 2 u x) :
    euclideanLaplacianJet n (ftaylorSeries ℝ u x) = laplacian (n := n) u x := by
  classical
  unfold euclideanLaplacianJet laplacian
  exact Finset.sum_congr rfl fun i _ ↦ ftaylorSeries_second_coordinate_eq u x i hu

/-- The Laplace equation `Δu = 0` in dimension `n`.

For `n = 0`, the coordinate sum is empty and the operator is identically zero. Analytic PDE
applications should assume `0 < n`. -/
def laplaceEquation (n : ℕ) : LinearPDE ℝ (ℝ^n) ℝ 2 where
  operator := fun u x ↦ laplacian (n := n) u x
  map_zero := by simp [laplacian, partialDeriv]
  map_add := by
    intro u v hu hv x
    change laplacian (n := n) (fun y ↦ u y + v y) x =
      laplacian (n := n) u x + laplacian (n := n) v x
    exact laplacian_add (n := n) u v x hu.contDiffAt hv.contDiffAt
  map_smul := by
    intro c u hu x
    change laplacian (n := n) (fun y ↦ c * u y) x =
      c * laplacian (n := n) u x
    exact laplacian_const_smul (n := n) c u x
  congr_jet := by
    intro u v x hu hv hjet
    rw [← euclideanLaplacianJet_ftaylorSeries_eq u x hu,
      ← euclideanLaplacianJet_ftaylorSeries_eq v x hv]
    unfold euclideanLaplacianJet ftaylorSeries
    rw [hjet 2 le_rfl]
  rhs := fun _ ↦ (0 : ℝ)
  domain := Set.univ

/-- The Laplace model evaluates to its totalized coordinate-residual expression.

The identity holds for every `u`; reading it as the classical Laplacian requires `u ∈ C²`. -/
theorem laplaceEquation_residual (n : ℕ) (u : ℝ^n → ℝ)
    (x : ℝ^n) :
    (laplaceEquation n).residual u x = laplacian (n := n) u x := by
  simp [LinearPDE.residual, laplaceEquation]

end PDE
