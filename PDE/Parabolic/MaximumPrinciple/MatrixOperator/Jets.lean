/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixOperator.Jets
public import PDE.Parabolic.MaximumPrinciple.MatrixOperator

/-!
# Parabolic matrix residuals from spatial and temporal derivatives

The operator is determined by the value, first and second spatial
derivatives, and first time derivative. Its perturbation bound is independent
of mixed derivatives and second time derivatives.
-/

@[expose] public noncomputable section

namespace ParabolicMaximum

open Filter
open scoped Topology

variable {n : ℕ}

/-- The parabolic operator evaluated through given spatial and time derivatives. -/
theorem matrixParabolicOperator_eq_of_hasDerivAt
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    {u : ℝ^n → ℝ → ℝ} {Du : ℝ^n → ℝ^n →L[ℝ] ℝ}
    {H : ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ} {d : ℝ} {x : ℝ^n} {t : ℝ}
    (hu : ∀ᶠ y in 𝓝 x, HasFDerivAt (fun z ↦ u z t) (Du y) y)
    (hDu : HasFDerivAt Du H x) (ht : HasDerivAt (u x) d t) :
    matrixParabolicOperator a b c u x t =
      d + (-(∑ i : Fin n, ∑ j : Fin n,
        a x t i j * H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
        Du x (b x t) + c x t * u x t) := by
  rw [matrixParabolicOperator, ht.deriv,
    EllipticMaximum.matrixOperator_eq_of_hasFDerivAt _ _ _ hu hDu]

/-- Perturbing the supplied derivatives controls the difference of
parabolic residuals, with no joint second differentiability assumption. -/
theorem abs_matrixParabolicOperator_sub_le_of_hasDerivAt
    (a : ℝ^n → ℝ → Matrix (Fin n) (Fin n) ℝ)
    (b : ℝ^n → ℝ → ℝ^n) (c : ℝ^n → ℝ → ℝ)
    {u v : ℝ^n → ℝ → ℝ} {Du Dv : ℝ^n → ℝ^n →L[ℝ] ℝ}
    {Hu Hv : ℝ^n →L[ℝ] ℝ^n →L[ℝ] ℝ} {du dv : ℝ} {x : ℝ^n} {t : ℝ}
    (hu : ∀ᶠ y in 𝓝 x, HasFDerivAt (fun z ↦ u z t) (Du y) y)
    (hDu : HasFDerivAt Du Hu x) (hut : HasDerivAt (u x) du t)
    (hv : ∀ᶠ y in 𝓝 x, HasFDerivAt (fun z ↦ v z t) (Dv y) y)
    (hDv : HasFDerivAt Dv Hv x) (hvt : HasDerivAt (v x) dv t) :
    |matrixParabolicOperator a b c u x t - matrixParabolicOperator a b c v x t| ≤
      |du - dv| + ((∑ i : Fin n, ∑ j : Fin n, |a x t i j|) * ‖Hu - Hv‖ +
        ‖b x t‖ * ‖Du x - Dv x‖ + |c x t| * |u x t - v x t|) := by
  rw [matrixParabolicOperator, matrixParabolicOperator, hut.deriv, hvt.deriv,
    add_sub_add_comm]
  exact (abs_add_le _ _).trans (add_le_add le_rfl
    (EllipticMaximum.abs_matrixOperator_sub_le_of_hasFDerivAt
      (fun y ↦ a y t) (fun y ↦ b y t) (fun y ↦ c y t) hu hDu hv hDv))

end ParabolicMaximum
