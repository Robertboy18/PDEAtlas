/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Variational.Spaces.WholeSpaceHilbert
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.H10L2
public import PDE.Hyperbolic.Variational.Semigroup.Generation
public import PDE.Spaces.Sobolev.GraphSpace.Operators.BaseInjectivity

/-!
# Whole-space energy geometry for the semilinear wave equation

The base coordinate gives the dense inclusion `H¹(ℝ^n) → L²(ℝ^n)`. The H¹ inner
product represents `1 - Δ`; subtracting its L² part gives the weak Laplacian form.
The added mass makes the linear wave generator coercive without a Poincaré inequality,
a bounded domain, or a discrete spectrum.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Sobolev InnerProductSpace SobolevSpace.WholeSpaceHilbert

namespace PDE.Hyperbolic.NonlinearWave.Cauchy

open SobolevSpace SobolevSpace.GraphSpace
open PDE.Analysis.Evolution PDE.Analysis.Variational

variable {n : ℕ}

/-- The whole-space energy inclusion, with no boundary condition on its domain. -/
def energyTriple (n : ℕ) :
    GelfandTriple (V := H¹(ℝ^n)) (H := DerivLp n 2 univ) where
  inclusion := wkpBaseCoordinateCLM
  injective := wkpBaseCoordinateCLM_injective isOpen_univ
  denseRange := by
    apply (baseCoordCLM_denseRange (n := n) isOpen_univ).mono
    rintro y ⟨u, rfl⟩
    exact ⟨u.val, rfl⟩

/-- The form of `1 - Δ`, namely the full H¹ inner product. -/
def massForm (n : ℕ) : H¹(ℝ^n) →L[ℝ] StrongDual ℝ H¹(ℝ^n) :=
  innerSL ℝ

/-- The mass form is coercive in the natural H¹ norm with constant one. -/
theorem massForm_coercive (n : ℕ) : IsCoercive (massForm n) := by
  refine ⟨1, zero_lt_one, fun u ↦ ?_⟩
  change 1 * ‖u‖ * ‖u‖ ≤ inner ℝ u u
  rw [real_inner_self_eq_norm_sq, one_mul, pow_two]

/-- The real H¹ pairing is symmetric. -/
theorem massForm_symmetric (u v : H¹(ℝ^n)) : massForm n u v = massForm n v u := by
  change inner ℝ u v = inner ℝ v u
  exact real_inner_comm v u

/-- The weak form of `-Δ`, acting on all H¹ test functions. -/
def gradientForm (n : ℕ) : H¹(ℝ^n) →L[ℝ] StrongDual ℝ H¹(ℝ^n) :=
  massForm n - (energyTriple n).energyToDual

/-- The weak Laplacian pairs exactly the first weak derivatives in spatial L². -/
theorem gradientForm_apply (u v : H¹(ℝ^n)) :
    gradientForm n u v =
      ∑ i : Fin n, ⟪u.val (singleDerivIndex n i), v.val (singleDerivIndex n i)⟫_ℝ := by
  change ⟪u.val, v.val⟫_ℝ - ⟪u.val (baseIndex n 1), v.val (baseIndex n 1)⟫_ℝ = _
  rw [ambient_inner_eq_base_add_sum_deriv]
  exact add_sub_cancel_left _ _

end PDE.Hyperbolic.NonlinearWave.Cauchy
