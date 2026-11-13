/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.ContinuousBounds
public import PDE.Analysis.LinearAlgebra.Ellipticity
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Continuous coefficient assumptions

Almost-everywhere ellipticity and essential coefficient bounds extend to
every point of the open domain. The coordinate quadratic form gives the
positive-semidefinite matrix needed by the contact estimates.
-/

@[expose] public section

noncomputable section

namespace EllipticHarnack

open PDE.Analysis MeasureTheory Set
open scoped RealInnerProductSpace

variable {n : ℕ}

/-- Continuous coefficients extend the almost-everywhere ellipticity
condition to the pointwise Euclidean quadratic-form inequality. -/
theorem elliptic_on_open_of_ae
    {U : Set (ℝ^n)} (hU : IsOpen U)
    {a : ℝ^n → Matrix (Fin n) (Fin n) ℝ} (ha : ContinuousOn a U) {α : ℝ}
    (hell : ∀ᵐ x ∂volume.restrict U, ∀ v : ℝ^n,
      α * ‖v‖ ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, a x i j * v i * v j) :
    ∀ x ∈ U, ∀ v : ℝ^n, α * ‖v‖ ^ 2 ≤ ⟪v, (a x).toEuclideanLin v⟫ := by
  have hentry (i j : Fin n) : ContinuousOn (fun x ↦ a x i j) U :=
    continuousOn_pi.mp (continuousOn_pi.mp ha i) j
  intro x hx v
  rw [inner_toEuclideanLin_self]
  exact leOn_open_of_ae_le hU continuousOn_const
    (continuousOn_finsetSum _ fun i _ ↦ continuousOn_finsetSum _ fun j _ ↦
      ((hentry i j).mul continuousOn_const).mul continuousOn_const)
    (hell.mono fun _ h ↦ h v) x hx

end EllipticHarnack
