/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Form.Generation

/-!
# Energy-space representatives of form semigroup orbits

For initial data in the operator domain, the orbit lifts continuously into the energy
space. The lift is constructed by applying the coercive variational inverse at one to
`S(t)(x - Ax)`. Uniqueness of the variational solution identifies it with the energy
representative of `S(t)x`. Its pivot derivative satisfies the form evolution equation.
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis.Evolution.GelfandTriple

open PDE.Analysis.Variational
open scoped InnerProductSpace

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (T : GelfandTriple (V := V) (H := H)) (B : V →L[ℝ] StrongDual ℝ V)
variable (hnonneg : ∀ u, 0 ≤ B u u) (hcoercive : IsCoercive (B + T.energyToDual))

/-- The energy representative of a domain orbit, constructed using the unit resolvent. -/
def formEnergyOrbit (x : (T.formOperator B).domain) (t : ℝ) : V :=
  solveCLM (B + T.energyToDual) hcoercive
    (pivotLoadCLM T.inclusion
      ((T.formSemigroup B hnonneg hcoercive).realOrbit ((x : H) - T.formOperator B x) t))

/-- The constructed lift represents the orbit and satisfies its weak generator equation. -/
theorem formEnergyOrbit_spec (x : (T.formOperator B).domain) (t : ℝ) :
    T.inclusion (T.formEnergyOrbit B hnonneg hcoercive x t) =
        (T.formSemigroup B hnonneg hcoercive).realOrbit x t ∧
      B (T.formEnergyOrbit B hnonneg hcoercive x t) =
        -T.pivotToDual
          ((T.formSemigroup B hnonneg hcoercive).realOrbit (T.formOperator B x) t) := by
  let S := T.formSemigroup B hnonneg hcoercive
  obtain ⟨u, hu, hBu⟩ :=
    (T.hasGeneratorAt_formSemigroup_iff B hnonneg hcoercive _ _).1
      ((T.hasGeneratorAt_formSemigroup B hnonneg hcoercive x).map t.toNNReal)
  have hweak : IsWeakSolution (B + T.energyToDual)
      (pivotLoadCLM T.inclusion (S.realOrbit ((x : H) - T.formOperator B x) t)) u := by
    intro v
    have hv := DFunLike.congr_fun hBu v
    change B u v = -⟪S t.toNNReal (T.formOperator B x), T.inclusion v⟫_ℝ at hv
    change B u v + ⟪T.inclusion u, T.inclusion v⟫_ℝ =
      pivotLoadCLM T.inclusion (S.realOrbit ((x : H) - T.formOperator B x) t) v
    rw [pivotLoadCLM_apply, hu]
    unfold StronglyContinuousSemigroup.realOrbit
    rw [map_sub, inner_sub_left]
    linarith
  have hueq : u = T.formEnergyOrbit B hnonneg hcoercive x t :=
    hweak.eq_solve (B + T.energyToDual) hcoercive _
  rw [← hueq]
  exact ⟨hu, hBu⟩

/-- Domain orbits are continuous even in the stronger energy norm. -/
theorem continuous_formEnergyOrbit (x : (T.formOperator B).domain) :
    Continuous (T.formEnergyOrbit B hnonneg hcoercive x) :=
  (solveCLM (B + T.energyToDual) hcoercive).continuous.comp
    ((pivotLoadCLM T.inclusion).continuous.comp
      ((T.formSemigroup B hnonneg hcoercive).continuous_realOrbit
        ((x : H) - T.formOperator B x)))

/-- The energy lift attains the prescribed initial vector in the pivot space. -/
theorem inclusion_formEnergyOrbit_zero (x : (T.formOperator B).domain) :
    T.inclusion (T.formEnergyOrbit B hnonneg hcoercive x 0) = x := by
  rw [(T.formEnergyOrbit_spec B hnonneg hcoercive x 0).1,
    StronglyContinuousSemigroup.realOrbit_zero]

/-- The energy lift has the strong pivot derivative of the semigroup orbit. -/
theorem hasDerivAt_inclusion_formEnergyOrbit (x : (T.formOperator B).domain)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ T.inclusion (T.formEnergyOrbit B hnonneg hcoercive x s))
      ((T.formSemigroup B hnonneg hcoercive).realOrbit (T.formOperator B x) t) t := by
  have heq : (fun s ↦ T.inclusion (T.formEnergyOrbit B hnonneg hcoercive x s)) =
      (T.formSemigroup B hnonneg hcoercive).realOrbit x :=
    funext fun s ↦ (T.formEnergyOrbit_spec B hnonneg hcoercive x s).1
  rw [heq]
  exact T.hasDerivAt_formSemigroup B hnonneg hcoercive x ht

/-- The pivot derivative of the lifted orbit solves the homogeneous weak evolution equation. -/
theorem formEnergyOrbit_weakEquation (x : (T.formOperator B).domain)
    {t : ℝ} (ht : 0 < t) (v : V) :
    ⟪deriv (fun s ↦ T.inclusion (T.formEnergyOrbit B hnonneg hcoercive x s)) t,
      T.inclusion v⟫_ℝ + B (T.formEnergyOrbit B hnonneg hcoercive x t) v = 0 := by
  rw [(T.hasDerivAt_inclusion_formEnergyOrbit B hnonneg hcoercive x ht).deriv]
  have h := DFunLike.congr_fun (T.formEnergyOrbit_spec B hnonneg hcoercive x t).2 v
  change B _ v = -⟪_, T.inclusion v⟫_ℝ at h
  rw [h, add_neg_cancel]

end PDE.Analysis.Evolution.GelfandTriple
