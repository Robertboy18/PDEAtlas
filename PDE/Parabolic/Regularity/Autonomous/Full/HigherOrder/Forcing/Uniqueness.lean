/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Regularity.Autonomous.Full.HigherOrder.Forcing

/-!
# Uniqueness of the finite parabolic derivative tuple

The pivot class determines every spatial Sobolev realization. Adjacent weak
time derivatives then determine every later entry of a finite tuple, so the
regularity estimates apply to any realization of the derivatives of the same
function.
-/

@[expose] public noncomputable section

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder.ForcingJet

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- The pivot class determines the full spatial Sobolev head. -/
theorem head_eq_of_headBase_eq (hopen : IsOpen Ω) {m : ℕ}
    {F G : ForcingJet n Ω a b m} (h : F.headBase = G.headBase) :
    F.head = G.head := by
  apply Lp.ext
  filter_upwards [F.headBase_ae, G.headBase_ae] with t hF hG
  apply wkpBaseCoordinateCLM_injective hopen
  rw [← hF, ← hG, h]

/-- A tuple of successive weak time derivatives is determined by its original
pivot class, including the final entry with no further derivative assumed. -/
theorem eq_of_headBase_eq (hopen : IsOpen Ω) {m : ℕ}
    {F G : ForcingJet n Ω a b m}
    (hF : F.HasWeakDerivatives) (hG : G.HasWeakDerivatives)
    (h : F.headBase = G.headBase) : F = G := by
  induction m with
  | zero => exact head_eq_of_headBase_eq hopen h
  | succ m ih =>
    apply Prod.ext (head_eq_of_headBase_eq hopen h)
    apply ih hF.2 hG.2
    have hderiv := hF.headBase
    rw [h] at hderiv
    have hae := hderiv.ae_eq isOpen_Ioo hG.headBase
    rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hae
    exact Lp.ext hae

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.HigherOrder.ForcingJet
