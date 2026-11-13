/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Reflection
public import PDE.Fluid.DeGregorio.DynamicRescaling
import CAS.ExactTactic

/-!
# Reflected classical De Gregorio solutions

The transformation `(ω,u)(x,t) ↦ (-ω(-x,t),-u(-x,t))` preserves both the transport
equation and the concrete spectral Biot–Savart relation. It also preserves the
rescaled equation with the same prescribed rates. These statements hold for
arbitrary fields.
-/

@[expose] public section

noncomputable section

open MeasureTheory PDE.Analysis
open scoped ContDiff

namespace DeGregorio

/-- Signed spatial reflection of both physical fields. Its fixed points are
pairs of spatially odd functions. -/
def reflectedFields (fields : Fields) : Fields where
  vorticity := fun x t ↦ -fields.vorticity (-x) t
  velocity := fun x t ↦ -fields.velocity (-x) t

/-- Time differentiation of the reflected vorticity retains the output sign. -/
theorem deriv_reflectedFields_time (fields : Fields) (x t : ℝ) :
    deriv ((reflectedFields fields).vorticity x) t =
      -deriv (fields.vorticity (-x)) t := by
  change deriv (-(fields.vorticity (-x))) t = _
  exact deriv.neg

/-- Spatial differentiation cancels the two signs in reflected vorticity. -/
theorem deriv_reflectedFields_vorticity (fields : Fields) (x t : ℝ) :
    deriv (fun y ↦ (reflectedFields fields).vorticity y t) x =
      deriv (fun y ↦ fields.vorticity y t) (-x) := by
  change deriv (-(fun y ↦ fields.vorticity (-y) t)) x = _
  rw [deriv.neg, deriv_comp_neg (f := fun y ↦ fields.vorticity y t), neg_neg]

/-- Spatial differentiation cancels the two signs in reflected velocity. -/
theorem deriv_reflectedFields_velocity (fields : Fields) (x t : ℝ) :
    deriv (fun y ↦ (reflectedFields fields).velocity y t) x =
      deriv (fun y ↦ fields.velocity y t) (-x) := by
  change deriv (-(fun y ↦ fields.velocity (-y) t)) x = _
  rw [deriv.neg, deriv_comp_neg (f := fun y ↦ fields.velocity y t), neg_neg]

/-- Reflection preserves the derivative regularity in the classical model. -/
theorem HasClassicalRegularityOn.reflectedFields {fields : Fields} {times : Set ℝ}
    (h : HasClassicalRegularityOn fields times) :
    HasClassicalRegularityOn (reflectedFields fields) times where
  vorticity_differentiableAt {x t} ht := by
    have hm : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ (-p.1, p.2)) (x, t) :=
      differentiableAt_fst.neg.prodMk differentiableAt_snd
    exact ((h.vorticity_differentiableAt (x := -x) ht).comp (x, t) hm).neg
  velocity_differentiableAt {x t} ht :=
    ((h.velocity_differentiableAt (x := -x) ht).comp x differentiableAt_id.neg).neg

/-- Reflection preserves the generalized transport equation. -/
theorem SatisfiesTransportEquationOn.reflectedFields {a : ℝ}
    {fields : Fields} {times : Set ℝ} (h : SatisfiesTransportEquationOn a fields times) :
    SatisfiesTransportEquationOn a (reflectedFields fields) times := by
  intro x t ht
  rw [deriv_reflectedFields_time, deriv_reflectedFields_vorticity,
    deriv_reflectedFields_velocity]
  have hpde := h (x := -x) ht
  dsimp [DeGregorio.reflectedFields]
  cas

/-- Reflection preserves the concrete spectral Biot–Savart relation. -/
theorem SatisfiesBiotSavartOn.reflectedFields {fields : Fields} {times : Set ℝ}
    (h : SatisfiesBiotSavartOn fields times) :
    SatisfiesBiotSavartOn (reflectedFields fields) times := by
  intro t ht
  have hderiv :
      deriv (fun x ↦ (DeGregorio.reflectedFields fields).velocity x t) =
        fun x ↦ deriv (fun y ↦ fields.velocity y t) (-x) :=
    funext fun x ↦ deriv_reflectedFields_velocity fields x t
  rw [hderiv]
  exact (h ht).neg_reflect

/-- Signed reflection gives another classical solution. -/
theorem IsClassicalSolutionOn.reflectedFields {a : ℝ}
    {fields : Fields} {times : Set ℝ} (h : IsClassicalSolutionOn a fields times) :
    IsClassicalSolutionOn a (reflectedFields fields) times where
  regularity := h.regularity.reflectedFields
  transport := h.transport.reflectedFields
  biotSavart := h.biotSavart.reflectedFields

/-- The prescribed spatial and amplitude rates are unchanged by reflection. -/
theorem SatisfiesRescaledTransportEquationOn.reflectedFields {a : ℝ}
    {fields : Fields} {cl cw : ℝ → ℝ} {times : Set ℝ}
    (h : SatisfiesRescaledTransportEquationOn a fields cl cw times) :
    SatisfiesRescaledTransportEquationOn a (reflectedFields fields) cl cw times := by
  intro x t ht
  rw [deriv_reflectedFields_time, deriv_reflectedFields_vorticity,
    deriv_reflectedFields_velocity]
  have hpde := h (x := -x) ht
  dsimp [DeGregorio.reflectedFields]
  cas

/-- Signed reflection gives another classical rescaled solution with the same rates. -/
theorem IsClassicalRescaledSolutionOn.reflectedFields {a : ℝ}
    {fields : Fields} {cl cw : ℝ → ℝ} {times : Set ℝ}
    (h : IsClassicalRescaledSolutionOn a fields cl cw times) :
    IsClassicalRescaledSolutionOn a (reflectedFields fields) cl cw times where
  regularity := h.regularity.reflectedFields
  transport := h.transport.reflectedFields
  biotSavart := h.biotSavart.reflectedFields

end DeGregorio
