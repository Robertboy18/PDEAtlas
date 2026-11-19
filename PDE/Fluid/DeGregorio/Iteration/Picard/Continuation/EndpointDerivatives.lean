/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.RestartTraces
public import PDE.Fluid.DeGregorio.Iteration.Picard.FixedPoint
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# One-sided classical derivatives at the closed time traces

The continuous transport right-hand side gives one-sided time derivatives of a
frozen output at both endpoints of `[0, T]`. The derivatives are taken within `Iic T`
and `Ici 0`, so the values of the field outside the slab do not enter.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Common
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

variable {B : NNReal} {T R : ℝ} {hT : 0 ≤ T}
  {F : C(Icc (0 : ℝ) T,
    supportedHkBaseBall 1 2 univ
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
  {W₀ : W^{2,2}((Set.univ : Set (ℝ^1)))} {w₀ : ℝ → ℝ} {c w : ℝ → ℝ → ℝ}

/-- The vorticity at each spatial point is continuous on the closed time slab. -/
theorem IsHkFrozenOutput.continuousOn_time
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) (x : ℝ) :
    ContinuousOn (w x) (Icc 0 T) := by
  have hc : Continuous (fun t ↦ w x (projIcc 0 T hT t)) := h.continuous.comp
    ((continuous_const (y := x)).prodMk (continuous_projIcc (h := hT)))
  exact hc.continuousOn.congr fun t ht ↦ by
    simp only [projIcc_of_mem hT ht]

/-- The left derivative at the terminal trace is the closed transport value. -/
theorem IsHkFrozenOutput.hasDerivWithinAt_time_terminal
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) (hpos : 0 < T) (x : ℝ) :
    HasDerivWithinAt (w x)
      (c x T * w x T -
        hkCurveHilbertVelocity hT F x T * deriv (fun y ↦ w y T) x) (Iic T) T := by
  apply hasDerivWithinAt_Iic_of_tendsto_deriv
    (s := Ioo 0 T)
    (fun t ht ↦
      (h.isClassicalSolutionOn.regularity.vorticity_time_differentiableAt
        (x := x) ht).differentiableWithinAt)
    ((h.continuousOn_time x T ⟨hT, le_rfl⟩).mono Ioo_subset_Icc_self)
    (Ioo_mem_nhdsLT hpos)
  have hc := h.continuous_transport_rhs.comp
    ((continuous_const (y := x)).prodMk (continuous_projIcc (h := hT)))
  have hlim := (hc.tendsto T).mono_left (nhdsWithin_le_nhds (s := Iio T))
  simp only [Function.comp_apply,
    projIcc_of_mem hT (show T ∈ Icc 0 T from ⟨hT, le_rfl⟩)] at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsLT hpos] with t ht
  simp only [Function.comp_apply, projIcc_of_mem hT (Ioo_subset_Icc_self ht)]
  exact (eq_sub_iff_add_eq.mpr (h.transport x t ht)).symm

/-- The right derivative at the initial trace is the closed transport value. -/
theorem IsHkFrozenOutput.hasDerivWithinAt_time_initial
    (h : IsHkFrozenOutput hT F F W₀ w₀ c w) (hpos : 0 < T) (x : ℝ) :
    HasDerivWithinAt (w x)
      (c x 0 * w x 0 -
        hkCurveHilbertVelocity hT F x 0 * deriv (fun y ↦ w y 0) x) (Ici 0) 0 := by
  apply hasDerivWithinAt_Ici_of_tendsto_deriv
    (s := Ioo 0 T)
    (fun t ht ↦
      (h.isClassicalSolutionOn.regularity.vorticity_time_differentiableAt
        (x := x) ht).differentiableWithinAt)
    ((h.continuousOn_time x 0 ⟨le_rfl, hT⟩).mono Ioo_subset_Icc_self)
    (Ioo_mem_nhdsGT hpos)
  have hc := h.continuous_transport_rhs.comp
    ((continuous_const (y := x)).prodMk (continuous_projIcc (h := hT)))
  have hlim := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simp only [Function.comp_apply,
    projIcc_of_mem hT (show 0 ∈ Icc 0 T from ⟨le_rfl, hT⟩)] at hlim
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT hpos] with t ht
  simp only [Function.comp_apply, projIcc_of_mem hT (Ioo_subset_Icc_self ht)]
  exact (eq_sub_iff_add_eq.mpr (h.transport x t ht)).symm

end DeGregorio.Iteration
