/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.Iteration.Picard.SpatialTraces

/-!
# Matching coupled outputs at an H² trace

Two coupled outputs with the same L² value have the same continuous
vorticity, first spatial derivative, Hilbert coefficient and normalized velocity
at that time. Restarting from the terminal H² graph therefore matches the
transport right-hand side and the interior time-derivative traces. The two slabs
may have different durations, H² bounds and support radii.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Analysis PDE.Common
open scoped Topology Sobolev

open SobolevSpace SobolevSpace.GraphSpace

namespace DeGregorio.Iteration

variable {B D : NNReal} {T S R Q : ℝ} {hT : 0 ≤ T} {hS : 0 ≤ S}
  {F : C(Icc (0 : ℝ) T,
    supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-R) R) B)}
  {G : C(Icc (0 : ℝ) S,
    supportedHkBaseBall 1 2 univ (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ) ⁻¹' Icc (-Q) Q) D)}
  {W₀ V₀ : W^{2,2}((Set.univ : Set (ℝ^1)))} {w₀ z₀ : ℝ → ℝ} {c w d z : ℝ → ℝ → ℝ}

/-- Equality of the L² trace determines the spatial fields used by the coupled
transport equation, even when the outputs belong to different slabs and balls. -/
theorem IsHkFrozenOutput.spatial_fields_eq_of_base_eq
    (hF : IsHkFrozenOutput hT F F W₀ w₀ c w)
    (hG : IsHkFrozenOutput hS G G V₀ z₀ d z)
    (t : Icc (0 : ℝ) T) (s : Icc (0 : ℝ) S) (hbase : (F t).val = (G s).val) :
    (fun x ↦ w x t) = (fun x ↦ z x s) ∧
      deriv (fun x ↦ w x t) = deriv (fun x ↦ z x s) ∧
      (fun x ↦ c x t) = (fun x ↦ d x s) ∧
      (fun x ↦ hkCurveHilbertVelocity hT F x t) =
        (fun x ↦ hkCurveHilbertVelocity hS G x s) := by
  have hrep := hF.representative t
  rw [hbase] at hrep
  have hw : (fun x ↦ w x t) = (fun x ↦ z x s) :=
    (Continuous.ae_eq_iff_eq volume
      (hF.continuous.comp (continuous_id.prodMk continuous_const))
      (hG.continuous.comp (continuous_id.prodMk continuous_const))).mp
        (hrep.symm.trans (hG.representative s))
  have hpF := hF.hilbert_pair t
  have hpG := hG.hilbert_pair s
  rw [projIcc_of_mem hT t.property, hbase] at hpF
  rw [projIcc_of_mem hS s.property] at hpG
  have hc : (fun x ↦ c x t) = (fun x ↦ d x s) :=
    (Continuous.ae_eq_iff_eq volume
      (hF.coefficient_continuous.comp (continuous_id.prodMk continuous_const))
      (hG.coefficient_continuous.comp (continuous_id.prodMk continuous_const))).mp
        (hpF.ae_eq_right hpG)
  refine ⟨hw, congrArg deriv hw, hc, ?_⟩
  simp only [hkCurveHilbertVelocity, projIcc_of_mem hT t.property,
    projIcc_of_mem hS s.property, hbase]

/-- Restarting from the terminal H² graph matches both interior time-derivative
traces with the restart's initial transport value. -/
theorem IsHkFrozenOutput.matching_time_deriv_traces_of_restart
    (hF : IsHkFrozenOutput hT F F W₀ w₀ c w)
    (hG : IsHkFrozenOutput hS G G V₀ z₀ d z)
    (hV : wkpBaseCoordinateCLM V₀ = (F ⟨T, hT, le_rfl⟩).val) (x : ℝ) :
    Tendsto (fun t : Ioo (0 : ℝ) T ↦ deriv (w x) t)
        (comap ((↑) : Ioo (0 : ℝ) T → ℝ) (𝓝 T))
        (𝓝 (d x 0 * z x 0 -
          hkCurveHilbertVelocity hS G x 0 * deriv (fun y ↦ z y 0) x)) ∧
      Tendsto (fun s : Ioo (0 : ℝ) S ↦ deriv (z x) s)
        (comap ((↑) : Ioo (0 : ℝ) S → ℝ) (𝓝 (0 : ℝ)))
        (𝓝 (d x 0 * z x 0 -
          hkCurveHilbertVelocity hS G x 0 * deriv (fun y ↦ z y 0) x)) := by
  have hbase : (F ⟨T, hT, le_rfl⟩).val = (G ⟨0, le_rfl, hS⟩).val :=
    hV.symm.trans hG.initial_base.symm
  obtain ⟨hw, hderiv, hc, hu⟩ :=
    hF.spatial_fields_eq_of_base_eq hG ⟨T, hT, le_rfl⟩ ⟨0, le_rfl, hS⟩ hbase
  have hleft := hF.tendsto_time_deriv_from_interior x ⟨T, hT, le_rfl⟩
  have hrhs : c x T * w x T -
      hkCurveHilbertVelocity hT F x T * deriv (fun y ↦ w y T) x =
        d x 0 * z x 0 -
          hkCurveHilbertVelocity hS G x 0 * deriv (fun y ↦ z y 0) x := by
    rw [congrFun hw x, congrFun hc x, congrFun hu x, congrFun hderiv x]
  rw [hrhs] at hleft
  exact ⟨hleft, hG.tendsto_time_deriv_from_interior x ⟨0, le_rfl, hS⟩⟩

end DeGregorio.Iteration
