/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Parabolic.Heat.WholeSpace.SelfsimilarVectorDecay
public import PDE.Fluid.Incompressible.LerayProjection.Sobolev
public import PDE.Analysis.Evolution.Semigroup.SmoothingKernel

/-!
# The free self-similar smoothing kernel

The actual gaining family, extended by zero at nonpositive times, has a jointly
continuous action for positive lag. Splitting off a fixed positive gaining time
reduces this to joint continuity of the strongly continuous vector semigroup.
Leray projection retains this continuity and the quantitative smoothing bound.
-/

@[expose] public noncomputable section

open Filter Set SobolevSpace SobolevSpace.GraphSpace IncompressibleFlow
open PDE.Analysis.Evolution
open scoped NNReal Sobolev Topology

namespace HeatEquation.WholeSpace

variable {n k : ℕ}

/-- Extend the physical vector gaining operator by zero at nonpositive times. -/
def vectorSelfsimilarHeatGainKernel (n k : ℕ) (r : ℝ) :
    VectorH n k →L[ℝ] VectorH n (k + 1) :=
  if hr : 0 < r then vectorSelfsimilarHeatGain n k (.mk r hr.le) hr else 0

@[simp]
theorem vectorSelfsimilarHeatGainKernel_eq {r : ℝ} (hr : 0 < r) :
    vectorSelfsimilarHeatGainKernel n k r =
      vectorSelfsimilarHeatGain n k (.mk r hr.le) hr := by
  simp only [vectorSelfsimilarHeatGainKernel, dite_eq_left hr]

/-- The gaining kernel at a positive time, with the time as a nonnegative real. -/
theorem vectorSelfsimilarHeatGainKernel_eq_toNNReal {r : ℝ} (hr : 0 < r) :
    vectorSelfsimilarHeatGainKernel n k r =
      vectorSelfsimilarHeatGain n k r.toNNReal (Real.toNNReal_pos.mpr hr) := by
  rw [vectorSelfsimilarHeatGainKernel_eq hr]
  exact vectorSelfsimilarHeatGain_congr (Real.toNNReal_of_nonneg hr.le).symm _ _

/-- The gaining kernel at `τ + σ` is free evolution for `σ` followed by gain for `τ`. -/
theorem vectorSelfsimilarHeatGainKernel_add {τ σ : ℝ} (hτ : 0 < τ) (hσ : 0 ≤ σ)
    (u : VectorH n k) :
    vectorSelfsimilarHeatGainKernel n k (τ + σ) u =
      vectorSelfsimilarHeatGainKernel n k τ (vectorSelfsimilarHeat n k σ.toNNReal u) := by
  have hτσ : 0 < τ + σ := by linarith
  rw [vectorSelfsimilarHeatGainKernel_eq_toNNReal hτσ,
    vectorSelfsimilarHeatGainKernel_eq_toNNReal hτ, ← vectorSelfsimilarHeatGain_add_of_pos_left]
  rw [vectorSelfsimilarHeatGain_congr (Real.toNNReal_add hτ.le hσ)]

/-- Positive-lag continuity of the action follows from a fixed gaining step and
joint continuity of the strongly continuous semigroup. -/
theorem continuousOn_vectorSelfsimilarHeatGainKernel_apply :
    ContinuousOn (fun p : ℝ × VectorH n k ↦ vectorSelfsimilarHeatGainKernel n k p.1 p.2)
      (Ioi 0 ×ˢ univ) := by
  apply continuousOn_kernel_apply_of_semigroup_factor
    (vectorSelfsimilarHeatSemigroup n (k + 1))
  intro c r hc hcr u
  have hr := hc.trans hcr
  rw [vectorSelfsimilarHeatGainKernel_eq hr, vectorSelfsimilarHeatGainKernel_eq hc]
  have hsum : (r - c).toNNReal + NNReal.mk c hc.le = NNReal.mk r hr.le := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, Real.coe_toNNReal _ (sub_nonneg.mpr hcr.le)]
    exact sub_add_cancel _ _
  have h := vectorSelfsimilarHeatGain_add (r - c).toNNReal (.mk c hc.le) hc u
  simpa only [hsum, vectorSelfsimilarHeatSemigroup, MonoidHom.coe_mk,
    OneHom.coe_mk, toAdd_ofAdd] using h

/-- The projected gaining kernel uses the actual Sobolev Leray projection. -/
def projectedSelfsimilarHeatGainKernel (n k : ℕ) (r : ℝ) :
    VectorH n k →L[ℝ] VectorH n (k + 1) :=
  (leraySobolev n (k + 1)).comp (vectorSelfsimilarHeatGainKernel n k r)

/-- Projection preserves joint continuity of the positive-lag action. -/
theorem continuousOn_projectedSelfsimilarHeatGainKernel_apply :
    ContinuousOn
      (fun p : ℝ × VectorH n k ↦ projectedSelfsimilarHeatGainKernel n k p.1 p.2)
      (Ioi 0 ×ˢ univ) :=
  (leraySobolev n (k + 1)).continuous.comp_continuousOn
    continuousOn_vectorSelfsimilarHeatGainKernel_apply

/-- Leray projection is nonexpansive, so the projected kernel retains the free bound. -/
theorem norm_projectedSelfsimilarHeatGainKernel_le {r : ℝ} (hr : 0 < r) :
    ‖projectedSelfsimilarHeatGainKernel n k r‖ ≤
      selfsimilarSmoothingConstant n k * Real.exp (((2 : ℝ) - n) * r / 4) *
        (1 + (Real.sqrt r)⁻¹) := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg
      (mul_nonneg (selfsimilarSmoothingConstant_nonneg n k) (Real.exp_pos _).le)
      (by positivity))
  intro u
  exact (norm_leraySobolev_le _).trans (by
    rw [vectorSelfsimilarHeatGainKernel_eq hr]
    exact norm_vectorSelfsimilarHeatGain_le_exp (.mk r hr.le) hr u)

/-- Each kernel value is fixed by the actual Sobolev Leray projector. -/
theorem leraySobolev_projectedSelfsimilarHeatGainKernel (r : ℝ) (u : VectorH n k) :
    leraySobolev n (k + 1) (projectedSelfsimilarHeatGainKernel n k r u) =
      projectedSelfsimilarHeatGainKernel n k r u := by
  exact leraySobolev_idempotent _

end HeatEquation.WholeSpace
