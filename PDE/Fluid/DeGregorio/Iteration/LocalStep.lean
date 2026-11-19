/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Transport.LocalExistence
public import PDE.Analysis.Fourier.HilbertTransform.RealPair.Sobolev

/-!
# A transport step with the Hilbert velocity

Freeze a compact C² vorticity profile, construct its normalized Hilbert velocity,
and solve the resulting linear transport equation near any initial point. Both
coefficients come from the principal value, identified with the spectral
transform. Its global velocity Lipschitz bound is derived from the
input H¹ norms.

The output is a transport iterate: its velocity is computed from the frozen input,
not from the output.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory PDE.Analysis
open scoped NNReal

namespace DeGregorio

/-- A compact C² frozen input gives the normalized Biot–Savart velocity,
its input-norm Lipschitz bound, and a constructed local Eulerian transport step.
The transported initial datum may differ from the frozen input. -/
theorem exists_local_hilbert_transport_step
    (f w₀ : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    (hw₀ : ContDiff ℝ 1 w₀) (x₀ : ℝ) :
    IsHilbertPair f (deriv (hilbertPVVelocity f)) ∧
      hilbertPVVelocity f 0 = 0 ∧
      LipschitzWith
        ((eLpNorm f 2 volume).toNNReal + (eLpNorm (deriv f) 2 volume).toNNReal)
        (hilbertPVVelocity f) ∧
      ∃ V : Set (ℝ × ℝ), IsOpen V ∧ (x₀, 0) ∈ V ∧
        ∃ w : ℝ → ℝ → ℝ, ContDiffOn ℝ 1 (Function.uncurry w) V ∧
          (∀ x, (x, 0) ∈ V → w x 0 = w₀ x) ∧
          ∀ x t, (x, t) ∈ V →
            deriv (w x) t + hilbertPVVelocity f x * deriv (fun y ↦ w y t) x =
              deriv (hilbertPVVelocity f) x * w x t := by
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hH : ContDiff ℝ 1 (hilbertPV f) :=
    contDiff_hilbertPV_of_contDiff_succ_compactSupport 1 hf hsupp
  have hd := hasDerivAt_hilbertPVVelocity_of_contDiff_one_compactSupport hf₁ hsupp
  have hu : ContDiff ℝ 1 (hilbertPVVelocity f) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun x ↦ (hd x).differentiableAt, ?_⟩
    rw [show deriv (hilbertPVVelocity f) = hilbertPV f from funext fun x ↦ (hd x).deriv]
    exact hH.continuous
  refine ⟨isHilbertPair_deriv_hilbertPVVelocity hf₁ hsupp, hilbertPVVelocity_zero f,
    lipschitzWith_hilbertPVVelocity_of_contDiff_two_compactSupport hf hsupp, ?_⟩
  obtain ⟨V, hV, hxV, w, hw, hinit, hpde⟩ :=
    TransportEquation.exists_local_transport_solution
    (fun x _ ↦ hilbertPVVelocity f x) (fun x _ ↦ hilbertPV f x)
    (hu.comp contDiff_fst) (hH.comp contDiff_fst) w₀ hw₀ x₀
  refine ⟨V, hV, hxV, w, hw, hinit, ?_⟩
  intro x t hxt
  rw [(hd x).deriv]
  exact hpde x t hxt

end DeGregorio
