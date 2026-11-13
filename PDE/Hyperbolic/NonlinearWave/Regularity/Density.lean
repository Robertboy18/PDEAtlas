/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.Momentum.Balance
import Mathlib.Analysis.Calculus.ContDiff.Operations
import PDE.FDeriv.PartialDeriv.Regularity

/-!
# Smooth densities for a wave with a C¹ potential

The equation makes the composed reaction smooth. The derivative of the
composed potential is therefore smooth too.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace WaveEquation

/-- On an open region of a smooth wave, a C¹ potential has smooth
composition with the field. -/
theorem contDiffOn_potential_comp_of_smooth_wave {n : ℕ} {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {Ω : Set (ℝ^(n + 1))} (hΩ : IsOpen Ω) (hV : ContDiff ℝ 1 V) (hu : ContDiffOn ℝ ∞ u Ω)
    (hw : ∀ p ∈ Ω, semilinearWaveOperator V u p = 0) :
    ContDiffOn ℝ ∞ (fun p ↦ V (u p)) Ω := by
  have hp (i : Fin (n + 1)) : ContDiffOn ℝ ∞ (∂[i] u) Ω :=
    hu.partialDeriv i hΩ (by simp)
  have hpp (i : Fin (n + 1)) : ContDiffOn ℝ ∞ (∂[i] (∂[i] u)) Ω :=
    (hp i).partialDeriv i hΩ (by simp)
  have hbox : ContDiffOn ℝ ∞ (waveOperator u) Ω := by
    unfold waveOperator
    exact (hpp 0).sub (ContDiffOn.sum fun i _ ↦ hpp i.succ)
  have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ u) Ω :=
    hu.fderiv_of_isOpen hΩ (by simp)
  rw [contDiffOn_infty_iff_fderiv_of_isOpen hΩ]
  constructor
  · exact hV.differentiable one_ne_zero |>.comp_differentiableOn
      (hu.differentiableOn (by simp))
  · refine (hbox.neg.smul hfderiv).congr fun p hpΩ ↦ ?_
    have hup : DifferentiableAt ℝ u p :=
      (hu.contDiffAt (hΩ.mem_nhds hpΩ)).differentiableAt (by simp)
    have hchain := ((hV.differentiable one_ne_zero (u p)).hasDerivAt
      |>.comp_hasFDerivAt p hup.hasFDerivAt).fderiv
    have he : deriv V (u p) = -waveOperator u p := by
      have h := hw p hpΩ
      unfold semilinearWaveOperator at h
      linarith
    simpa only [he, Pi.smul_apply', Function.comp_def] using hchain

/-- The physical energy density is smooth on a smooth wave region,
even though the scalar potential is assumed only C¹. -/
theorem contDiffOn_energyDensity_of_smooth_wave {n : ℕ} {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {Ω : Set (ℝ^(n + 1))} (hΩ : IsOpen Ω) (hV : ContDiff ℝ 1 V) (hu : ContDiffOn ℝ ∞ u Ω)
    (hw : ∀ p ∈ Ω, semilinearWaveOperator V u p = 0) :
    ContDiffOn ℝ ∞ (semilinearWaveEnergyDensity V u) Ω := by
  have hK : ContDiffOn ℝ ∞ (classicalWaveEnergyDensity u) Ω := by
    rw [contDiffOn_infty]
    exact fun m p hp ↦ (contDiffAt_classicalWaveEnergyDensity (m := m)
      ((hu.contDiffAt (hΩ.mem_nhds hp)).of_le (by simp))).contDiffWithinAt
  exact hK.add (contDiffOn_potential_comp_of_smooth_wave hΩ hV hu hw)

/-- Every spatial stress component is smooth along the equation,
with no scalar reaction differentiability assumption. -/
theorem contDiffOn_spatialStress_of_smooth_wave {n : ℕ} {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {Ω : Set (ℝ^(n + 1))} (hΩ : IsOpen Ω) (hV : ContDiff ℝ 1 V) (hu : ContDiffOn ℝ ∞ u Ω)
    (hw : ∀ p ∈ Ω, semilinearWaveOperator V u p = 0) (i j : Fin n) :
    ContDiffOn ℝ ∞ (waveSpatialStress V u i j) Ω := by
  have hp (i : Fin (n + 1)) : ContDiffOn ℝ ∞ (∂[i] u) Ω :=
    hu.partialDeriv i hΩ (by simp)
  have hL : ContDiffOn ℝ ∞ (waveLagrangianDensity V u) Ω := by
    unfold waveLagrangianDensity
    exact (((hp 0).pow 2).sub (ContDiffOn.sum fun k _ ↦ (hp k.succ).pow 2)).div_const 2
      |>.sub (contDiffOn_potential_comp_of_smooth_wave hΩ hV hu hw)
  unfold waveSpatialStress
  split_ifs
  · exact ((hp i.succ).mul (hp j.succ)).add hL
  · exact ((hp i.succ).mul (hp j.succ)).add contDiffOn_const

end WaveEquation
