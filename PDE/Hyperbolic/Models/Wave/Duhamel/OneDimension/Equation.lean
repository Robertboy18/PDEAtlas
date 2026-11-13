/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.Models.Wave.Duhamel.OneDimension.Construction

/-!
# The one-dimensional forced wave equation

Each emitted d'Alembert wave has zero residual and initial velocity equal to
its source slice. The retarded wave identity therefore leaves exactly the
forcing at the current spacetime point.
-/

@[expose] public noncomputable section

namespace WaveEquation

open PDE.Common

/-- The one-dimensional retarded field solves `u_tt - u_xx = f` on forward spacetime. -/
theorem waveOperator_dAlembertDuhamelSolution {f : ℝ^2 → ℝ} (hf : ContDiffOn ℝ 1 f {p | 0 ≤ p 0})
    {p : ℝ^2} (hp : 0 ≤ p 0) :
    waveOperator (dAlembertDuhamelSolution f) p = f p := by
  let F (s : ℝ) := dAlembertSolution1D (fun _ ↦ 0) (fun x ↦ f (timeSpaceCons (max 0 s) x))
  have hres (s : ℝ) (q : ℝ^2) : waveOperator (F s) q = 0 :=
    waveOperator_dAlembertFormula _ _ contDiff_const (contDiff_dAlembert_forward_velocity hf s) q
  have he := waveOperator_retardedWave (contDiff_two_dAlembertSolution1D_forward hf)
    (fun _ hj ↦ continuous_iteratedFDeriv_dAlembertSolution1D_forward hf hj)
    (fun _ x ↦ dAlembert_satisfies_initial_pos _ _ x) (spatialPartCLM 1 p) (p 0)
  change waveOperator (dAlembertDuhamelSolution f) (timeSpaceCons (p 0) (spatialPartCLM 1 p)) =
    (∂[0] (F (p 0))) (timeSpaceCons 0 (spatialPartCLM 1 p)) + ∫ s in (0 : ℝ)..p 0,
        waveOperator (F s) (timeSpaceCons (p 0 - s) (spatialPartCLM 1 p)) at he
  simp only [hres, intervalIntegral.integral_zero, add_zero] at he
  have hv : (∂[0] (F (p 0))) (timeSpaceCons 0 (spatialPartCLM 1 p)) =
      f (timeSpaceCons (max 0 (p 0)) (spatialPartCLM 1 p)) :=
    dAlembert_satisfies_initial_vel _ _ contDiff_const
      (contDiff_dAlembert_forward_velocity hf (p 0)) (spatialPartCLM 1 p)
  simpa only [hv, max_eq_right hp, timeSpaceCons_spatialPartCLM] using he

end WaveEquation
