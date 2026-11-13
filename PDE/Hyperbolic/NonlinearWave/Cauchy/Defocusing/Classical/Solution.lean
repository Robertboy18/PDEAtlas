/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.ForwardUniqueness

/-!
# The forward classical cubic Cauchy problem

The predicate records the three-dimensional PDE, joint C² regularity
at positive time, C¹ regularity up to the initial slice, and both prescribed
right Cauchy traces.
-/

@[expose] public noncomputable section

open Set PDE.Common WaveEquation

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing

/-- A forward classical solution of `uₜₜ − Δu + u³ = 0` in ℝ³. -/
structure IsClassicalSolution (g h : ℝ^3 → ℝ) (u : ℝ^4 → ℝ) : Prop where
  /-- Joint C² regularity at every positive time. -/
  regularity : ContDiffOn ℝ 2 u {p | 0 < p 0}
  /-- Joint first derivatives extend continuously to the initial slice. -/
  initial_regularity : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}
  /-- The coordinate wave equation. -/
  pde : ∀ p : ℝ^4, 0 < p 0 → waveOperator u p + u p ^ 3 = 0
  /-- The prescribed displacement trace. -/
  position : ∀ x : ℝ^3, u (timeSpaceCons 0 x) = g x
  /-- The prescribed right velocity trace. -/
  velocity : ∀ x : ℝ^3,
    HasDerivWithinAt (fun t ↦ u (timeSpaceCons t x)) (h x) (Ici 0) 0

/-- Every two forward classical cubic solutions with the same Cauchy data agree.
The proof is local on each backward cone and requires no spatial norm bounds. -/
theorem IsClassicalSolution.eqOn {g h : ℝ^3 → ℝ} {u v : ℝ^4 → ℝ}
    (hu : IsClassicalSolution g h u) (hv : IsClassicalSolution g h v) :
    EqOn u v {p | 0 ≤ p 0} := by
  intro p hp
  change 0 ≤ p 0 at hp
  have hf : LocallyLipschitz (fun z : ℝ ↦ z ^ 3) :=
    (contDiff_id.pow 3 : ContDiff ℝ 1 (fun z : ℝ ↦ z ^ 3)).locallyLipschitz
  have he := eq_on_closed_cone_forward_locallyLipschitz hf
    hu.regularity hv.regularity hu.initial_regularity hv.initial_regularity
    (spatialPart p) (T := p 0 + 1) (by linarith)
    (fun t ht x _ ↦ hu.pde (timeSpaceCons t x) (by simpa using ht.1))
    (fun t ht x _ ↦ hv.pde (timeSpaceCons t x) (by simpa using ht.1))
    (fun x _ ↦ (hu.position x).trans (hv.position x).symm)
    (fun x _ ↦ (hu.velocity x).derivWithin (uniqueDiffOn_Ici 0 0 le_rfl) |>.trans
      ((hv.velocity x).derivWithin (uniqueDiffOn_Ici 0 0 le_rfl)).symm)
    (p 0) ⟨hp, by linarith⟩ (spatialPart p)
    (Metric.mem_closedBall_self (by linarith))
  simpa only [timeSpaceCons_spatialPart] using he

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing
