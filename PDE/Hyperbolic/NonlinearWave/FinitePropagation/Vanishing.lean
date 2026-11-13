/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.ForwardConeEnergyIdentity

/-!
# The semilinear cone energy

For a nonnegative `C¹` potential, the semilinear energy on the shrinking backward cone is
nonnegative and antitone. If `V(0) = 0`, zero Cauchy data on the base ball give zero energy on
the base slice.
-/

@[expose] public section

namespace WaveEquation

open Filter MeasureTheory PDE.Analysis Set
open scoped BigOperators RealInnerProductSpace

variable {n : ℕ}

/-- The semilinear shrinking-cone energy is antitone for nonnegative
potentials. -/
theorem semilinearBackwardConeEnergy_antitone [Fact (0 < n)] {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hV : ContDiff ℝ 1 V) (hVnonneg : ∀ z, 0 ≤ V z) (hu : ContDiff ℝ 2 u) (c : ℝ^n) {a T : ℝ}
    (hwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      semilinearWaveOperator (n := n) V u (PDE.Common.timeSpaceCons (n := n) t x) = 0) :
    AntitoneOn (semilinearBackwardConeEnergy (n := n) V u c T) (Set.Ico a T) := by
  have hderiv : ∀ t ∈ Set.Ico a T, HasDerivAt (semilinearBackwardConeEnergy (n := n) V u c T)
          (sphereIntegral n (semilinearWaveConeBoundaryFlux (n := n) V u c t) c (T - t))
          t := by
    intro t ht
    exact hasDerivAt_semilinearBackwardConeEnergy_of_solution (n := n) hV hu c T ht.2 (hwave t ht)
  apply antitoneOn_of_deriv_nonpos (convex_Ico a T)
  · exact fun t ht ↦ (hderiv t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' := interior_subset ht
    rw [(hderiv t ht').deriv]
    exact sphereIntegral_semilinearWaveConeBoundaryFlux_nonpos
      (n := n) V hVnonneg u c t (sub_pos.mpr ht'.2)

/-- The semilinear shrinking-cone energy is nonnegative for a nonnegative
potential. -/
theorem semilinearBackwardConeEnergy_nonneg (V : ℝ → ℝ) (hVnonneg : ∀ z, 0 ≤ V z)
    (u : ℝ^(n + 1) → ℝ) (c : ℝ^n) (T t : ℝ) :
    0 ≤ semilinearBackwardConeEnergy (n := n) V u c T t := by
  unfold semilinearBackwardConeEnergy
  apply add_nonneg (backwardConeEnergy_nonneg (n := n) u c T t)
  unfold ballIntegral
  exact MeasureTheory.setIntegral_nonneg measurableSet_ball fun x _ ↦ hVnonneg _

/-- Zero Cauchy data on the base ball give zero semilinear energy on the base
cone slice when `V(0) = 0`. -/
theorem semilinearBackwardConeEnergy_initial_eq_zero {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hVzero : V 0 = 0) (hu : ContDiff ℝ 2 u) (c : ℝ^n) {a T : ℝ}
    (hpos : ∀ x ∈ Metric.closedBall c (T - a), u (PDE.Common.timeSpaceCons (n := n) a x) = 0)
    (hvel : ∀ x ∈ Metric.closedBall c (T - a),
      (∂[0] u) (PDE.Common.timeSpaceCons (n := n) a x) = 0) :
    semilinearBackwardConeEnergy (n := n) V u c T a = 0 := by
  unfold semilinearBackwardConeEnergy
  rw [backwardConeEnergy_initial_eq_zero (n := n) hu c hpos hvel]
  simp only [zero_add, ballIntegral]
  apply MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero
  exact Filter.Eventually.of_forall fun x hx ↦ by
    rw [hpos x (Metric.ball_subset_closedBall hx), hVzero]

end WaveEquation
