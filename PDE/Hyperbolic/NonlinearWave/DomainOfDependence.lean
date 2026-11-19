/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.QuadraticEnergy
import PDE.Hyperbolic.NonlinearWave.FinitePropagation.Vanishing
import PDE.Hyperbolic.NonlinearWave.Stability

/-!
# Domain of dependence for semilinear wave equations

We prove local uniqueness for two classical solutions of

`uₜₜ - Δu + f(u) = 0`

with a common globally Lipschitz nonlinearity. For the difference `w = u - v`,
the quadratic cone energy

`E(t) = 1 / 2 ∫_{B(c,T-t)} (wₜ² + |Dₓw|² + w²)`

satisfies `E'(t) ≤ (1 + K) E(t)`. The lateral cone flux is nonpositive, while
the volume residual is controlled by the Lipschitz constant `K`. Grönwall's
inequality therefore propagates equality of the Cauchy data throughout the
backward cone. This energy is the energy `e(t)` of the proof of Theorem 3 of Evans, §12.1.2,
for the difference of the two solutions.

The closed-cone theorem has the form of Evans's statement, whose ball `B(x₀, t₀)` and cone
`K(x₀, t₀)` are closed. The final theorem is the open-cone form, with data on the open base
ball; we obtain it by shrinking the vertex time and applying the closed-cone result.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.2, definition of the cone `K(x₀, t₀)`, Theorem 3
  and its proof; Appendix A.2, notation for balls.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory PDE.Analysis Set

namespace WaveEquation

variable {n : ℕ}

/-- The derivative of the quadratic difference energy on a shrinking cone is
bounded above by `(1 + K)` times that energy. -/
theorem deriv_semilinearBackwardConeEnergy_sub_le [Fact (0 < n)] {K : NNReal} {f : ℝ → ℝ}
    {u v : ℝ^(n + 1) → ℝ} (hf : LipschitzWith K f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (c : ℝ^n) (T : ℝ) {t : ℝ} (ht : t < T)
    (huwave : ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) u p + f (u p) = 0)
    (hvwave : ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) v p + f (v p) = 0) :
    deriv (semilinearBackwardConeEnergy (n := n) (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) c T)
      t ≤ (1 + (K : ℝ)) *
      semilinearBackwardConeEnergy (n := n) (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) c T t :=
  deriv_quadraticConeEnergy_le (hu.sub hv) c T ht fun x hx ↦ (le_abs_self _).trans
    (abs_semilinearWaveEnergyBalanceResidual_sub_le hf hu hv (huwave x hx) (hvwave x hx))

/-- The quadratic difference energy of two semilinear waves grows at most
exponentially along a backward cone. -/
theorem semilinearBackwardConeEnergy_sub_le_exp [Fact (0 < n)] {K : NNReal} {f : ℝ → ℝ}
    {u v : ℝ^(n + 1) → ℝ} (hf : LipschitzWith K f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (c : ℝ^n) {a T : ℝ}
    (huwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) u p + f (u p) = 0)
    (hvwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) v p + f (v p) = 0)
    {t : ℝ} (ht : t ∈ Set.Ico a T) :
    semilinearBackwardConeEnergy (n := n) (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) c T t ≤
      semilinearBackwardConeEnergy (n := n) (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) c T a *
      Real.exp ((1 + (K : ℝ)) * (t - a)) :=
  quadraticConeEnergy_le_exp (hu.sub hv) c (C := 1 + (K : ℝ)) (fun s hs x hx ↦ (le_abs_self _).trans
    (abs_semilinearWaveEnergyBalanceResidual_sub_le hf hu hv (huwave s hs x hx) (hvwave s hs x hx)))
    ht

/-- Equal Cauchy data on the base ball force the quadratic difference energy
to vanish on every open slice of the backward cone. -/
theorem semilinearBackwardConeEnergy_sub_eq_zero_of_eq_cauchyData [Fact (0 < n)] {K : NNReal}
    {f : ℝ → ℝ} {u v : ℝ^(n + 1) → ℝ} (hf : LipschitzWith K f) (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v) (c : ℝ^n) {a T : ℝ}
    (huwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) u p + f (u p) = 0)
    (hvwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) v p + f (v p) = 0)
    (hposition : ∀ x ∈ Metric.closedBall c (T - a), u (PDE.Common.timeSpaceCons (n := n) a x) =
      v (PDE.Common.timeSpaceCons (n := n) a x))
    (hvelocity : ∀ x ∈ Metric.closedBall c (T - a),
      (∂[0] u) (PDE.Common.timeSpaceCons (n := n) a x) =
      (∂[0] v) (PDE.Common.timeSpaceCons (n := n) a x)) {t : ℝ} (ht : t ∈ Set.Ico a T) :
    semilinearBackwardConeEnergy (n := n) (fun z : ℝ ↦ z ^ 2 / 2) (fun p ↦ u p - v p) c T t =
      0 := by
  have hinitial := semilinearBackwardConeEnergy_initial_eq_zero (V := fun z : ℝ ↦ z ^ 2 / 2)
    (by simp) (hu.sub hv) c (fun x hx ↦ sub_eq_zero.mpr (hposition x hx)) fun x hx ↦ by
      rw [PDE.partialDeriv_sub (hu.differentiable (by norm_num)).differentiableAt
        (hv.differentiable (by norm_num)).differentiableAt, hvelocity x hx, sub_self]
  refine le_antisymm ?_ (semilinearBackwardConeEnergy_nonneg _ (fun z ↦ by positivity) _ c T t)
  simpa [hinitial] using semilinearBackwardConeEnergy_sub_le_exp hf hu hv c huwave hvwave ht

/-- Two classical semilinear waves with a common globally Lipschitz
nonlinearity and equal Cauchy data on the base ball agree throughout the
closed backward cone. -/
theorem eq_on_closed_backwardCone_of_eq_cauchyData_semilinear [Fact (0 < n)] {K : NNReal}
    {f : ℝ → ℝ} {u v : ℝ^(n + 1) → ℝ} (hf : LipschitzWith K f) (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v) (c : ℝ^n) {a T : ℝ}
    (huwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) u p + f (u p) = 0)
    (hvwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) v p + f (v p) = 0)
    (hposition : ∀ x ∈ Metric.closedBall c (T - a), u (PDE.Common.timeSpaceCons (n := n) a x) =
      v (PDE.Common.timeSpaceCons (n := n) a x))
    (hvelocity : ∀ x ∈ Metric.closedBall c (T - a),
      (∂[0] u) (PDE.Common.timeSpaceCons (n := n) a x) =
      (∂[0] v) (PDE.Common.timeSpaceCons (n := n) a x)) :
    ∀ t ∈ Set.Icc a T, ∀ x ∈ Metric.closedBall c (T - t),
      u (PDE.Common.timeSpaceCons (n := n) t x) = v (PDE.Common.timeSpaceCons (n := n) t x) := by
  have hw : ContDiff ℝ 2 fun p ↦ u p - v p := hu.sub hv
  have hzero := eq_zero_on_closed_backwardCone_of_energy_eq_zero hw c
    (fun x hx ↦ sub_eq_zero.mpr (hposition x hx)) fun t ht ↦ by
      have htotal := semilinearBackwardConeEnergy_sub_eq_zero_of_eq_cauchyData hf hu hv c huwave
        hvwave hposition hvelocity ht
      have hq : 0 ≤ ballIntegral n (fun y ↦
          (u (PDE.Common.timeSpaceCons t y) - v (PDE.Common.timeSpaceCons t y)) ^ 2 / 2)
            c (T - t) :=
        setIntegral_nonneg measurableSet_ball fun x _ ↦ by positivity
      unfold semilinearBackwardConeEnergy at htotal
      linarith [backwardConeEnergy_nonneg (fun p ↦ u p - v p) c T t]
  exact fun t ht x hx ↦ sub_eq_zero.mp (hzero t ht x hx)

/-- Two classical semilinear waves with a common globally Lipschitz
nonlinearity and equal Cauchy data on the open base ball agree throughout the
open backward cone. -/
theorem eq_on_open_backwardCone_of_eq_cauchyData_semilinear [Fact (0 < n)] {K : NNReal} {f : ℝ → ℝ}
    {u v : ℝ^(n + 1) → ℝ} (hf : LipschitzWith K f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (c : ℝ^n) {a T : ℝ}
    (huwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) u p + f (u p) = 0)
    (hvwave : ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t),
      let p := PDE.Common.timeSpaceCons (n := n) t x; waveOperator (n := n) v p + f (v p) = 0)
    (hposition : ∀ x ∈ Metric.ball c (T - a), u (PDE.Common.timeSpaceCons (n := n) a x) =
      v (PDE.Common.timeSpaceCons (n := n) a x))
    (hvelocity : ∀ x ∈ Metric.ball c (T - a), (∂[0] u) (PDE.Common.timeSpaceCons (n := n) a x) =
      (∂[0] v) (PDE.Common.timeSpaceCons (n := n) a x)) :
    ∀ t ∈ Set.Ico a T, ∀ x ∈ Metric.ball c (T - t), u (PDE.Common.timeSpaceCons (n := n) t x) =
      v (PDE.Common.timeSpaceCons (n := n) t x) := by
  intro t ht x hx
  have htxT : t + dist x c < T := by rw [Metric.mem_ball] at hx; linarith
  have hlarge : (t + dist x c + T) / 2 < T := by linarith
  refine eq_on_closed_backwardCone_of_eq_cauchyData_semilinear (T := (t + dist x c + T) / 2) hf hu
    hv c (fun s hs y hy ↦ huwave s ⟨hs.1, hs.2.trans hlarge⟩ y
      (Metric.ball_subset_ball (by linarith) hy))
    (fun s hs y hy ↦ hvwave s ⟨hs.1, hs.2.trans hlarge⟩ y
      (Metric.ball_subset_ball (by linarith) hy))
    (fun y hy ↦ hposition y (Metric.closedBall_subset_ball (by linarith) hy))
    (fun y hy ↦ hvelocity y (Metric.closedBall_subset_ball (by linarith) hy)) t
    ⟨ht.1, by linarith [dist_nonneg (x := x) (y := c)]⟩ x ?_
  rw [Metric.mem_closedBall]
  linarith

end WaveEquation
