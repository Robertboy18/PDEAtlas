/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.RealLine.Cauchy
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Uniqueness
public import PDE.Hyperbolic.NonlinearWave.RealLine.Continuation.Localization

/-!
# Classical uniqueness on the real line

Two C² fields satisfying `u_tt - u_xx = -f(u)` and the same Cauchy data on a
base interval agree on its closed backward light cone. The reaction need only
be locally Lipschitz. Compactness supplies a Lipschitz constant on the two
solution ranges; the cone-energy argument then applies to a real
Lipschitz extension of the reaction.

The hypotheses concern the PDE and initial values. The cone theorem uses ambient C² fields; the
open-strip theorem only requires C² regularity for `t < T` and assumes no terminal trace. The PDE is
required only on the indicated cone or strip. Uniqueness of the constructed global field is asserted
at nonnegative times, since its negative-time extension is not prescribed by the Cauchy problem.
-/

@[expose] public noncomputable section

open PDE.Common PDE.Analysis Set
open scoped Topology BoundedContinuousFunction

namespace WaveEquation

/-- A Lipschitz restriction of the source to a set containing both solution ranges
is sufficient for classical domain of dependence in one space dimension. -/
theorem eq_on_closed_backwardCone_of_eq_cauchyData_lipschitzOn {K : NNReal} {f : ℝ → ℝ} {s : Set ℝ}
    {u v : ℝ^2 → ℝ} (hf : LipschitzOnWith K f s) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (c : ℝ^1) {a T : ℝ}
    (huwave : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator (n := 1) u (timeSpaceCons t x) = -f (u (timeSpaceCons t x)))
    (hvwave : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator (n := 1) v (timeSpaceCons t x) = -f (v (timeSpaceCons t x)))
    (hus : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t), u (timeSpaceCons t x) ∈ s)
    (hvs : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t), v (timeSpaceCons t x) ∈ s)
    (hposition : ∀ x ∈ Metric.closedBall c (T - a), u (timeSpaceCons a x) = v (timeSpaceCons a x))
    (hvelocity : ∀ x ∈ Metric.closedBall c (T - a), (∂[0] u) (timeSpaceCons a x) =
      (∂[0] v) (timeSpaceCons a x)) :
    ∀ t ∈ Icc a T, ∀ x ∈ Metric.closedBall c (T - t),
      u (timeSpaceCons t x) = v (timeSpaceCons t x) := by
  exact SmallData.Classical.eq_on_closed_backwardCone_of_eq_cauchyData_lipschitzOn
    (n := 1) hf hu hv c huwave hvwave hus hvs hposition hvelocity

/-- All ambient C² solutions with a locally Lipschitz reaction obey finite speed
of dependence. Only the PDE inside the cone and data on its base are required. -/
theorem eq_on_closed_backwardCone_of_eq_cauchyData_locallyLipschitz {f : ℝ → ℝ} {u v : ℝ^2 → ℝ}
    (hf : LocallyLipschitz f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (c : ℝ^1) {a T : ℝ}
    (huwave : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator (n := 1) u (timeSpaceCons t x) = -f (u (timeSpaceCons t x)))
    (hvwave : ∀ t ∈ Ico a T, ∀ x ∈ Metric.ball c (T - t),
      waveOperator (n := 1) v (timeSpaceCons t x) = -f (v (timeSpaceCons t x)))
    (hposition : ∀ x ∈ Metric.closedBall c (T - a), u (timeSpaceCons a x) = v (timeSpaceCons a x))
    (hvelocity : ∀ x ∈ Metric.closedBall c (T - a), (∂[0] u) (timeSpaceCons a x) =
      (∂[0] v) (timeSpaceCons a x)) :
    ∀ t ∈ Icc a T, ∀ x ∈ Metric.closedBall c (T - t),
      u (timeSpaceCons t x) = v (timeSpaceCons t x) := by
  exact SmallData.Classical.eq_on_closed_backwardCone_of_eq_cauchyData_locallyLipschitz
    (n := 1) hf hu hv c huwave hvwave hposition hvelocity

/-- Equality of Cauchy data propagates across a finite forward strip for arbitrary
C² solutions. No global bound on either field is needed. -/
theorem eq_on_forward_strip_of_eq_cauchyData_locallyLipschitz {f : ℝ → ℝ} {u v : ℝ^2 → ℝ} {a T : ℝ}
    (hf : LocallyLipschitz f) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (huwave : ∀ p : ℝ^2, p 0 ∈ Ico a T → waveOperator (n := 1) u p = -f (u p))
    (hvwave : ∀ p : ℝ^2, p 0 ∈ Ico a T → waveOperator (n := 1) v p = -f (v p))
    (hposition : ∀ x : ℝ^1, u (timeSpaceCons a x) = v (timeSpaceCons a x))
    (hvelocity : ∀ x : ℝ^1, (∂[0] u) (timeSpaceCons a x) = (∂[0] v) (timeSpaceCons a x)) :
    ∀ p : ℝ^2, p 0 ∈ Icc a T → u p = v p := by
  exact SmallData.Classical.eq_on_forward_strip_of_eq_cauchyData_locallyLipschitz
    (n := 1) hf hu hv huwave hvwave hposition hvelocity

/-- Classical uniqueness before a terminal time requires no regularity at that
time. The fields need only be C² on the open half-space `t < T`, including a
neighborhood of the initial slice. -/
theorem eq_on_forward_open_strip_of_eq_cauchyData_locallyLipschitz {f : ℝ → ℝ} {u v : ℝ^2 → ℝ}
    {a T : ℝ} (hf : LocallyLipschitz f) (hu : ContDiffOn ℝ 2 u {p | p 0 < T})
    (hv : ContDiffOn ℝ 2 v {p | p 0 < T})
    (huwave : ∀ p : ℝ^2, p 0 ∈ Ico a T → waveOperator (n := 1) u p = -f (u p))
    (hvwave : ∀ p : ℝ^2, p 0 ∈ Ico a T → waveOperator (n := 1) v p = -f (v p))
    (hposition : ∀ x : ℝ^1, u (timeSpaceCons a x) = v (timeSpaceCons a x))
    (hvelocity : ∀ x : ℝ^1, (∂[0] u) (timeSpaceCons a x) = (∂[0] v) (timeSpaceCons a x)) :
    ∀ p : ℝ^2, p 0 ∈ Ico a T → u p = v p := by
  exact SmallData.Classical.eq_on_forward_open_strip_of_eq_cauchyData_locallyLipschitz
    (n := 1) hf hu hv huwave hvwave hposition hvelocity

/-- The constructed global wave is unique among all ambient C² solutions of the
same forward PDE with the same initial position and velocity. -/
theorem eq_nonlinearClassicalSolution_of_cauchyData {L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (hf₁ : ContDiff ℝ 1 f) {g h : ℝ →ᵇ ℝ} (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 1 h) {u : ℝ^2 → ℝ} (hu : ContDiff ℝ 2 u)
    (huwave : ∀ p : ℝ^2, 0 ≤ p 0 → waveOperator (n := 1) u p = -f (u p))
    (hposition : ∀ x : ℝ^1, u (timeSpaceCons 0 x) = g (x 0))
    (hvelocity : ∀ x : ℝ^1, (∂[0] u) (timeSpaceCons 0 x) = h (x 0)) :
    ∀ p : ℝ^2, 0 ≤ p 0 → u p = nonlinearClassicalSolution hf g h p := by
  intro p hp
  exact eq_on_forward_strip_of_eq_cauchyData_locallyLipschitz
    hf₁.locallyLipschitz hu (contDiff_two_nonlinearClassicalSolution hf hf₁ hg hh)
    (fun q hq ↦ huwave q hq.1)
    (fun q hq ↦ waveOperator_nonlinearClassicalSolution hf hf₁ hg hh hq.1)
    (fun x ↦ (hposition x).trans (nonlinearClassicalSolution_initial_position hf g h x).symm)
    (fun x ↦ (hvelocity x).trans (nonlinearClassicalSolution_initial_velocity hf hf₁ hg hh x).symm)
    p ⟨hp, le_rfl⟩

end WaveEquation
