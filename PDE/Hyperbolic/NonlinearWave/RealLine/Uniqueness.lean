/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.RealLine.Cauchy
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Uniqueness
public import PDE.Hyperbolic.NonlinearWave.RealLine.Continuation.Localization

/-!
# Uniqueness of the constructed classical wave on the real line

The global wave `nonlinearClassicalSolution` of `u_tt - u_xx = -f(u)` is the only ambient C²
solution of the forward problem with its Cauchy data
(`eq_nonlinearClassicalSolution_of_cauchyData`). Uniqueness is asserted at nonnegative times,
since the negative-time extension of the constructed field is not prescribed by the Cauchy
problem.

The domain-of-dependence and strip uniqueness theorems for a locally Lipschitz reaction hold in
every space dimension and are stated once, in
`PDE.Hyperbolic.NonlinearWave.SmallData.Classical.Uniqueness`; on the real line they are used at
`n = 1`.
-/

@[expose] public noncomputable section

open PDE.Common PDE.Analysis Set
open scoped Topology BoundedContinuousFunction

namespace WaveEquation

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
  exact SmallData.Classical.eq_on_forward_strip_of_eq_cauchyData_locallyLipschitz (n := 1)
    hf₁.locallyLipschitz hu (contDiff_two_nonlinearClassicalSolution hf hf₁ hg hh)
    (fun q hq ↦ huwave q hq.1)
    (fun q hq ↦ waveOperator_nonlinearClassicalSolution hf hf₁ hg hh hq.1)
    (fun x ↦ (hposition x).trans (nonlinearClassicalSolution_initial_position hf g h x).symm)
    (fun x ↦ (hvelocity x).trans (nonlinearClassicalSolution_initial_velocity hf hf₁ hg hh x).symm)
    p ⟨hp, le_rfl⟩

end WaveEquation
