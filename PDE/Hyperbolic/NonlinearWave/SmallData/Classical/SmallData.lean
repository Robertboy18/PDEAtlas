/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.SmallData
public import PDE.Spaces.Sobolev.Approximation.Density.SmallNorm
import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.Exponent

/-!
# Small smooth data with a finite classical lifespan

A positive multiple of a fixed mollifier gives the initial velocity. We can
make its norm as small as we like in any prescribed integer-order Sobolev space
while keeping its support fixed and its integral positive.

For the quadratic focusing wave in three dimensions, local existence and the
finite existence horizon are both proved. Together they give a maximal
classical solution for these data. The conclusion is failure of classical
continuation at a finite time; a statement about a diverging solution norm
requires a separate continuation criterion. The theorem is the exponent `p = 2` of
`LocalPower.exists_small_data_finite_maximalSolution_abs_rpow_three`.
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace.GraphSpace TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace WaveEquation.SmallData.Classical

/-- Arbitrarily small smooth compact velocities in any prescribed `W^{k,q}`
space give a quadratic focusing wave with a positive finite maximal classical
lifespan in three dimensions. The initial displacement is zero. Both the data
and the solution are constructed. -/
theorem exists_small_data_finite_maximalSolution_quadratic_three
    (k : ℕ) (q : ℝ≥0∞) [Fact (1 ≤ q)] {ε : ℝ} (hε : 0 < ε) :
    ∃ h : 𝓓((⊤ : Opens (ℝ^3)), ℝ),
      (∀ x, 0 ≤ h x) ∧
      (∀ x, 2 ≤ ‖x‖ → h x = 0) ∧
      0 < ∫ x, h x ∧
      ‖globalTestFunctionToWkpOn (k := k) (p := q) (Ω := univ) h‖ < ε ∧
      ∃ T : ℝ, ∃ u : ℝ^4 → ℝ,
        IsMaximalSolutionBefore (fun z ↦ -|z| ^ (2 : ℝ)) (fun _ ↦ 0) h T u :=
  LocalPower.exists_small_data_finite_maximalSolution_abs_rpow_three le_rfl
    two_lt_one_add_sqrt_two k q hε

end WaveEquation.SmallData.Classical
