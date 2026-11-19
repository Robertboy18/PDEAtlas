/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Strauss.Nonexistence
public import PDE.Spaces.Sobolev.Approximation.Density.SmallNorm

/-!
# Small smooth data in the strict Strauss range

The nonexistence theorem applies to a family of initial velocities:
positive multiples of a fixed smooth mollifier. Their support stays in the ball
of radius two, and their norm can be arbitrarily small in any prescribed
integer-order `L²` Sobolev space.

This excludes a global classical solution with the stated forward support.
Constructing a local solution and identifying its maximal lifespan are separate
steps; neither is a hypothesis hidden in the choice of data.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Common Set SobolevSpace.GraphSpace TopologicalSpace
open scoped Distributions Sobolev

namespace WaveEquation.SmallData

/-- For every Sobolev order and positive size bound, some nonnegative smooth
compactly supported velocity data admit no global forward-supported classical
wave with zero displacement when `1 < p < 1 + √2`. -/
theorem exists_small_data_not_global_cauchy_solution_three (k : ℕ) {p ε : ℝ} (hp : 1 < p)
    (hcrit : p < 1 + Real.sqrt 2) (hε : 0 < ε) :
    ∃ h : 𝓓((⊤ : Opens (ℝ^3)), ℝ),
      (∀ x, 0 ≤ h x) ∧
      (∀ x, 2 ≤ ‖x‖ → h x = 0) ∧
      0 < ∫ x, h x ∧
      ‖globalTestFunctionToWkpOn (k := k) (p := 2) (Ω := univ) h‖ < ε ∧
      ¬∃ u : ℝ^4 → ℝ,
        ContDiff ℝ 2 u ∧ HasForwardSupport u 2 ∧
        (∀ t, 0 < t → ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) =
          |u (timeSpaceCons t x)| ^ p) ∧
        (∀ x : ℝ^3, u (timeSpaceCons 0 x) = 0) ∧
        (∀ x : ℝ^3, (∂[0] u) (timeSpaceCons 0 x) = h x) := by
  obtain ⟨h, hhn, hsupport, hpositive, hnorm⟩ := exists_nonneg_testFunction_sobolevNorm_lt 3 k 2 hε
  refine ⟨h, hhn, hsupport, hpositive, hnorm, ?_⟩
  rintro ⟨u, hu, hs, hwave, hzero, hinitial⟩
  exact not_global_cauchy_solution_three_of_lt_strauss hu hs
    contDiff_const (h.contDiff.of_le (by simp)) (by norm_num)
    hp hcrit hwave hzero hinitial (by simp) hpositive

end WaveEquation.SmallData
