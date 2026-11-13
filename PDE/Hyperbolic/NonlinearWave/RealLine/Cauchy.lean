/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.RealLine.Global

/-!
# The bounded-data classical nonlinear wave Cauchy problem

A C¹ globally Lipschitz reaction admits a global forward classical solution from
bounded C² displacement and bounded C¹ velocity. The endpoint uses ordinary scalar
data and bounded-range hypotheses, without integrability or bounds on derivatives.
Both initial values are attained and are joint spacetime limits.

The solution is the fixed point of `u = u⁰ - D[f(u)]`, where `u⁰` is d'Alembert's solution (8)
of Evans, §2.4.1(a), with data `g` and `h`, and `D[F]` is the Duhamel solution (43) of
Example (i) in §2.4.2, with right-hand side `F`. The data have the regularity of §2.4.1(a),
Theorem 1, `g ∈ C²` and `h ∈ C¹`, and are bounded. By
`existsUnique_nonlinearStrip_of_boundedContinuousData_anyTime`, the fixed point is unique on
every strip `ℝ × [0, T]`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1(a), equation (8) and Theorem 1;
  §2.4.2, Example (i), equation (43).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE.Common PDE.Analysis Set Filter Function
open scoped Topology BoundedContinuousFunction

namespace WaveEquation

/-- The global field remains bounded on every finite forward spacetime strip.
The bound may depend on the horizon. -/
theorem nonlinearClassicalSolution_bounded_on_strip {L : NNReal} {f : ℝ → ℝ}
    (hf : LipschitzWith L f) (g h : ℝ →ᵇ ℝ) (T : NNReal) :
    ∃ C : ℝ, ∀ p : ℝ^2, p 0 ∈ Icc (0 : ℝ) (T : ℝ) → ‖nonlinearClassicalSolution hf g h p‖ ≤ C := by
  refine ⟨‖nonlinearStripSolution hf g h T‖, fun p hp ↦ ?_⟩
  rw [nonlinearClassicalSolution_eq_on_strip hf g h hp,
    classicalStripExtension_eq_on_strip hf g h hp]
  exact (nonlinearStripSolution hf g h T).norm_coe_le_norm _

/-- Bounded `C²` displacement and bounded `C¹` velocity produce a global forward
classical solution for a `C¹`, globally Lipschitz reaction. The solution has a `C²` extension across
time zero; the PDE is asserted for nonnegative time. Both assigned initial values are also joint
spacetime limits. -/
theorem exists_global_classical_solution_of_bounded_data {f g h : ℝ → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (hf₁ : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h)
    (hgb : Bornology.IsBounded (range g)) (hhb : Bornology.IsBounded (range h)) :
    ∃ u : ℝ^2 → ℝ, ContDiff ℝ 2 u ∧
      (∀ p : ℝ^2, 0 ≤ p 0 → waveOperator (n := 1) u p = -f (u p)) ∧
      (∀ x : ℝ^1, u (timeSpaceCons 0 x) = g (x 0)) ∧
      (∀ x : ℝ^1, (∂[0] u) (timeSpaceCons 0 x) = h (x 0)) ∧
      (∀ x : ℝ^1, Tendsto u (𝓝 (timeSpaceCons 0 x)) (𝓝 (g (x 0)))) ∧
      (∀ x : ℝ^1, Tendsto (∂[0] u) (𝓝 (timeSpaceCons 0 x)) (𝓝 (h (x 0)))) ∧
      (∀ T : NNReal, ∃ C : ℝ, ∀ p : ℝ^2, p 0 ∈ Icc (0 : ℝ) (T : ℝ) → ‖u p‖ ≤ C) := by
  let G : ℝ →ᵇ ℝ := ⟨⟨g, hg.continuous⟩, Metric.isBounded_range_iff.mp hgb⟩
  let H : ℝ →ᵇ ℝ := ⟨⟨h, hh.continuous⟩, Metric.isBounded_range_iff.mp hhb⟩
  refine ⟨nonlinearClassicalSolution hf G H,
    contDiff_two_nonlinearClassicalSolution hf hf₁ hg hh, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ hp ↦ waveOperator_nonlinearClassicalSolution hf hf₁ hg hh hp
  · exact nonlinearClassicalSolution_initial_position hf G H
  · exact nonlinearClassicalSolution_initial_velocity hf hf₁ hg hh
  · exact tendsto_nonlinearClassicalSolution_initial hf hf₁ hg hh
  · exact tendsto_partialDeriv_nonlinearClassicalSolution_initial hf hf₁ hg hh
  · exact nonlinearClassicalSolution_bounded_on_strip hf G H

end WaveEquation
