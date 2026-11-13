/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.RealLine.Cauchy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import CAS.IntegrationTactic

/-!
# Nonlinear classical waves from bounded scalar data

The theorem `exists_global_classical_solution_of_bounded_data` gives a global `C²`
solution of `□u = -(1 + sin u)`, whose reaction does not vanish at zero, with the
bounded smooth data `sin(x²)` and `cos(x²)` (`exists_shifted_sine_wave`). For a constant
reaction `c` and zero data the constructed solution `nonlinearClassicalSolution` is
`-c t²/2` (`nonlinearClassicalSolution_constant`), so it grows quadratically in time.
-/

@[expose] public noncomputable section

open PDE.Common WaveEquation Set Filter
open scoped Topology BoundedContinuousFunction

namespace PDE.Examples.NonlinearClassicalWave

/-- There is a global `C²` solution of `□u = -(1 + sin u)` with data `sin(x²)` and
`cos(x²)`, attaining them as limits and bounded on every strip `0 ≤ t ≤ T`. -/
theorem exists_shifted_sine_wave :
    ∃ u : ℝ^2 → ℝ, ContDiff ℝ 2 u ∧
      (∀ p : ℝ^2, 0 ≤ p 0 → waveOperator u p = -(1 + Real.sin (u p))) ∧
      (∀ x : ℝ^1, u (timeSpaceCons 0 x) = Real.sin ((x 0) ^ 2)) ∧
      (∀ x : ℝ^1, (∂[0] u) (timeSpaceCons 0 x) = Real.cos ((x 0) ^ 2)) ∧
      (∀ x : ℝ^1, Tendsto u
        (𝓝 (timeSpaceCons 0 x)) (𝓝 (Real.sin ((x 0) ^ 2)))) ∧
      (∀ x : ℝ^1, Tendsto (∂[0] u)
        (𝓝 (timeSpaceCons 0 x)) (𝓝 (Real.cos ((x 0) ^ 2)))) ∧
      (∀ T : NNReal, ∃ C : ℝ, ∀ p : ℝ^2, p 0 ∈ Icc (0 : ℝ) (T : ℝ) → ‖u p‖ ≤ C) := by
  have hf : LipschitzWith 1 (fun s : ℝ ↦ 1 + Real.sin s) :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      simpa only [dist_add_left] using Real.lipschitzWith_sin.dist_le_mul x y
  apply exists_global_classical_solution_of_bounded_data hf
    (contDiff_const.add Real.contDiff_sin)
    (Real.contDiff_sin.comp (contDiff_id.pow 2))
    (Real.contDiff_cos.comp (contDiff_id.pow 2))
  · refine isBounded_iff_forall_norm_le.mpr ⟨1, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact Real.abs_sin_le_one _
  · refine isBounded_iff_forall_norm_le.mpr ⟨1, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact Real.abs_cos_le_one _

/-- The d'Alembert–Duhamel integral of the constant `c` is `c t²/2`. -/
theorem duhamel_constant (c : ℝ) (p : ℝ^2) :
    dAlembertDuhamelSolution (fun _ ↦ c) p = c * (p 0) ^ 2 / 2 := by
  rw [dAlembertDuhamelSolution_eq_doubleIntegral]
  simp only [dAlembertFormula, add_zero, mul_zero, zero_add,
    intervalIntegral.integral_const, smul_eq_mul]
  cas

/-- For the constant reaction `c` and zero data the constructed global solution is
`-c t²/2` for `t ≥ 0`. -/
theorem nonlinearClassicalSolution_constant (c : ℝ) {p : ℝ^2} (hp : 0 ≤ p 0) :
    nonlinearClassicalSolution (LipschitzWith.const c) 0 0 p = -c * (p 0) ^ 2 / 2 := by
  let T : NNReal := ⟨p 0, hp⟩
  rw [nonlinearClassicalSolution_eq_on_strip (LipschitzWith.const c) 0 0
    (T := T) ⟨hp, le_rfl⟩]
  simp only [classicalStripExtension, BoundedContinuousFunction.coe_zero, Pi.zero_apply,
    dAlembertFormula, add_zero, mul_zero, intervalIntegral.integral_zero,
    duhamel_constant, zero_sub]
  cas

end PDE.Examples.NonlinearClassicalWave
