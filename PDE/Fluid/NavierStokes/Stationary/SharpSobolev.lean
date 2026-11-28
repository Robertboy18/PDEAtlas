/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import PDE.Fluid.NavierStokes.Stationary.Exhaustion
public import PDE.Spaces.Sobolev.Inequalities.Sobolev.Sharp.ThreeDimensional

/-!
# The sharp Sobolev inequality with the gradient norm of the stationary Navier–Stokes spaces

The stationary Navier–Stokes modules measure the gradient of a scalar field `u ∈ H¹(ℝⁿ)` with
`‖scalarGradientCLM u‖`, the norm of the list of its weak partial derivatives in a Hilbert
product. This norm is the `L²` norm of the weak gradient `wkpGradientCLM u`, so every bound for
one is a bound for the other. In particular the sharp Sobolev inequality `‖u‖₆ ≤ K_s ‖∇u‖₂` on
`H¹(ℝ³)`, with `K_s = 2^{2/3} / (√3 π^{2/3})`, holds with this norm. That `K_s` is the best
constant is not proved.

## Main results

* `NavierStokes.Stationary.norm_scalarGradientCLM_eq` (all `u` in `H¹(ℝⁿ)`, all `n`):
  `‖scalarGradientCLM u‖ = ‖wkpGradientCLM u‖`.
* `NavierStokes.Stationary.norm_scalarGradientCLM_le` (all `u` in `H¹(ℝⁿ)`, all `n`):
  `‖scalarGradientCLM u‖ ≤ ‖u‖_{H¹}`; `norm_gradientCLM_le` is the same bound for vector fields.
* `SobolevSpace.Inequalities.toReal_eLpNorm_six_le_sharp` (all `u` in `H¹(ℝ³)`):
  `‖u‖₆ ≤ K_s ‖scalarGradientCLM u‖`.

## How it works

`scalarGradientCLM u` lists the weak partial derivatives of `u` in a Hilbert product, and
`wkpGradientCLM u` is the same list as one square-integrable vector field. Both squared norms are
`∑ⱼ ‖∂ⱼu‖₂²` (`norm_scalarGradientCLM_sq`, `norm_wkpGradientCLM_sq_eq_sum_deriv_sq`). The other
two results are `norm_wkpGradientCLM_apply_le` and
`SobolevSpace.Inequalities.toReal_eLpNorm_six_le_mul_norm_wkpGradientCLM` with the gradient norm
rewritten. In dimension `n ≥ 3` the same rewriting turns
`SobolevSpace.Inequalities.toReal_eLpNorm_le_sharpSobolevConstant_mul_norm_wkpGradientCLM` into
the inequality with `‖scalarGradientCLM u‖`.

## References

* G. Talenti, "Best constant in Sobolev inequality", *Ann. Mat. Pura Appl.* 110 (1976), 353-372:
  the inequality, with the constant in formula (2). <https://doi.org/10.1007/BF02418013>
* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Appendix A, Lemma 6 and its
  proof, where the inequality is quoted from Talenti. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace
open scoped ENNReal Sobolev Real

namespace NavierStokes.Stationary

/-- The gradient norm of a scalar field of `H¹(ℝⁿ)` in the Hilbert product of its partial
derivatives is the `L²` norm of its weak gradient: both squares are `∑ⱼ ‖∂ⱼu‖₂²`. -/
theorem norm_scalarGradientCLM_eq {n : ℕ} (u : H¹(ℝ^n)) :
    ‖scalarGradientCLM u‖ = ‖wkpGradientCLM u‖ := by
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [norm_scalarGradientCLM_sq, norm_wkpGradientCLM_sq_eq_sum_deriv_sq]
  rfl

/-- The gradient norm of a scalar field of `H¹(ℝⁿ)` is at most its `H¹` norm. -/
theorem norm_scalarGradientCLM_le {n : ℕ} (u : H¹(ℝ^n)) : ‖scalarGradientCLM u‖ ≤ ‖u‖ :=
  (norm_scalarGradientCLM_eq u).trans_le (norm_wkpGradientCLM_apply_le u)

end NavierStokes.Stationary

namespace SobolevSpace.Inequalities

/-- **The sharp Sobolev inequality on `H¹(ℝ³)`** (Aubin, Talenti), with the gradient norm of
the stationary Navier–Stokes spaces: every `u` in `H¹(ℝ³)` satisfies `‖u‖₆ ≤ K_s ‖∇u‖₂` with
`K_s = 2^{2/3} / (√3 π^{2/3})`. The left side is the `L⁶` norm of the representative of `u`,
which is finite by `memLp_pStar_H1`, and `‖scalarGradientCLM u‖² = ∑ⱼ ‖∂ⱼu‖₂²`.

This is the inequality that Hou, Wang and Yang quote from Talenti in the proof of their
Lemma 6. It is `toReal_eLpNorm_six_le_mul_norm_wkpGradientCLM` with the gradient norm rewritten.
That `K_s` is the smallest constant is not proved. -/
theorem toReal_eLpNorm_six_le_sharp (u : H¹(ℝ^3)) :
    (eLpNorm (baseRepresentative u) 6 volume).toReal ≤
      2 ^ (2 / 3 : ℝ) / (√3 * π ^ (2 / 3 : ℝ)) *
        ‖NavierStokes.Stationary.scalarGradientCLM u‖ := by
  rw [NavierStokes.Stationary.norm_scalarGradientCLM_eq]
  exact toReal_eLpNorm_six_le_mul_norm_wkpGradientCLM u

end SobolevSpace.Inequalities
