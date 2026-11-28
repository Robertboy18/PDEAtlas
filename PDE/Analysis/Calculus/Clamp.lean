/-
Authors: Levent Alpöge, Tristan Buckmaster

The lemmas of this file come from modules of the Lean package of the paper
"Finite-time blow-up for the Navier–Stokes equations"
(https://github.com/tristanbuckmaster/navier-stokes, folder lean/, commit ad53419),
where they were steps of longer proofs. They were included in BlowupZoo
(https://github.com/lean-dojo/BlowupZoo, folder AtlasCandidates/) with the permission of the
authors (20 November 2026) and moved here from there; the file NOTICE of this repository records it.
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PDE.Analysis.Scalar.Definitions

set_option linter.style.header false

/-!
# The clamp to the interval `[-1, 1]` and functions composed with it

The clamp `PDE.Analysis.clampUnit` does not increase distances, so it is Lipschitz with the constant
one. A function composed with it is Lipschitz when the function is of class `C²` or a polynomial,
and inside `(-1, 1)` it has the derivative of the function itself, because the clamp is the identity
there. The Lipschitz bounds come from the fact that a continuously differentiable function is
Lipschitz on a compact interval.

## Main results

* `PDE.Analysis.deriv_comp_clampUnit`: For `x` in `(-1, 1)`, the derivative of `y ↦ u (clampUnit y)`
  at `x` is `deriv u x`.
* `PDE.Analysis.exists_lipschitzWith_comp_clampUnit`: For `u : ℝ → ℝ` of class `C²`, the function
  `x ↦ u (clampUnit x)` is Lipschitz on `ℝ`.
* `PDE.Analysis.exists_lipschitzWith_eval_clampUnit`: For a real polynomial `P`, the function
  `x ↦ P.eval (clampUnit x)` is Lipschitz on `ℝ`.
* `PDE.Analysis.integral_deriv_eval_clampUnit_sq`: For a real polynomial `P`, the integral over
  `[-1, 1]` of the square of the derivative of `y ↦ P.eval (clampUnit y)` is the integral of the
  square of the derivative of `P`.
* `PDE.Analysis.deriv_eval_clampUnit`: For a real polynomial `P` and `x` in `(-1, 1)`, the
  derivative of `y ↦ P.eval (clampUnit y)` at `x` is the derivative of `P` at `x`. A case of
  `PDE.Analysis.deriv_comp_clampUnit`.
* `PDE.Analysis.dist_clampUnit_le`: The clamp does not increase distances:
  `dist (clampUnit x) (clampUnit y) ≤ dist x y`. This is `PDE.Analysis.lipschitzWith_clampUnit` in
  terms of distances.
* `PDE.Analysis.lipschitzWith_clampUnit`: The clamp `clampUnit` to `[-1, 1]` is Lipschitz with the
  constant one.

## References

* Levent Alpöge and Tristan Buckmaster, the Lean package of the paper "Finite-time blow-up for the
  Navier–Stokes equations", <https://github.com/tristanbuckmaster/navier-stokes>, folder `lean/`,
  commit `ad53419`: the lemmas of this module and their proofs, adapted to this library. See
  `NOTICE` for attribution and permission.
-/

@[expose] public section

noncomputable section

open MeasureTheory Polynomial

namespace PDE.Analysis

/-- For `x` in `(-1, 1)`, the derivative of `y ↦ u (clampUnit y)` at `x` is `deriv u x`. -/
theorem deriv_comp_clampUnit (u : ℝ → ℝ) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (fun y ↦ u (clampUnit y)) x = deriv u x := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  rw [clampUnit_eq_self (Set.Ioo_subset_Icc_self hy)]

/-- For a real polynomial `P` and `x` in `(-1, 1)`, the derivative of `y ↦ P.eval (clampUnit y)` at
`x` is the derivative of `P` at `x`. A case of `PDE.Analysis.deriv_comp_clampUnit`. -/
theorem deriv_eval_clampUnit (P : ℝ[X]) {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    deriv (fun y ↦ P.eval (clampUnit y)) x = (derivative P).eval x := by
  rw [deriv_comp_clampUnit (fun y ↦ P.eval y) hx, Polynomial.deriv]

/-- The clamp `clampUnit` to `[-1, 1]` is Lipschitz with the constant one. -/
theorem lipschitzWith_clampUnit : LipschitzWith 1 clampUnit :=
  (LipschitzWith.id.const_min 1).const_max (-1)

/-- The clamp does not increase distances: `dist (clampUnit x) (clampUnit y) ≤ dist x y`. This is
`PDE.Analysis.lipschitzWith_clampUnit` in terms of distances. -/
theorem dist_clampUnit_le (x y : ℝ) : dist (clampUnit x) (clampUnit y) ≤ dist x y := by
  simpa using lipschitzWith_clampUnit.dist_le_mul x y

/-- For `u : ℝ → ℝ` of class `C²`, the function `x ↦ u (clampUnit x)` is Lipschitz on `ℝ`. -/
theorem exists_lipschitzWith_comp_clampUnit (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u) :
    ∃ K, LipschitzWith K (fun x ↦ u (clampUnit x)) := by
  obtain ⟨K, hK⟩ := (hu.contDiffOn (s := Set.Icc (-1 : ℝ) 1)).exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc
  refine ⟨K, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  exact (hK.dist_le_mul _ (clampUnit_mem_Icc x) _ (clampUnit_mem_Icc y)).trans
    (mul_le_mul_of_nonneg_left (dist_clampUnit_le x y) K.2)

/-- For a real polynomial `P`, the function `x ↦ P.eval (clampUnit x)` is Lipschitz on `ℝ`. -/
theorem exists_lipschitzWith_eval_clampUnit (P : ℝ[X]) : ∃ K, LipschitzWith K
    (fun x ↦ P.eval (clampUnit x)) := by
  have hc : ContDiff ℝ 1 (fun x : ℝ ↦ P.eval x) := by
    simpa using P.contDiff_aeval (𝕜 := ℝ) 1
  obtain ⟨K, hK⟩ := hc.contDiffOn.exists_lipschitzOnWith (s := Set.Icc (-1 : ℝ) 1)
    one_ne_zero (convex_Icc _ _) isCompact_Icc
  refine ⟨K, LipschitzWith.of_dist_le_mul fun x y ↦ ?_⟩
  calc dist (P.eval (clampUnit x)) (P.eval (clampUnit y)) ≤ K * dist (clampUnit x) (clampUnit y) :=
        hK.dist_le_mul _ (clampUnit_mem_Icc x) _ (clampUnit_mem_Icc y)
    _ ≤ K * dist x y := by
        gcongr
        simpa using lipschitzWith_clampUnit.dist_le_mul x y

/-- For a real polynomial `P`, the integral over `[-1, 1]` of the square of the derivative of
`y ↦ P.eval (clampUnit y)` is the integral of the square of the derivative of `P`. -/
theorem integral_deriv_eval_clampUnit_sq (P : ℝ[X]) :
    (∫ x in (-1 : ℝ)..1, deriv (fun y ↦ P.eval (clampUnit y)) x ^ 2)
      = ∫ x in (-1 : ℝ)..1, (derivative P).eval x ^ 2 := by
  apply intervalIntegral.integral_congr_ae
  have h1 : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 1 := by
    rw [ae_iff]
    simp
  filter_upwards [h1] with x hx hmem
  rw [Set.uIoc_of_le (by norm_num)] at hmem
  rw [deriv_eval_clampUnit P ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩]

end PDE.Analysis
