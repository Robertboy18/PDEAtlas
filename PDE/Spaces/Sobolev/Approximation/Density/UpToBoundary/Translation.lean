/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Approximation.Mollification.LpApproximation
public import PDE.Spaces.Sobolev.Compactness.Rellich.Translation
import PDE.Spaces.Sobolev.Approximation.VectorValued.Density.UpToBoundary.Translation

/-!
# Translated mollification in finite `Lᵖ`

Mollification followed by a translation tending to zero still converges in `Lᵖ`.
This is the analytic step in Evans §5.3.3: the translation makes room for the
mollifier near the boundary. Classical coordinate derivatives commute with translation
at every order, without differentiating a boundary chart.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.3.3, Theorem 3, pp. 266-268, for approximation by
  functions smooth up to a C¹ boundary.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (partialDeriv iteratedPartialDeriv)

open MeasureTheory Filter
open scoped ENNReal Topology

namespace SobolevSpace.Approximation.UpToBoundary

open GraphSpace.Rellich

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Translation commutes with any finite word of coordinate derivatives. -/
theorem iteratedPartialDeriv_comp_add
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (α : List (Fin n)) (f : ℝ^n → F)
    (a x : ℝ^n) :
    iteratedPartialDeriv α (fun y ↦ f (y + a)) x =
      iteratedPartialDeriv α f (x + a) := by
  induction α generalizing x with
  | nil => rfl
  | cons i α ih =>
    simp only [iteratedPartialDeriv, funext ih, partialDeriv, fderiv_comp_add_right]

/-- Mollification preserves membership in every finite `Lᵖ` space. -/
theorem memLp_mollify (μ : Mollifier n) {ε : ℝ} (hε : 0 < ε) (hp : p ≠ ∞)
    {f : ℝ^n → ℝ} (hf : MemLp f p volume) :
    MemLp (mollify μ ε f) p volume :=
  (MollifyLp.eLpNorm_mollify_le μ hε hp hf).trans_lt hf.eLpNorm_lt_top

/-- If the scale and the translation tend to zero, translated mollification converges
in `Lᵖ`. The original function need not have any weak derivatives. -/
theorem mollify_translate_converges_Lp (μ : Mollifier n) (hp : p ≠ ∞)
    {f : ℝ^n → ℝ} (hf : MemLp f p volume)
    (ε : ℕ → ℝ) (hε : ∀ m, 0 < ε m) (hε0 : Tendsto ε atTop (𝓝 0))
    (a : ℕ → ℝ^n) (ha : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun m ↦ eLpNorm (fun x ↦ mollify μ (ε m) f (x + a m) - f x)
      p volume) atTop (𝓝 0) := by
  simpa only [mollifyVector_real] using
    VectorValued.UpToBoundary.mollifyVector_translate_converges_Lp μ hp hf ε hε hε0 a ha

end SobolevSpace.Approximation.UpToBoundary
