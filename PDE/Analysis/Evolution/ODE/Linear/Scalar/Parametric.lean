/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.ODE.Linear.Scalar
import PDE.Analysis.Integration.Primitive.Parametric

/-!
# Joint smoothness of the scalar integrating-factor solution

If the coefficients `a(t, p)`, `b(t, p)` and the initial value `q₀(p)` are `Cⁿ` on
`ℝ × P` for a normed-space parameter `p`, then `scalarLinearSolution` is jointly
`Cⁿ` in `(t, p)`, for every `n ≤ ∞`. The proof writes the two integrals of the
solution formula as parameter-dependent primitives.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace PDE.Analysis.Evolution

universe u

/-- Smooth parameter-dependent coefficients and initial values give a jointly
smooth scalar solution. Time is the first coordinate. The initial time is fixed,
and the formula applies on either side of it. No sign condition is needed. -/
theorem contDiff_scalarLinearSolution_uncurry
    {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {n : ℕ∞} {a b : ℝ × P → ℝ} {q₀ : P → ℝ}
    (ha : ContDiff ℝ n a) (hb : ContDiff ℝ n b) (hq₀ : ContDiff ℝ n q₀)
    (t₀ : ℝ) :
    ContDiff ℝ n (fun p : ℝ × P ↦
      scalarLinearSolution (fun s ↦ a (s, p.2)) (fun s ↦ b (s, p.2))
        t₀ (q₀ p.2) p.1) := by
  let A : ℝ × P → ℝ := fun p ↦ -backwardPrimitive a t₀ p
  have hA : ContDiff ℝ n A := (contDiff_backwardPrimitive ha t₀).neg
  have hAeq (p : ℝ × P) : A p = ∫ s in t₀..p.1, a (s, p.2) := by
    dsimp only [A, backwardPrimitive]
    rw [intervalIntegral.integral_symm, neg_neg]
  let B : ℝ × P → ℝ := fun p ↦ Real.exp (A p) * b p
  have hB : ContDiff ℝ n B := hA.exp.mul hb
  have hBeq (p : ℝ × P) :
      -backwardPrimitive B t₀ p =
        ∫ v in t₀..p.1, Real.exp (∫ s in t₀..v, a (s, p.2)) * b (v, p.2) := by
    rw [backwardPrimitive, intervalIntegral.integral_symm, neg_neg]
    apply intervalIntegral.integral_congr
    intro v _
    dsimp only [B]
    rw [hAeq]
  have heq :
      (fun p : ℝ × P ↦
        scalarLinearSolution (fun s ↦ a (s, p.2)) (fun s ↦ b (s, p.2))
          t₀ (q₀ p.2) p.1) =
      (fun p : ℝ × P ↦ Real.exp (-A p) *
        (q₀ p.2 - backwardPrimitive B t₀ p)) := by
    funext p
    simp only [scalarLinearSolution, sub_eq_add_neg, hAeq, hBeq]
  rw [heq]
  exact hA.neg.exp.mul ((hq₀.comp contDiff_snd).sub (contDiff_backwardPrimitive hB t₀))

end PDE.Analysis.Evolution
