/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Cutoffs between two balls and Lipschitz products

`IsBallCutoff ζ ρ₂ ρ₃`: `ζ` is continuous, Lipschitz, takes values in `[0, 1]`, equals `1` on the
closed ball of radius `ρ₂` and vanishes outside the open ball of radius `ρ₃`; a smooth one exists
for `0 < ρ₂ < ρ₃` (`exists_isBallCutoff`, a smooth bump function). The product `ζ w` of such a
cutoff with a Lipschitz map `w` bounded on the ball of radius `ρ₃` is Lipschitz
(`lipschitzWith_smul_of_eq_zero`).

## Main results

* `PDE.Analysis.IsBallCutoff`, `PDE.Analysis.exists_isBallCutoff`.
* `PDE.Analysis.lipschitzWith_smul_of_eq_zero`.
-/

@[expose] public noncomputable section

open Set
open scoped NNReal

namespace PDE.Analysis

set_option linter.missingDocs true

/-! ### Cutoffs and Lipschitz products -/

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A cutoff between two balls: a continuous Lipschitz function with values in `[0, 1]`, equal to
`1` on the closed ball of radius `ρ₂` and to `0` outside the open ball of radius `ρ₃`. -/
structure IsBallCutoff (ζ : E → ℝ) (ρ₂ ρ₃ : ℝ) : Prop where
  /-- Continuity. -/
  continuous : Continuous ζ
  /-- A Lipschitz bound. -/
  lipschitz : ∃ K : ℝ≥0, LipschitzWith K ζ
  /-- Nonnegativity. -/
  nonneg : ∀ y, 0 ≤ ζ y
  /-- The bound by `1`. -/
  le_one : ∀ y, ζ y ≤ 1
  /-- `ζ = 1` on the closed ball of radius `ρ₂`. -/
  eq_one : ∀ y, ‖y‖ ≤ ρ₂ → ζ y = 1
  /-- `ζ = 0` outside the open ball of radius `ρ₃`. -/
  eq_zero : ∀ y, ρ₃ ≤ ‖y‖ → ζ y = 0

open scoped ContDiff in
/-- **Smooth cutoffs between two balls exist** in a finite dimensional inner product space, for
`0 < ρ₂ < ρ₃`: a smooth bump function. -/
theorem exists_isBallCutoff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {ρ₂ ρ₃ : ℝ} (h₂ : 0 < ρ₂) (h₂₃ : ρ₂ < ρ₃) :
    ∃ ζ : E → ℝ, IsBallCutoff ζ ρ₂ ρ₃ ∧ ContDiff ℝ ∞ ζ := by
  let f : ContDiffBump (0 : E) := ⟨ρ₂, ρ₃, h₂, h₂₃⟩
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (𝕂 := ℝ) (n := 1)
    f.hasCompactSupport f.contDiff one_ne_zero
  refine ⟨f, ⟨f.continuous, ⟨K, hK⟩, fun y ↦ f.nonneg, fun y ↦ f.le_one, fun y hy ↦ ?_,
    fun y hy ↦ ?_⟩, f.contDiff⟩
  · exact f.one_of_mem_closedBall (by simpa using hy)
  · exact f.zero_of_le_dist (by simpa using hy)

/-- **Lipschitz products with a cutoff.** If `ζ` is `K_ζ`-Lipschitz with `|ζ| ≤ 1` and vanishes
outside the ball of radius `R`, and `w` is `K_w`-Lipschitz and bounded by `B ≥ 0` on that ball,
then `ζ w` is Lipschitz with the constant `K_ζ B + K_w`. -/
theorem lipschitzWith_smul_of_eq_zero {ζ : E → ℝ} {w : E → F} {Kζ Kw : ℝ≥0} {R B : ℝ}
    (hζ : LipschitzWith Kζ ζ) (hζ1 : ∀ y, |ζ y| ≤ 1) (hζR : ∀ y, R ≤ ‖y‖ → ζ y = 0)
    (hw : LipschitzWith Kw w) (hB : ∀ y, ‖y‖ < R → ‖w y‖ ≤ B) (hB0 : 0 ≤ B) :
    LipschitzWith (Real.toNNReal (Kζ * B + Kw)) (fun y ↦ ζ y • w y) := by
  have key : ∀ y y' : E, ‖y‖ < R →
      dist (ζ y • w y) (ζ y' • w y') ≤ (Kζ * B + Kw) * dist y y' := by
    intro y y' hy
    have h1 : ζ y • w y - ζ y' • w y' = (ζ y - ζ y') • w y + ζ y' • (w y - w y') := by
      rw [sub_smul, smul_sub]
      abel
    rw [dist_eq_norm, h1]
    have hζd : |ζ y - ζ y'| ≤ Kζ * dist y y' := by
      rw [← Real.dist_eq]
      exact hζ.dist_le_mul y y'
    have hwd : ‖w y - w y'‖ ≤ Kw * dist y y' := by
      rw [← dist_eq_norm]
      exact hw.dist_le_mul y y'
    calc ‖(ζ y - ζ y') • w y + ζ y' • (w y - w y')‖
        ≤ |ζ y - ζ y'| * ‖w y‖ + |ζ y'| * ‖w y - w y'‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (Kζ * dist y y') * B + 1 * (Kw * dist y y') := by
          gcongr
          · exact hB y hy
          · exact hζ1 y'
      _ = (Kζ * B + Kw) * dist y y' := by ring
  refine LipschitzWith.of_dist_le' fun y y' ↦ ?_
  by_cases hy : ‖y‖ < R
  · exact key y y' hy
  by_cases hy' : ‖y'‖ < R
  · rw [dist_comm, dist_comm y]
    exact key y' y hy'
  · rw [not_lt] at hy hy'
    rw [hζR y hy, hζR y' hy', zero_smul, zero_smul, dist_self]
    positivity

end General

end PDE.Analysis
