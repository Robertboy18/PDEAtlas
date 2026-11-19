/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Classical

/-!
# Classical initial values in the wave compatibility recurrence

The initial time derivatives of a wave are computed by
`q₀ = g`, `q₁ = h`, and `qⱼ₊₂ = fⱼ - L qⱼ`. Here `fⱼ` denotes the canonical
initial trace of the corresponding forcing derivative. Every finite spatial
Sobolev realization of these classical values satisfies the same recurrence
with the full higher load, including all drift and potential terms.

Smoothness alone supplies the Sobolev realizations. Zero boundary values are
the separate compatibility requirement; they play no role in this algebra.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace Hyperbolic.HigherRegularity

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Formal initial time derivatives, computed from the initial position,
velocity, forcing traces and full spatial operator. -/
def classicalWaveInitialValue (P : SmoothFullCoefficients n Ω)
    (f : ℕ → ℝ^n → ℝ) (g h : ℝ^n → ℝ) : ℕ → ℝ^n → ℝ
  | 0 => g
  | 1 => h
  | j + 2 => fun x ↦ f j x - P.classicalLoad (classicalWaveInitialValue P f g h j) x

/-- Every computed initial value is smooth up to the spatial boundary when
the coefficients, initial data and forcing traces are smooth. -/
theorem classicalWaveInitialValue_regular (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) {f : ℕ → ℝ^n → ℝ} {g h : ℝ^n → ℝ}
    (hf : ∀ j r, ContDiffUpToBoundary r (f j) Ω) (hg : ∀ r, ContDiffUpToBoundary r g Ω)
    (hh : ∀ r, ContDiffUpToBoundary r h Ω) (j r : ℕ) :
    ContDiffUpToBoundary r (classicalWaveInitialValue P f g h j) Ω := by
  induction j using Nat.twoStepInduction generalizing r with
  | zero => exact hg r
  | one => exact hh r
  | more j ih _ =>
      exact (hf j r).sub (P.classicalLoad_regular hopen hbounded (ih (r + 2))) hopen

/-- The canonical Sobolev realization of a computed classical initial value. -/
def classicalWaveInitialSobolevValue (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {f : ℕ → ℝ^n → ℝ} {g h : ℝ^n → ℝ}
    (hf : ∀ j r, ContDiffUpToBoundary r (f j) Ω)
    (hg : ∀ r, ContDiffUpToBoundary r g Ω)
    (hh : ∀ r, ContDiffUpToBoundary r h Ω) (r j : ℕ) : W^{r,2}(Ω) :=
  (classicalWaveInitialValue_regular P hopen hbounded hf hg hh j r).toWkpSpaceOn
    hopen hbounded 2

/-- Spatial restriction does not change the computed initial data. -/
theorem lowerOrder_classicalWaveInitialSobolevValue (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) {f : ℕ → ℝ^n → ℝ} {g h : ℝ^n → ℝ}
    (hf : ∀ j r, ContDiffUpToBoundary r (f j) Ω) (hg : ∀ r, ContDiffUpToBoundary r g Ω)
    (hh : ∀ r, ContDiffUpToBoundary r h Ω) {r s : ℕ} (hsr : s ≤ r) (j : ℕ) :
    lowerOrderCLM hsr (classicalWaveInitialSobolevValue P hopen hbounded hf hg hh r j) =
      classicalWaveInitialSobolevValue P hopen hbounded hf hg hh s j := by
  unfold classicalWaveInitialSobolevValue
  exact ContDiffUpToBoundary.lowerOrder_toWkpSpaceOn _ hopen hbounded 2 hsr

/-- The classical recurrence realizes the full higher Sobolev load.
This equality includes every weak derivative coordinate of the initial data. -/
theorem classicalWaveInitialSobolevValue_add_two (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) {f : ℕ → ℝ^n → ℝ} {g h : ℝ^n → ℝ}
    (hf : ∀ j r, ContDiffUpToBoundary r (f j) Ω) (hg : ∀ r, ContDiffUpToBoundary r g Ω)
    (hh : ∀ r, ContDiffUpToBoundary r h Ω) (r j : ℕ) :
    classicalWaveInitialSobolevValue P hopen hbounded hf hg hh r (j + 2) =
      (hf j r).toWkpSpaceOn hopen hbounded 2 - P.load hopen hbounded r
      (classicalWaveInitialSobolevValue P hopen hbounded hf hg hh (r + 2) j) := by
  unfold classicalWaveInitialSobolevValue
  rw [P.load_toWkpSpaceOn, sub_eq_add_neg, ← ContDiffUpToBoundary.toWkpSpaceOn_neg,
    ← ContDiffUpToBoundary.toWkpSpaceOn_add]
  congr 1

end Hyperbolic.HigherRegularity
