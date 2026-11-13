/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Classical
public import PDE.Spaces.Sobolev.Calculus.Differentiation.UniformBoundaryData.Representative

/-!
# Classical initial values in the parabolic compatibility recurrence

The values are derived by `g₀ = g` and `gⱼ₊₁ = fⱼ(a) - Lgⱼ`, with the full
signed autonomous operator. Every finite Sobolev realization satisfies the
same recurrence. The boundary values are those of the continuous extensions to
the closure, so the values of the functions outside the domain play no role.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth

open SobolevSpace SobolevSpace.GraphSpace SobolevSpace.GraphSpace.BoundaryRegularity

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The recursively derived initial time derivatives. -/
def initialValue (P : SmoothFullCoefficients n Ω)
    (f : ℕ → ℝ^n → ℝ) (g : ℝ^n → ℝ) : ℕ → ℝ^n → ℝ
  | 0 => g
  | j + 1 => fun x ↦ f j x - P.classicalLoad (initialValue P f g j) x

/-- Every derived initial value is smooth up to the boundary to every finite order. -/
theorem initialValue_regular (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {f : ℕ → ℝ^n → ℝ} {g : ℝ^n → ℝ}
    (hf : ∀ j r, ContDiffUpToBoundary r (f j) Ω)
    (hg : ∀ r, ContDiffUpToBoundary r g Ω) (j r : ℕ) :
    ContDiffUpToBoundary r (initialValue P f g j) Ω := by
  induction j generalizing r with
  | zero => exact hg r
  | succ j ih =>
    exact (hf j r).sub (P.classicalLoad_regular hopen hbounded (ih (r + 2))) hopen

/-- The realization of the derived datum at any finite spatial order. -/
def initialSobolevValue (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {f : ℕ → ℝ^n → ℝ} {g : ℝ^n → ℝ}
    (hf : ∀ j r, ContDiffUpToBoundary r (f j) Ω)
    (hg : ∀ r, ContDiffUpToBoundary r g Ω) (r j : ℕ) : W^{r,2}(Ω) :=
  (initialValue_regular P hopen hbounded hf hg j r).toWkpSpaceOn hopen hbounded 2

/-- At order zero in time every spatial realization has the original initial class. -/
theorem base_initialSobolevValue_zero (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {f : ℕ → ℝ^n → ℝ} {g : ℝ^n → ℝ}
    (hf : ∀ j r, ContDiffUpToBoundary r (f j) Ω)
    (hg : ∀ r, ContDiffUpToBoundary r g Ω) (r : ℕ) :
    wkpBaseCoordinateCLM (initialSobolevValue P hopen hbounded hf hg r 0) =
      (hg 0).toLp hopen hbounded 2 := by
  apply MeasureTheory.Lp.ext
  exact ((initialValue_regular P hopen hbounded hf hg 0 r).toWkpSpaceOn_base_ae
    hopen hbounded 2).trans ((hg 0).toLp_coeFn hopen hbounded 2).symm

/-- Spatial restriction commutes with the initial-value construction. -/
theorem lowerOrder_initialSobolevValue (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {f : ℕ → ℝ^n → ℝ} {g : ℝ^n → ℝ}
    (hf : ∀ j r, ContDiffUpToBoundary r (f j) Ω)
    (hg : ∀ r, ContDiffUpToBoundary r g Ω) {r s : ℕ} (hsr : s ≤ r) (j : ℕ) :
    lowerOrderCLM hsr (initialSobolevValue P hopen hbounded hf hg r j) =
      initialSobolevValue P hopen hbounded hf hg s j := by
  exact ContDiffUpToBoundary.lowerOrder_toWkpSpaceOn _ hopen hbounded 2 hsr

/-- The classical recurrence agrees with the recurrence for the full higher
Sobolev load. -/
theorem initialSobolevValue_succ (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {f : ℕ → ℝ^n → ℝ} {g : ℝ^n → ℝ}
    (hf : ∀ j r, ContDiffUpToBoundary r (f j) Ω)
    (hg : ∀ r, ContDiffUpToBoundary r g Ω) (r j : ℕ) :
    initialSobolevValue P hopen hbounded hf hg r (j + 1) =
      (hf j r).toWkpSpaceOn hopen hbounded 2 -
        P.load hopen hbounded r (initialSobolevValue P hopen hbounded hf hg (r + 2) j) := by
  unfold initialSobolevValue
  rw [P.load_toWkpSpaceOn, sub_eq_add_neg,
    ← ContDiffUpToBoundary.toWkpSpaceOn_neg, ← ContDiffUpToBoundary.toWkpSpaceOn_add]
  congr 1

/-- The continuous boundary values of each recursively derived datum. -/
def initialBoundaryValue (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    {f : ℕ → ℝ^n → ℝ} {g : ℝ^n → ℝ}
    (hf : ∀ j r, ContDiffUpToBoundary r (f j) Ω)
    (hg : ∀ r, ContDiffUpToBoundary r g Ω) (j : ℕ) : ℝ^n → ℝ :=
  (initialValue_regular P hopen hbounded hf hg j 0).continuousRepresentative

end PDE.Parabolic.DivergenceFormHeat.AutonomousRegularity.Smooth
