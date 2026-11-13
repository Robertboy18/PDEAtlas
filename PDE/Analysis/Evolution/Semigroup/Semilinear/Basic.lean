/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Duhamel.Basic

/-!
# Semilinear mild solutions

The semilinear Picard map acts on continuous curves on a closed time interval.
Mathlib's `IccExtend` supplies representatives outside that interval solely to write
the Bochner integral; values outside the interval do not enter the equation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The Picard map for the mild equation on `[0, τ]`. -/
def picardMap (T : StronglyContinuousSemigroup E) (F : C(E, E))
    (x₀ : E) (τ : NNReal) (u : C(Icc (0 : ℝ) (τ : ℝ), E)) :
    C(Icc (0 : ℝ) (τ : ℝ), E) where
  toFun t := T (t : ℝ).toNNReal x₀ +
    T.duhamel (fun s ↦ F (IccExtend τ.property u s)) t
  continuous_toFun :=
    ((T.continuous_orbit x₀).comp
      (continuous_real_toNNReal.comp continuous_subtype_val)).add
      ((T.continuous_duhamel
        (F.continuous.comp u.continuous.Icc_extend')).comp continuous_subtype_val)

/-- A continuous curve satisfying the semilinear variation-of-constants equation.
This is a mild solution, without an assertion that its values lie in the generator domain. -/
def IsMildSolutionOn (T : StronglyContinuousSemigroup E) (F : C(E, E))
    (x₀ : E) (τ : NNReal) (u : C(Icc (0 : ℝ) (τ : ℝ), E)) : Prop :=
  ∀ t, u t = T (t : ℝ).toNNReal x₀ +
    T.duhamel (fun s ↦ F (IccExtend τ.property u s)) t

omit [CompleteSpace E] in
/-- Every mild solution has the prescribed initial value. -/
theorem IsMildSolutionOn.initial_value {T : StronglyContinuousSemigroup E}
    {F : C(E, E)} {x₀ : E} {τ : NNReal}
    {u : C(Icc (0 : ℝ) (τ : ℝ), E)} (hu : T.IsMildSolutionOn F x₀ τ u) :
    u ⟨0, le_rfl, τ.property⟩ = x₀ := by
  simpa [map_zero_apply] using hu ⟨0, le_rfl, τ.property⟩

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
