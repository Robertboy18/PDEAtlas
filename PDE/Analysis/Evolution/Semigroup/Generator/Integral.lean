/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Semigroup.Generator

/-!
# Integrating in a semigroup generator domain

If a vector-valued function and its generator image are integrable, their
integrals still satisfy the generator relation. The integrated-orbit
characterization lets us commute bounded operators with the integral, without
treating the unbounded generator as a continuous operator on the ambient space.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Interval

namespace PDE.Analysis.Evolution.StronglyContinuousSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The generator commutes with an interval integral when both the function and
its generator image are integrable. -/
theorem hasGeneratorAt_intervalIntegral (T : StronglyContinuousSemigroup E)
    {f Af : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (hAf : IntervalIntegrable Af volume a b)
    (hA : ∀ s ∈ uIcc a b, T.HasGeneratorAt (f s) (Af s)) :
    T.HasGeneratorAt (∫ s in a..b, f s) (∫ s in a..b, Af s) := by
  apply (T.hasGeneratorAt_iff_integratedOperator _ _).mpr
  intro t
  calc
    T.integratedOperator t (∫ s in a..b, Af s) =
        ∫ s in a..b, T.integratedOperator t (Af s) :=
      ((T.integratedOperator t).intervalIntegral_comp_comm hAf).symm
    _ = ∫ s in a..b, T t (f s) - f s := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact (T.hasGeneratorAt_iff_integratedOperator _ _).mp (hA s hs) t
    _ = T t (∫ s in a..b, f s) - ∫ s in a..b, f s := by
      rw [intervalIntegral.integral_sub
        ⟨(T t).integrable_comp hf.1, (T t).integrable_comp hf.2⟩ hf,
        (T t).intervalIntegral_comp_comm hf]

end PDE.Analysis.Evolution.StronglyContinuousSemigroup
