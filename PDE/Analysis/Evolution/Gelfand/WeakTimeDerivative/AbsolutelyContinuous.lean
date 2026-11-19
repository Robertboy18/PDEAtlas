/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Gelfand weak derivatives of absolutely continuous curves

If `u : ℝ → V` is absolutely continuous on `[a, b]` with derivative `du` almost everywhere,
then the class of `energyToDual ∘ du` is the Gelfand weak time derivative of the class of `u`.
The proof is integration by parts against time tests in the pivot inner product. Absolutely
continuous finite-dimensional Galerkin trajectories are the main example.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set

namespace PDE.Analysis.Evolution

/-- If `u` is absolutely continuous on `[a, b]` with `u' = du` almost everywhere, and `U`,
`G` are the classes of `u` and `energyToDual ∘ du`, then `G` is the Gelfand weak time
derivative of `U`. -/
theorem HasGelfandWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval
    {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : GelfandTriple (V := V) (H := H))
    {a b : ℝ} (hab : a ≤ b) {u du : ℝ → V}
    (huAC : AbsolutelyContinuousOnInterval u a b)
    (hdu : ∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt u (du t) t)
    {U : Lp V 2 (volume.restrict (Ioc a b))}
    {G : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
    (hU : (U : ℝ → V) =ᵐ[volume.restrict (Ioc a b)] u)
    (hG : (G : ℝ → StrongDual ℝ V) =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ T.energyToDual (du t)) :
    HasGelfandWeakTimeDerivativeOn T U G := by
  intro v τ hτ
  have hJAC : AbsolutelyContinuousOnInterval (fun t ↦ T.inclusion (u t)) a b :=
    T.inclusion.lipschitzWith.comp_absolutelyContinuousOnInterval huAC
  have hJdu : ∀ᵐ t ∂volume.restrict (Ioc a b),
      HasDerivAt (fun s ↦ T.inclusion (u s)) (T.inclusion (du t)) t := by
    filter_upwards [hdu] with t ht
    exact T.inclusion.hasFDerivAt.comp_hasDerivAt t ht
  have hp := τ.integrationByParts_inner hab (T.inclusion v) hJAC hJdu
  rw [hτ, mul_zero, add_zero, intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hab] at hp
  calc
    _ = ∫ t in Ioc a b, inner ℝ (T.inclusion (du t)) (T.inclusion v) * τ.toFun t := by
      apply integral_congr_ae
      filter_upwards [hG, τ.memLp.coeFn_toLp] with t ht hτt
      change τ.toLp t = τ.toFun t at hτt
      rw [ht, hτt]
      rfl
    _ = -(∫ t in Ioc a b, inner ℝ (T.inclusion (u t)) (T.inclusion v) * τ.derivFun t) :=
      hp.symm
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hU, τ.derivMemLp.coeFn_toLp] with t ht hτt
      change τ.derivToLp t = τ.derivFun t at hτt
      rw [ht, hτt]

end PDE.Analysis.Evolution
