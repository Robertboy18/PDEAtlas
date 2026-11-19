/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.WeakWave.EnergyUniqueness.ContinuousRepresentatives
public import PDE.Analysis.Evolution.Gelfand.WeakTimeDerivative.Distributional

/-!
# Distributional derivatives of the original weak wave

The integrated displacement identity implies the corresponding Banach-valued distributional
derivative, `displacement_hasWeakTimeDerivativeOn`; the velocity identity is
`velocity_hasWeakTimeDerivativeOn` of `EnergyUniqueness.Basic`. These consequences let a
classical representative be identified with the original velocity and acceleration by
uniqueness of weak derivatives.
-/

@[expose] public noncomputable section

namespace Hyperbolic.Variational.IsGelfandWeakWaveSolution

open MeasureTheory Set PDE.Analysis.Evolution

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {a b : ℝ} {T : GelfandTriple (V := V) (H := H)}
  {B : ℝ → V →L[ℝ] StrongDual ℝ V}
  {ell : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
  {u : Lp V 2 (volume.restrict (Ioc a b))}
  {v : Lp H 2 (volume.restrict (Ioc a b))}
  {w : Lp (StrongDual ℝ V) 2 (volume.restrict (Ioc a b))}
  {q₀ : V} {p₀ : H}

/-- The original pivot velocity is the weak derivative of the
original displacement in the pivot space. -/
theorem displacement_hasWeakTimeDerivativeOn (h : IsGelfandWeakWaveSolution T B ell u v w q₀ p₀) :
    HasWeakTimeDerivativeOn (Ioo a b) (fun t ↦ T.inclusion (u t)) (fun t ↦ v t) := by
  have hd : HasGelfandWeakTimeDerivativeOn T u
      (T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) v) := by
    intro z τ hτ
    have heq := h.displacementIdentity.equation z τ
    simp only [zero_apply, zero_mul, integral_zero, add_zero, hτ, mul_zero] at heq
    rw [heq]
    apply integral_congr_ae
    filter_upwards [T.pivotToDual.coeFn_compLpL v] with t ht
    rw [ht]
  exact hd.pivot_hasWeakTimeDerivativeOn

end Hyperbolic.Variational.IsGelfandWeakWaveSolution
