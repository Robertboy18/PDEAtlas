/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.Primitive
public import PDE.Analysis.Evolution.Integrated.TimeTestFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bochner primitives with prescribed initial value

An integrable curve on a bounded interval has an absolutely continuous primitive with any
prescribed initial value. Cutting the integrand off outside the interval supplies one
globally continuous representative. The `L²` specialization uses finite interval measure;
no endpoint value of an `Lp` representative is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PDE.Analysis.Evolution

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- An integrable curve has a continuous primitive, including its initial value,
whose classical almost-everywhere and distributional derivatives are the given curve. -/
theorem exists_initial_primitive_of_integrableOn {a b : ℝ} {v : ℝ → X}
    (hvint : IntegrableOn v (Ioc a b)) (q₀ : X) :
    ∃ Q : ℝ → X, Continuous Q ∧ Q a = q₀ ∧
      (∀ t ∈ Icc a b, Q t = q₀ + ∫ s in a..t, v s) ∧
      AbsolutelyContinuousOnInterval Q a b ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt Q (v t) t) ∧
      HasWeakTimeDerivativeOn (Ioo a b) Q v := by
  let G : ℝ → X := (Ioc a b).indicator (fun t ↦ v t)
  have hG : Integrable G volume := hvint.integrable_indicator measurableSet_Ioc
  let Q : ℝ → X := fun t ↦ q₀ + ∫ s in a..t, G s
  have hQ : Continuous Q :=
    continuous_const.add
      (intervalIntegral.continuous_primitive (fun _ _ ↦ hG.intervalIntegrable) a)
  have hAC (c d : ℝ) : AbsolutelyContinuousOnInterval Q c d :=
    ((LipschitzWith.const q₀).lipschitzOnWith.absolutelyContinuousOnInterval).add
      (absolutelyContinuousOnInterval_intervalPrimitive hG.locallyIntegrable a c d)
  have hd : ∀ᵐ t ∂volume, HasDerivAt Q (G t) t := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hG.locallyIntegrable] with t ht
    exact (ht a).const_add q₀
  have heq : G =ᵐ[volume.restrict (Ioc a b)] fun t ↦ v t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact indicator_of_mem ht _
  have hweak := HasWeakTimeDerivativeOn.of_absolutelyContinuousOnInterval
    hQ.locallyIntegrable hG.locallyIntegrable hAC hd
  refine ⟨Q, hQ, by simp [Q], ?_, hAC a b, ?_, ?_⟩
  · intro t ht
    dsimp only [Q]
    congr 1
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    have hs' : s ∈ Ioc a b := by
      rw [uIoc_of_le ht.1] at hs
      exact ⟨hs.1, hs.2.trans ht.2⟩
    exact indicator_of_mem hs' _
  · filter_upwards [ae_restrict_of_ae hd, heq] with t ht hGt
    simpa only [hGt] using ht
  · apply (hweak.mono (subset_univ _)).congr_ae_restrict
      measurableSet_Ioo Filter.EventuallyEq.rfl
    exact heq.filter_mono (ae_mono (volume.restrict_mono_set Ioo_subset_Ioc_self))

/-- A square-integrable curve has a continuous primitive, including its initial value,
whose classical almost-everywhere and distributional derivatives are the given curve. -/
theorem exists_initial_primitive_L2 {a b : ℝ}
    (v : Lp X 2 (volume.restrict (Ioc a b))) (q₀ : X) :
    ∃ Q : ℝ → X, Continuous Q ∧ Q a = q₀ ∧
      (∀ t ∈ Icc a b, Q t = q₀ + ∫ s in a..t, v s) ∧
      AbsolutelyContinuousOnInterval Q a b ∧
      (∀ᵐ t ∂volume.restrict (Ioc a b), HasDerivAt Q (v t) t) ∧
      HasWeakTimeDerivativeOn (Ioo a b) Q v :=
  exists_initial_primitive_of_integrableOn ((Lp.memLp v).integrable (by norm_num)) q₀

end PDE.Analysis.Evolution
