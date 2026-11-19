/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.GraphSpace.Representatives.FirstOrder
public import PDE.Spaces.Sobolev.Inequalities.Poincare.Mean.ZeroGradient
import PDE.Spaces.Sobolev.Foundations.Representatives.Algebra

/-!
# Agreement of weak potentials on overlaps

Two Sobolev potentials of the same field differ by a constant on every bounded
connected open overlap. The statement concerns their value
representatives and uses only equality of their weak gradients almost everywhere.
The empty overlap is included, with an arbitrary zero constant.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal Sobolev

namespace SobolevSpace.GraphSpace

variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] {Ω Λ V : Set (ℝ^n)}

/-- Weak potentials with the same gradient differ almost everywhere by
a constant on a bounded preconnected open overlap. -/
theorem exists_ae_eq_const_sub_of_gradient_eq
    (u : W^{1,p}(Ω)) (v : W^{1,p}(Λ))
    (hV : IsOpen V) (hc : IsPreconnected V) (hb : Bornology.IsBounded V)
    (hVΩ : V ⊆ Ω) (hVΛ : V ⊆ Λ)
    (heq : (∇ u : ℝ^n → ℝ^n) =ᵐ[domainMeasure n V] ∇ v) :
    ∃ c : ℝ, (fun x ↦ baseRepresentative u x - baseRepresentative v x)
      =ᵐ[domainMeasure n V] fun _ ↦ c := by
  by_cases hne : V.Nonempty
  · have : IsFiniteMeasure (domainMeasure n V) :=
      isFiniteMeasure_domainMeasure_of_isBounded hb
    have hu : MemLp (baseRepresentative u) p (domainMeasure n V) :=
      (Lp.memLp (wkpBaseCoordinateCLM u)).mono_measure
        (Measure.restrict_mono hVΩ le_rfl)
    have hv : MemLp (baseRepresentative v) p (domainMeasure n V) :=
      (Lp.memLp (wkpBaseCoordinateCLM v)).mono_measure
        (Measure.restrict_mono hVΛ le_rfl)
    apply exists_ae_eq_const_of_weak_gradient_zero hV ⟨hne, hc⟩
      ((hu.integrable (Fact.out : 1 ≤ p)).sub (hv.integrable (Fact.out : 1 ≤ p)))
    intro i
    have hi := hasWeakDerivativeOn_sub [i]
      ((hasWeakDerivativeOn_wkpGradientCLM u i).mono hV.measurableSet hVΩ)
      ((hasWeakDerivativeOn_wkpGradientCLM v i).mono hV.measurableSet hVΛ)
    apply hi.congr_ae Filter.EventuallyEq.rfl
    filter_upwards [heq] with x hx
    simp [hx]
  · refine ⟨0, ?_⟩
    simp [not_nonempty_iff_eq_empty.mp hne, domainMeasure, Filter.EventuallyEq]

end SobolevSpace.GraphSpace
