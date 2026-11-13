/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Foundations.VectorValued.WeakDerivatives
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Testing Banach-valued weak derivatives by the continuous dual

For Bochner locally integrable functions, the scalar weak identities obtained by every
continuous linear functional recover the vector identity. Local integrability is required
before commuting a functional with the Bochner integral.
-/

@[expose] public noncomputable section

open PDE (iteratedPartialDeriv)
open MeasureTheory TopologicalSpace
open scoped Distributions

namespace SobolevSpace.VectorValued

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {Ω : Opens ℝ^n} {α : List (Fin n)} {f g : ℝ^n → F}

/-- Scalar weak derivatives under every continuous linear functional determine the
Banach-valued weak derivative, provided both functions are Bochner locally integrable. -/
theorem hasWeakDerivativeOn_of_forall_dual
    (hf : LocallyIntegrableOn f Ω volume) (hg : LocallyIntegrableOn g Ω volume)
    (h : ∀ L : F →L[ℝ] ℝ, HasWeakDerivativeOn Ω α (L ∘ f) (L ∘ g)) :
    HasWeakDerivativeOn Ω α f g := by
  refine ⟨hf, hg, ?_⟩
  intro φ
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  have hleft : Integrable (fun x ↦ iteratedPartialDeriv α φ.toFun x • f x)
      (domainMeasure n Ω) := ((iteratedPartialDerivTest α φ).integrable_smul hf).mono_measure
    Measure.restrict_le_self
  have hright : Integrable (fun x ↦ φ x • g x) (domainMeasure n Ω) :=
    (φ.integrable_smul hg).mono_measure Measure.restrict_le_self
  rw [map_smul, ← L.integral_comp_comm hleft, ← L.integral_comp_comm hright]
  simpa only [map_smul, Function.comp_apply] using (h L).integral_identity φ

/-- Under Bochner local integrability, the vector relation is equivalent to its
scalar observations under every continuous linear functional. -/
theorem hasWeakDerivativeOn_iff_forall_dual
    (hf : LocallyIntegrableOn f Ω volume) (hg : LocallyIntegrableOn g Ω volume) :
    HasWeakDerivativeOn Ω α f g ↔ ∀ L : F →L[ℝ] ℝ,
      SobolevSpace.HasWeakDerivativeOn (Ω : Set ℝ^n) α (L ∘ f) (L ∘ g) := by
  constructor
  · intro h L
    exact hasWeakDerivativeOn_real_iff.mp (h.map L)
  · intro h
    exact hasWeakDerivativeOn_of_forall_dual hf hg
      (fun L ↦ hasWeakDerivativeOn_real_iff.mpr (h L))

end SobolevSpace.VectorValued
