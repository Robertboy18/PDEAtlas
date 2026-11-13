/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.FDeriv.Calculus

/-!
# Translations and linear images of coordinate derivatives

Translation identities hold for Mathlib's total derivative without
regularity assumptions. Continuous linear maps commute with coordinate
derivatives at points of differentiability; the lambda form below can be
used directly by `rw`. The real-to-complex inclusion also preserves
nondifferentiability, so its identity needs no smoothness hypothesis.
-/

@[expose] public noncomputable section

open PDE

variable {n : ℕ} {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace PDE

/-- Ordinary coordinate derivatives commute with right translation. -/
theorem partialDeriv_comp_add_right (i : Fin n) (f : ℝ^n → E) (a : ℝ^n) :
    (∂[i] (fun x ↦ f (x + a))) = fun x ↦ (∂[i] f) (x + a) := by
  funext x
  change fderiv ℝ (fun y ↦ f (y + a)) x (EuclideanSpace.single i (1 : ℝ)) = _
  rw [fderiv_comp_add_right]
  rfl

/-- Left-translation form of the coordinate derivative identity. -/
theorem partialDeriv_comp_add_left (i : Fin n) (f : ℝ^n → E) (a : ℝ^n) :
    (∂[i] (fun x ↦ f (a + x))) = fun x ↦ (∂[i] f) (a + x) := by
  simpa only [add_comm a] using partialDeriv_comp_add_right i f a

/-- Translation by a negative vector, in the usual subtraction notation. -/
theorem partialDeriv_comp_sub (i : Fin n) (f : ℝ^n → E) (a : ℝ^n) :
    (∂[i] (fun x ↦ f (x - a))) = fun x ↦ (∂[i] f) (x - a) := by
  simpa only [sub_eq_add_neg] using partialDeriv_comp_add_right i f (-a)

/-- Real-to-complex inclusion commutes with total coordinate derivatives.
At a nondifferentiable point both derivatives are zero: differentiability
of the complex-valued map would imply differentiability of its real part. -/
theorem partialDeriv_ofReal (i : Fin n) (f : ℝ^n → ℝ) :
    (∂[i] (fun x ↦ (f x : ℂ))) = fun x ↦ ((∂[i] f) x : ℂ) := by
  funext x
  by_cases hf : DifferentiableAt ℝ f x
  · exact Complex.ofRealCLM.partialDeriv_comp i hf
  · have hc : ¬ DifferentiableAt ℝ (fun y ↦ (f y : ℂ)) x := by
      intro h
      have hr := Complex.reCLM.differentiableAt.comp x h
      apply hf
      simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using hr
    change fderiv ℝ (fun y ↦ (f y : ℂ)) x (EuclideanSpace.single i (1 : ℝ)) =
      (fderiv ℝ f x (EuclideanSpace.single i (1 : ℝ)) : ℂ)
    rw [fderiv_zero_of_not_differentiableAt hc, fderiv_zero_of_not_differentiableAt hf]
    simp

/-- Real-to-complex inclusion commutes with a finite word of total coordinate derivatives.
No regularity assumption is needed. -/
theorem iteratedPartialDeriv_ofReal (α : List (Fin n)) (f : ℝ^n → ℝ) :
    iteratedPartialDeriv α (fun x ↦ (f x : ℂ)) =
      fun x ↦ ((iteratedPartialDeriv α f x : ℝ) : ℂ) := by
  induction α with
  | nil => rfl
  | cons i α ih =>
    change ∂[i] (iteratedPartialDeriv α (fun x ↦ (f x : ℂ))) =
      fun x ↦ ((∂[i] (iteratedPartialDeriv α f)) x : ℂ)
    rw [ih, partialDeriv_ofReal]

end PDE
