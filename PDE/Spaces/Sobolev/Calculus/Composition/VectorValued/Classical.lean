/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Differentiation.VectorValued.ClassicalToWeak

/-!
# The classical Banach-valued chain rule on an open domain

The Fréchet chain rule gives the coordinate derivative of a composition.
The classical-to-weak identification then makes this a weak derivative identity
on the open domain, for arbitrary Banach codomains.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace

namespace SobolevSpace.VectorValued

variable {n : ℕ} {Ω : Opens ℝ^n}
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] in
/-- The local classical chain rule, stated directly as a Banach-valued weak
derivative identity. -/
theorem hasWeakDerivativeOn_comp_of_contDiffOn {Φ : E → F} {f : ℝ^n → E}
    (hΦ : ContDiff ℝ 1 Φ) (hf : ContDiffOn ℝ 1 f Ω) (i : Fin n) :
    HasWeakDerivativeOn Ω [i] (Φ ∘ f)
      (fun x ↦ fderiv ℝ Φ (f x) ((∂[i] f) x)) := by
  have h := hasWeakDerivativeOn_of_contDiffOn_one (hΦ.comp_contDiffOn hf) i
  apply h.congr_ae Filter.EventuallyEq.rfl
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  change fderiv ℝ (Φ ∘ f) x (EuclideanSpace.single i 1) = _
  rw [fderiv_comp x (hΦ.differentiable one_ne_zero).differentiableAt
    ((hf.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt one_ne_zero)]
  rfl

end SobolevSpace.VectorValued
