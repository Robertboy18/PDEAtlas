/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Integrating a continuous derivative under local domination

A locally uniform integrable majorant for the derivative gives both the actual
derivative of a parameter integral and its continuity. The index space is an
arbitrary measure space; compact support and finite measure are unnecessary.
-/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped Topology

variable {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : E → α → F} {D : E → α → E →L[ℝ] F}

namespace PDE

/-- A locally dominated derivative integrates to the actual Fréchet derivative
of the parameter integral. -/
theorem hasFDerivAt_integral_of_locally_dominated
    (hf : ∀ x, Integrable (f x) μ)
    (hD : ∀ x, AEStronglyMeasurable (D x) μ)
    (hd : ∀ᵐ a ∂μ, ∀ x, HasFDerivAt (fun y ↦ f y a) (D x a) x)
    (hbound : ∀ x, ∃ s ∈ 𝓝 x, ∃ b : α → ℝ,
      Integrable b μ ∧ ∀ᵐ a ∂μ, ∀ y ∈ s, ‖D y a‖ ≤ b a)
    (x : E) :
    HasFDerivAt (fun y ↦ ∫ a, f y a ∂μ) (∫ a, D x a ∂μ) x := by
  obtain ⟨s, hs, b, hb, hDb⟩ := hbound x
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le hs
    (Eventually.of_forall fun y ↦ (hf y).aestronglyMeasurable)
    (hf x) (hD x) hDb hb (hd.mono fun a ha y _ ↦ ha y)

/-- Local domination of a continuous derivative makes the integral `C¹`.
The majorant may depend on the parameter neighbourhood. -/
theorem contDiff_one_integral_of_locally_dominated
    (hf : ∀ x, Integrable (f x) μ)
    (hD : ∀ x, AEStronglyMeasurable (D x) μ)
    (hd : ∀ᵐ a ∂μ, ∀ x, HasFDerivAt (fun y ↦ f y a) (D x a) x)
    (hc : ∀ᵐ a ∂μ, Continuous (fun x ↦ D x a))
    (hbound : ∀ x, ∃ s ∈ 𝓝 x, ∃ b : α → ℝ,
      Integrable b μ ∧ ∀ᵐ a ∂μ, ∀ y ∈ s, ‖D y a‖ ≤ b a) :
    ContDiff ℝ 1 (fun x ↦ ∫ a, f x a ∂μ) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun x ↦ ∫ a, D x a ∂μ, continuous_iff_continuousAt.mpr fun x ↦ ?_,
    fun x ↦ ?_⟩
  · obtain ⟨s, hs, b, hb, hDb⟩ := hbound x
    apply continuousAt_of_dominated (Eventually.of_forall hD) _ hb
      (hc.mono fun a ha ↦ ha.continuousAt)
    filter_upwards [hs] with y hy
    exact hDb.mono fun a ha ↦ ha y hy
  · exact hasFDerivAt_integral_of_locally_dominated hf hD hd hbound x

end PDE
