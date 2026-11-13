/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Calculus.Composition.FiniteProduct.Coordinates
public import PDE.Analysis.MeasureTheory.Lp.Superposition
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Continuous functions of a finite Sobolev jet

For a `C¹` scalar function with bounded derivative, both its value and its chain-rule
derivative depend continuously on the finite first jet in `Lᵖ`, for finite `p`.
The derivative expression has linear growth in the jet even when the derivative of
the scalar function is merely continuous. This is the convergence needed to close
the classical chain rule along smooth Sobolev approximations.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace.FiniteProductComposition

open MeasureTheory
open scoped ENNReal NNReal

variable {n m : ℕ} {p : ℝ≥0∞} {Ω : Set (ℝ^n)}
  {F : ℝ^m → ℝ} {C : ℝ≥0}

/-- Evaluate a scalar function on the value part of a finite first jet. -/
def valueIntegrand (F : ℝ^m → ℝ) (s : Fin m → ℝ × ℝ^n) : ℝ :=
  F (valuesCLM s)

/-- Apply the derivative to one spatial derivative column of a finite jet. -/
def derivativeIntegrand (F : ℝ^m → ℝ) (i : Fin n)
    (s : Fin m → ℝ × ℝ^n) : ℝ :=
  fderiv ℝ F (valuesCLM s) (derivativeCLM i s)

/-- The chain-rule integrand is continuous for a `C¹` scalar function. -/
theorem continuous_derivativeIntegrand (hF : ContDiff ℝ 1 F) (i : Fin n) :
    Continuous (derivativeIntegrand F i) :=
  ((hF.continuous_fderiv one_ne_zero).comp valuesCLM.continuous).clm_apply
    (derivativeCLM i).continuous

/-- A bounded derivative gives linear growth of the value integrand when `F 0 = 0`. -/
theorem norm_valueIntegrand_le (hF : ContDiff ℝ 1 F) (hzero : F 0 = 0)
    (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C) (s : Fin m → ℝ × ℝ^n) :
    ‖valueIntegrand F s‖ ≤ C * ‖valuesCLM (n := n) (m := m)‖ * ‖s‖ := by
  have hLip : LipschitzWith C F :=
    lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable one_ne_zero) hbound
  calc
    ‖valueIntegrand F s‖ ≤ C * ‖valuesCLM s‖ := by
      simpa [valueIntegrand, hzero] using hLip.norm_sub_le (valuesCLM s) 0
    _ ≤ C * (‖valuesCLM (n := n) (m := m)‖ * ‖s‖) :=
      mul_le_mul_of_nonneg_left (valuesCLM.le_opNorm s) C.coe_nonneg
    _ = _ := (mul_assoc _ _ _).symm

/-- The derivative integrand has linear growth in the full jet. -/
theorem norm_derivativeIntegrand_le (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C)
    (i : Fin n) (s : Fin m → ℝ × ℝ^n) :
    ‖derivativeIntegrand F i s‖ ≤ C * ‖derivativeCLM (m := m) i‖ * ‖s‖ := by
  calc
    ‖derivativeIntegrand F i s‖ ≤ ‖fderiv ℝ F (valuesCLM s)‖ *
        ‖derivativeCLM i s‖ := (fderiv ℝ F (valuesCLM s)).le_opNorm _
    _ ≤ C * ‖derivativeCLM i s‖ :=
      mul_le_mul_of_nonneg_right (hbound _) (norm_nonneg _)
    _ ≤ C * (‖derivativeCLM (m := m) i‖ * ‖s‖) :=
      mul_le_mul_of_nonneg_left ((derivativeCLM i).le_opNorm s) C.coe_nonneg
    _ = _ := (mul_assoc _ _ _).symm

/-- The value of a zero-preserving bounded-derivative function belongs to `Lᵖ`. -/
theorem memLp_valueIntegrand (hF : ContDiff ℝ 1 F) (hzero : F 0 = 0)
    (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C)
    (u : Lp (Fin m → ℝ × ℝ^n) p (domainMeasure n Ω)) :
    MemLp (fun x ↦ valueIntegrand F (u x)) p (domainMeasure n Ω) := by
  refine ((Lp.memLp u).norm.const_mul (C * ‖valuesCLM (n := n) (m := m)‖)).mono' ?_ ?_
  · exact (hF.continuous.comp valuesCLM.continuous).comp_aestronglyMeasurable
      (Lp.memLp u).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ norm_valueIntegrand_le hF hzero hbound (u x)

/-- The chain-rule expression belongs to `Lᵖ` for every finite jet in `Lᵖ`. -/
theorem memLp_derivativeIntegrand (hF : ContDiff ℝ 1 F)
    (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C) (i : Fin n)
    (u : Lp (Fin m → ℝ × ℝ^n) p (domainMeasure n Ω)) :
    MemLp (fun x ↦ derivativeIntegrand F i (u x)) p (domainMeasure n Ω) := by
  refine ((Lp.memLp u).norm.const_mul (C * ‖derivativeCLM (m := m) i‖)).mono' ?_ ?_
  · exact (continuous_derivativeIntegrand hF i).comp_aestronglyMeasurable
      (Lp.memLp u).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x ↦ norm_derivativeIntegrand_le hbound i (u x)

/-- Value superposition is continuous along finite first jets in finite-exponent `Lᵖ`. -/
theorem continuous_valueSuperposition [Fact (1 ≤ p)] (hp : p ≠ ∞) (hF : ContDiff ℝ 1 F)
    (hzero : F 0 = 0) (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C) :
    Continuous (Lp.superposition (fun _ : ℝ^n ↦ valueIntegrand F)
      (memLp_valueIntegrand (p := p) (Ω := Ω) hF hzero hbound)) := by
  apply Lp.continuous_superposition hp _ (Filter.Eventually.of_forall fun _ ↦
    hF.continuous.comp valuesCLM.continuous)
    (C := C * ‖valuesCLM (n := n) (m := m)‖) (a := 0) MemLp.zero
  exact Filter.Eventually.of_forall fun _ s ↦ by
    simpa only [valueIntegrand, Function.comp_apply, Pi.zero_apply, zero_add] using
      norm_valueIntegrand_le hF hzero hbound s

/-- Derivative superposition is continuous without a Lipschitz hypothesis on `DF`. -/
theorem continuous_derivativeSuperposition [Fact (1 ≤ p)] (hp : p ≠ ∞) (hF : ContDiff ℝ 1 F)
    (hbound : ∀ z, ‖fderiv ℝ F z‖ ≤ C) (i : Fin n) :
    Continuous (Lp.superposition (fun _ : ℝ^n ↦ derivativeIntegrand F i)
      (memLp_derivativeIntegrand (p := p) (Ω := Ω) hF hbound i)) := by
  apply Lp.continuous_superposition hp _ (Filter.Eventually.of_forall fun _ ↦
    continuous_derivativeIntegrand hF i)
    (C := C * ‖derivativeCLM (m := m) i‖) (a := 0) MemLp.zero
  exact Filter.Eventually.of_forall fun _ s ↦ by
    simpa only [Pi.zero_apply, zero_add] using norm_derivativeIntegrand_le hbound i s

end SobolevSpace.GraphSpace.FiniteProductComposition
