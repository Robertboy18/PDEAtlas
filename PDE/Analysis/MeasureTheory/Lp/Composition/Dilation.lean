/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.Composition.MeasureBound
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Dilation of Lp functions

On a finite-dimensional real vector space, composition with `x ↦ a • x` multiplies
Haar measure by `|a⁻¹|` to the dimension of the space. Mathlib supplies this measure
identity. It gives the `Lᵖ` seminorm of a dilated function, `|a|^(-d/p)` times that of the
function, and the bounded composition operator then gives dilation on `Lᵖ` classes with
its exact norm.

The value space is an arbitrary real normed space. The formulas include `p = ∞`,
negative dilation factors, and the zero-dimensional domain.
-/

@[expose] public noncomputable section

namespace MeasureTheory

open Module
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-- The change-of-variables factor of a dilation in the `Lᵖ` seminorm. -/
def dilationFactor (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ)
    (p : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal |(a ^ finrank ℝ E)⁻¹| ^ (1 / p).toReal

theorem dilationFactor_ne_top (a : ℝ) (p : ℝ≥0∞) : dilationFactor E a p ≠ ∞ :=
  ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top

/-- The dilation factor is nonincreasing in `|a|`, so it is bounded near a nonzero base
point. -/
theorem dilationFactor_le_of_le {a b : ℝ} (hb : 0 < b) (hab : b ≤ |a|) (p : ℝ≥0∞) :
    dilationFactor E a p ≤ dilationFactor E b p := by
  unfold dilationFactor
  apply ENNReal.rpow_le_rpow _ ENNReal.toReal_nonneg
  apply ENNReal.ofReal_le_ofReal
  rw [abs_inv, abs_inv, abs_pow, abs_pow, abs_of_pos hb]
  exact inv_anti₀ (pow_pos hb _) (pow_le_pow_left₀ hb.le hab _)

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E}
  [μ.IsAddHaarMeasure]

/-- The `Lᵖ` seminorm of a dilated function. -/
theorem eLpNorm_comp_smul {f : E → F} (hf : AEStronglyMeasurable f μ) {a : ℝ} (ha : a ≠ 0)
    (p : ℝ≥0∞) :
    eLpNorm (fun x ↦ f (a • x)) p μ = dilationFactor E a p * eLpNorm f p μ := by
  have hmap := Measure.map_addHaar_smul μ ha
  have hf' : AEStronglyMeasurable f (Measure.map (a • ·) μ) := by
    rw [hmap]
    exact hf.smul_measure _
  have h := eLpNorm_map_measure (p := p) hf' (continuous_const_smul a).measurable.aemeasurable
  rw [hmap, eLpNorm_smul_measure_of_ne_zero
    (ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero (pow_ne_zero _ ha)))).ne'] at h
  rw [dilationFactor, ← smul_eq_mul]
  exact h.symm

/-- Dilation preserves `Lᵖ`. -/
theorem MemLp.comp_smul {f : E → F} {p : ℝ≥0∞} (hf : MemLp f p μ) {a : ℝ} (ha : a ≠ 0) :
    MemLp (fun x ↦ f (a • x)) p μ := by
  change eLpNorm (fun x ↦ f (a • x)) p μ < ∞
  rw [eLpNorm_comp_smul hf.aestronglyMeasurable ha]
  exact ENNReal.mul_lt_top (dilationFactor_ne_top a p).lt_top hf.eLpNorm_lt_top

end MeasureTheory

namespace MeasureTheory.Lp

open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Composition by a nonzero scalar dilation on Lp classes. -/
def compSMul (a : ℝ) (ha : a ≠ 0) : Lp F p μ →L[ℝ] Lp F p μ :=
  compMeasureLeSMul (a • ·) (continuous_const_smul a).measurable
    ENNReal.ofReal_ne_top (le_of_eq (Measure.map_addHaar_smul μ ha))

/-- The dilation operator represents composition by scalar multiplication. -/
theorem coeFn_compSMul (a : ℝ) (ha : a ≠ 0) (u : Lp F p μ) :
    ⇑(compSMul μ p a ha u) =ᵐ[μ] fun x ↦ u (a • x) :=
  coeFn_compMeasureLeSMul _ _ _ _ u

/-- Dilation by one is the identity on Lp classes. -/
@[simp] theorem compSMul_one (u : Lp F p μ) :
    compSMul μ p 1 one_ne_zero u = u := by
  apply Lp.ext
  simpa only [one_smul] using coeFn_compSMul μ p 1 one_ne_zero u

/-- Successive scalar dilations multiply their factors. -/
theorem compSMul_mul (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (u : Lp F p μ) :
    compSMul μ p (a * b) (mul_ne_zero ha hb) u =
      compSMul μ p a ha (compSMul μ p b hb u) := by
  apply Lp.ext
  have hcomp := (Measure.quasiMeasurePreserving_smul μ ha).ae_eq_comp
    (coeFn_compSMul μ p b hb u)
  filter_upwards [coeFn_compSMul μ p (a * b) (mul_ne_zero ha hb) u,
    coeFn_compSMul μ p a ha (compSMul μ p b hb u), hcomp] with x h₁ h₂ h₃
  simpa only [h₁, h₂, Function.comp_apply, smul_smul, mul_comm] using h₃.symm

/-- The reciprocal dilation undoes a nonzero dilation. -/
@[simp] theorem compSMul_inv_compSMul (a : ℝ) (ha : a ≠ 0) (u : Lp F p μ) :
    compSMul μ p a⁻¹ (inv_ne_zero ha) (compSMul μ p a ha u) = u := by
  rw [← compSMul_mul]
  simp only [inv_mul_cancel₀ ha, compSMul_one]

/-- The exact change of variables formula for the Lp norm of a dilation. -/
theorem norm_compSMul (a : ℝ) (ha : a ≠ 0) (u : Lp F p μ) :
    ‖compSMul μ p a ha u‖ =
      |(a ^ Module.finrank ℝ E)⁻¹| ^ (1 / p).toReal * ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_compSMul μ p a ha u),
    eLpNorm_comp_smul (Lp.aestronglyMeasurable u) ha, ENNReal.toReal_mul, dilationFactor,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (abs_nonneg _)]

end MeasureTheory.Lp
