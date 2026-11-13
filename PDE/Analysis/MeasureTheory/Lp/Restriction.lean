/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Restriction along an inequality of measures

If `μ ≤ ν`, every `Lᵖ ν` class canonically defines an `Lᵖ μ` class with the
same representative. The resulting real continuous linear map is contractive.

This specializes Mathlib's measure-domination map to the constant-one case,
together with its identity and composition laws.
-/

@[expose] public section

noncomputable section


namespace MeasureTheory.Lp

open scoped ENNReal

variable {α E : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {μ ν ρ : Measure α}

/-- The contractive map `Lᵖ ν → Lᵖ μ` induced by an inequality `μ ≤ ν`. -/
def restrictionCLMOfLE (hμν : μ ≤ ν) :
    Lp E p ν →L[ℝ] Lp E p μ :=
  LpToLpOfMeasureLeSMul
    (c := (1 : ℝ≥0∞)) (by simp)
    (by simpa only [one_smul] using hμν)

/-- Restriction along `μ ≤ ν` preserves representatives almost everywhere
with respect to `μ`. -/
theorem restrictionCLMOfLE_apply_ae (hμν : μ ≤ ν) (f : Lp E p ν) :
    (restrictionCLMOfLE hμν f : α → E) =ᵐ[μ] (f : α → E) :=
  coeFn_LpToLpOfMeasureLeSMul
    (c := (1 : ℝ≥0∞)) (by simp)
    (by simpa only [one_smul] using hμν) f

/-- The operator norm of restriction along an inequality of measures is at
most one. -/
theorem norm_restrictionCLMOfLE_le_one (hμν : μ ≤ ν) :
    ‖(restrictionCLMOfLE hμν : Lp E p ν →L[ℝ] Lp E p μ)‖ ≤ 1 := by
  simpa [restrictionCLMOfLE] using
    (norm_LpToLpOfMeasureLeSMul_le
      (E := E) (p := p) (c := (1 : ℝ≥0∞)) (by simp)
      (by simpa only [one_smul] using hμν))

/-- Restriction along an inequality of measures does not increase norms. -/
theorem norm_restrictionCLMOfLE_apply_le (hμν : μ ≤ ν) (f : Lp E p ν) :
    ‖restrictionCLMOfLE hμν f‖ ≤ ‖f‖ := by
  calc
    ‖restrictionCLMOfLE hμν f‖
        ≤ ‖(restrictionCLMOfLE hμν : Lp E p ν →L[ℝ] Lp E p μ)‖ * ‖f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := by
      gcongr
      exact norm_restrictionCLMOfLE_le_one hμν
    _ = ‖f‖ := one_mul _

/-- Restriction along the reflexive measure inequality is the identity. -/
@[simp] theorem restrictionCLMOfLE_refl :
    restrictionCLMOfLE (E := E) (p := p) (le_refl μ) =
      ContinuousLinearMap.id ℝ (Lp E p μ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  simpa using
    (restrictionCLMOfLE_apply_ae
      (E := E) (p := p) (μ := μ) (ν := μ) (le_refl μ) f)

/-- Restricting successively along `μ ≤ ν ≤ ρ` equals direct restriction
along `μ ≤ ρ`. -/
theorem restrictionCLMOfLE_trans (hμν : μ ≤ ν) (hνρ : ν ≤ ρ) :
    (restrictionCLMOfLE (E := E) (p := p) hμν).comp
        (restrictionCLMOfLE (E := E) (p := p) hνρ) =
      restrictionCLMOfLE (E := E) (p := p) (hμν.trans hνρ) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have houter :
      ((restrictionCLMOfLE hμν).comp (restrictionCLMOfLE hνρ) f :
          α → E)
        =ᵐ[μ] (restrictionCLMOfLE hνρ f : α → E) :=
    restrictionCLMOfLE_apply_ae
      (E := E) (p := p) hμν (restrictionCLMOfLE hνρ f)
  have hinner :
      (restrictionCLMOfLE hνρ f : α → E) =ᵐ[μ] (f : α → E) :=
    ae_mono hμν
      (restrictionCLMOfLE_apply_ae (E := E) (p := p) hνρ f)
  have hdirect :
      (restrictionCLMOfLE (hμν.trans hνρ) f : α → E)
        =ᵐ[μ] (f : α → E) :=
    restrictionCLMOfLE_apply_ae
      (E := E) (p := p) (hμν.trans hνρ) f
  exact houter.trans (hinner.trans hdirect.symm)

end MeasureTheory.Lp
