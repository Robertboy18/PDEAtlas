/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Extension by zero from a restricted measure

For a measurable set `s`, extension by zero is an isometric embedding of
`Lᵖ (μ.restrict s)` into `Lᵖ μ`, represented pointwise by the indicator of `s`.
-/

@[expose] public section

noncomputable section


namespace MeasureTheory.Lp

open Set
open scoped ENNReal

variable {α E 𝕜 : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup E]
variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
variable {p : ℝ≥0∞} {μ : Measure α} {s : Set α}

/-- A representative of an `Lᵖ (μ.restrict s)` class, extended by zero off
`s`, lies in `Lᵖ μ`. -/
theorem extendByZero_memLp (hs : MeasurableSet s)
    (f : Lp E p (μ.restrict s)) :
    MemLp (s.indicator (fun x ↦ f x)) p μ :=
  (memLp_indicator_iff_restrict hs.nullMeasurableSet).2 (Lp.memLp f)

/-- Extension by zero from `Lᵖ (μ.restrict s)` to `Lᵖ μ` as a linear map. -/
def extendByZeroₗ (hs : MeasurableSet s) :
    Lp E p (μ.restrict s) →ₗ[𝕜] Lp E p μ where
  toFun f := (extendByZero_memLp hs f).toLp (s.indicator (fun x ↦ f x))
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    have hfg :=
      (ae_eq_restrict_iff_indicator_ae_eq hs).mp (coeFn_add f g)
    filter_upwards [hfg] with x hx
    by_cases hxs : x ∈ s
    · simpa [hxs, Pi.add_apply] using hx
    · simp [hxs]
  map_smul' c f := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    have hcf :=
      (ae_eq_restrict_iff_indicator_ae_eq hs).mp (coeFn_smul c f)
    filter_upwards [hcf] with x hx
    by_cases hxs : x ∈ s
    · simpa [hxs, Pi.smul_apply] using hx
    · simp [hxs]

/-- Extension by zero embeds `Lᵖ (μ.restrict s)` isometrically into `Lᵖ μ`. -/
def extendByZeroₗᵢ [Fact (1 ≤ p)] (hs : MeasurableSet s) :
    Lp E p (μ.restrict s) →ₗᵢ[𝕜] Lp E p μ where
  toLinearMap := extendByZeroₗ hs
  norm_map' f := by
    change ‖(extendByZero_memLp hs f).toLp
      (s.indicator (fun x ↦ f x))‖ = ‖f‖
    rw [norm_toLp, norm_def, eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]

/-- A representative of `extendByZeroₗᵢ hs f` is the indicator extension of
a representative of `f`. -/
theorem extendByZeroₗᵢ_apply_ae [Fact (1 ≤ p)] (hs : MeasurableSet s)
    (f : Lp E p (μ.restrict s)) :
    (extendByZeroₗᵢ (𝕜 := 𝕜) hs f : α → E) =ᵐ[μ]
      s.indicator (fun x ↦ f x) :=
  (extendByZero_memLp hs f).coeFn_toLp

end MeasureTheory.Lp
