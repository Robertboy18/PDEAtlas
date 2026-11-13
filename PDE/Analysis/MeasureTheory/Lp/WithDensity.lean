/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Change of density in finite-exponent `Lᵖ` spaces

If `w` is positive and finite almost everywhere, multiplication by
`w ^ (1 / p)` identifies `Lᵖ (μ.withDensity w)` isometrically with `Lᵖ μ`:
`∫ ‖w^(1/p) f‖^p dμ = ∫ ‖f‖^p w dμ = ∫ ‖f‖^p d(μ.withDensity w)`. This
change-of-measure calculation gives a linear isometric equivalence, so two `Lᵖ` spaces whose
measures differ by a Radon–Nikodym density can be identified. For example, `Lᵖ` of the
surface measure on a `C¹` boundary is identified with `Lᵖ` of a boundary-atlas measure.

Positivity of `w` is what makes the rescaling invertible: it gives
`μ ≪ μ.withDensity w`, so a.e. statements transfer in both directions.
Finiteness keeps the real root `w^(1/p)` meaningful.

## Main results

* `withDensityRoot`: the real function `x ↦ (w x).toReal ^ (1/p)`.
* `eLpNorm_withDensityRoot_smul`: the seminorm identity
  `‖w^(1/p) • f‖_{Lᵖ μ} = ‖f‖_{Lᵖ (μ.withDensity w)}`.
* `memLp_withDensityRoot_smul_iff`, `aestronglyMeasurable_withDensityRoot_smul_iff`:
  membership and measurability transfer in both directions.
* `withDensityRootLIE`: the linear isometric equivalence
  `Lᵖ (μ.withDensity w) ≃ₗᵢ[ℝ] Lᵖ μ`, with `withDensityRootLIE_apply_ae` and
  `withDensityRootLIE_symm_apply_ae` identifying representatives.
* `withDensityRootLIEOfEq`: the same equivalence for any `ν` with
  `μ.withDensity w = ν`.

## Implementation notes

Exponents are real numbers `p > 0` entering as `ENNReal.ofReal p`, with the
`Fact (1 ≤ ENNReal.ofReal p)` instance required by `Lp`. The value of
`densityRoot` at `∞` is whatever `ENNReal.toReal` gives; every theorem here
assumes `w < ∞` a.e., so this choice never matters.

`withDensityRootLIEOfEq` takes the target measure `ν` together with a proof
`μ.withDensity w = ν` rather than fixing `ν := μ.withDensity w`. This avoids
transporting `Lp` elements across an equality of measures when the weighted
measure has been defined under another name.
-/

@[expose] public section

noncomputable section


namespace MeasureTheory.Lp

open scoped ENNReal

variable {α E : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {μ : Measure α} {w : α → ℝ≥0∞}

/-- The real `p`-th root of one extended nonnegative scalar.

The value at `∞` is fixed by `ENNReal.toReal`; change-of-measure results use
this definition only for densities that are finite almost everywhere. -/
def densityRoot (a : ℝ≥0∞) (p : ℝ) : ℝ :=
  a.toReal ^ (1 / p)

/-- The real `p`-th root of an extended nonnegative density.

The value at `∞` is fixed by `ENNReal.toReal`; all results using this
definition assume that the density is finite almost everywhere. -/
def withDensityRoot (w : α → ℝ≥0∞) (p : ℝ) (x : α) : ℝ :=
  densityRoot (w x) p

/-- The density root of a positive finite scalar is nonzero. -/
theorem densityRoot_ne_zero (a : ℝ≥0∞) (ha_pos : 0 < a)
    (ha_top : a < ∞) (p : ℝ) :
    densityRoot a p ≠ 0 :=
  (Real.rpow_pos_of_pos
    (ENNReal.toReal_pos ha_pos.ne' ha_top.ne) _).ne'

private theorem withDensityRoot_ne_zero_ae
    (hw_pos : ∀ᵐ x ∂μ, 0 < w x) (hw_top : ∀ᵐ x ∂μ, w x < ∞)
    (p : ℝ) :
    ∀ᵐ x ∂μ, withDensityRoot w p x ≠ 0 := by
  filter_upwards [hw_pos, hw_top] with x hx_pos hx_top
  exact densityRoot_ne_zero (w x) hx_pos hx_top p

private theorem enorm_withDensityRoot_smul_rpow
    (a : ℝ≥0∞) (ha : a < ∞) {p : ℝ} (hp : 0 < p) (v : E) :
    ‖(a.toReal ^ (1 / p)) • v‖ₑ ^ p = a * ‖v‖ₑ ^ p := by
  rw [enorm_smul, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  congr 1
  rw [Real.enorm_eq_ofReal (Real.rpow_nonneg ENNReal.toReal_nonneg _)]
  rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity)]
  rw [← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]
  exact ENNReal.ofReal_toReal ha.ne

/-- Multiplication by the `p`-th root of a density converts the
`Lᵖ (μ.withDensity w)` seminorm into the `Lᵖ μ` seminorm. -/
theorem eLpNorm_withDensityRoot_smul
    (hw : Measurable w) (hw_top : ∀ᵐ x ∂μ, w x < ∞)
    {p : ℝ} (hp : 0 < p) (f : α → E) :
    eLpNorm (fun x ↦ withDensityRoot w p x • f x)
        (ENNReal.ofReal p) μ =
      eLpNorm f (ENNReal.ofReal p) (μ.withDensity w) := by
  have hroot_meas : Measurable (withDensityRoot w p) :=
    (Real.continuous_rpow_const (one_div_pos.mpr hp).le).measurable.comp
      hw.ennreal_toReal
  have hmeas :
      AEStronglyMeasurable (fun x ↦ withDensityRoot w p x • f x) μ ↔
        AEStronglyMeasurable f (μ.withDensity w) := by
    constructor
    · rintro ⟨g, hg, hfg⟩
      refine ⟨fun x ↦ (withDensityRoot w p x)⁻¹ • g x,
        hroot_meas.inv.stronglyMeasurable.smul hg, ?_⟩
      rw [Filter.EventuallyEq, ae_withDensity_iff hw]
      filter_upwards [hfg, hw_top] with x hx hx_top hx_ne
      have hroot_ne : withDensityRoot w p x ≠ 0 :=
        densityRoot_ne_zero (w x) (bot_lt_iff_ne_bot.mpr hx_ne) hx_top p
      rw [← hx, ← mul_smul, inv_mul_cancel₀ hroot_ne, one_smul]
    · rintro ⟨g, hg, hfg⟩
      refine ⟨fun x ↦ withDensityRoot w p x • g x,
        hroot_meas.stronglyMeasurable.smul hg, ?_⟩
      rw [Filter.EventuallyEq, ae_withDensity_iff hw] at hfg
      filter_upwards [hfg] with x hx
      by_cases hx_zero : w x = 0
      · simp only [withDensityRoot, densityRoot, hx_zero, ENNReal.toReal_zero,
          Real.zero_rpow (one_div_pos.mpr hp).ne', zero_smul]
      · rw [hx hx_zero]
  by_cases hf : AEStronglyMeasurable f (μ.withDensity w)
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top (hmeas.mpr hf),
      eLpNorm_eq_lintegral_rpow_enorm_toReal
        (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top hf,
      ENNReal.toReal_ofReal hp.le,
      lintegral_withDensity_eq_lintegral_mul_non_measurable μ hw hw_top]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hw_top] with x hx
    exact enorm_withDensityRoot_smul_rpow (w x) hx hp (f x)
  · rw [eLpNorm_of_not_aestronglyMeasurable hf,
      eLpNorm_of_not_aestronglyMeasurable (fun h ↦ hf (hmeas.mp h))]

/-- Strong measurability is preserved and reflected by multiplication by the
`p`-th root of a positive finite density. -/
theorem aestronglyMeasurable_withDensityRoot_smul_iff
    (hw : Measurable w) (hw_pos : ∀ᵐ x ∂μ, 0 < w x)
    (hw_top : ∀ᵐ x ∂μ, w x < ∞)
    {p : ℝ} (hp : 0 < p) {f : α → E} :
    AEStronglyMeasurable (fun x ↦ withDensityRoot w p x • f x) μ ↔
      AEStronglyMeasurable f (μ.withDensity w) := by
  have hμw : μ ≪ μ.withDensity w :=
    withDensity_absolutelyContinuous' hw.aemeasurable <|
      hw_pos.mono fun _ hx ↦ hx.ne'
  have hroot_meas : Measurable (withDensityRoot w p) :=
    (Real.continuous_rpow_const (by positivity : 0 ≤ 1 / p)).measurable.comp
      hw.ennreal_toReal
  have hroot_ne := withDensityRoot_ne_zero_ae hw_pos hw_top p
  constructor
  · intro hf
    have hfμ : AEStronglyMeasurable f μ := by
      have hinv := hroot_meas.aestronglyMeasurable.inv₀.smul hf
      apply hinv.congr
      filter_upwards [hroot_ne] with x hx
      change (withDensityRoot w p x)⁻¹ •
        (withDensityRoot w p x • f x) = f x
      rw [← mul_smul, inv_mul_cancel₀ hx, one_smul]
    exact hfμ.mono_ac (withDensity_absolutelyContinuous μ w)
  · intro hf
    exact hroot_meas.aestronglyMeasurable.smul (hf.mono_ac hμw)

/-- Membership in finite-exponent `Lᵖ` is preserved and reflected by the
canonical density-root rescaling. -/
theorem memLp_withDensityRoot_smul_iff
    (hw : Measurable w)
    (hw_top : ∀ᵐ x ∂μ, w x < ∞)
    {p : ℝ} (hp : 0 < p) {f : α → E} :
    MemLp (fun x ↦ withDensityRoot w p x • f x)
        (ENNReal.ofReal p) μ ↔
      MemLp f (ENNReal.ofReal p) (μ.withDensity w) := by
  rw [memLp_iff, memLp_iff, eLpNorm_withDensityRoot_smul hw hw_top hp f]

/-- Rescaling a representative of an `Lᵖ ν` class by the density root gives
an `Lᵖ μ` function when `ν = μ.withDensity w`. -/
theorem withDensityRoot_smul_memLp_of_eq
    (hw : Measurable w)
    (hw_top : ∀ᵐ x ∂μ, w x < ∞)
    {ν : Measure α} (hν : μ.withDensity w = ν)
    {p : ℝ} (hp : 0 < p) (f : Lp E (ENNReal.ofReal p) ν) :
    MemLp (fun x ↦ withDensityRoot w p x • f x)
      (ENNReal.ofReal p) μ := by
  apply (memLp_withDensityRoot_smul_iff hw hw_top hp).2
  rw [hν]
  exact Lp.memLp f

/-- Density-root rescaling from `Lᵖ ν` to `Lᵖ μ` as a linear map, for
`ν = μ.withDensity w`. -/
def withDensityRootOfEqₗ
    (hw : Measurable w) (hw_pos : ∀ᵐ x ∂μ, 0 < w x)
    (hw_top : ∀ᵐ x ∂μ, w x < ∞)
    {ν : Measure α} (hν : μ.withDensity w = ν)
    {p : ℝ} (hp : 0 < p) :
    Lp E (ENNReal.ofReal p) ν →ₗ[ℝ]
      Lp E (ENNReal.ofReal p) μ where
  toFun f :=
    (withDensityRoot_smul_memLp_of_eq hw hw_top hν hp f).toLp
      (fun x ↦ withDensityRoot w p x • f x)
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    have hμν : μ ≪ ν := by
      rw [← hν]
      exact withDensity_absolutelyContinuous' hw.aemeasurable <|
        hw_pos.mono fun _ hx ↦ hx.ne'
    filter_upwards [hμν.ae_eq (Lp.coeFn_add f g)] with x hx
    rw [hx]
    exact smul_add _ _ _
  map_smul' c f := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    have hμν : μ ≪ ν := by
      rw [← hν]
      exact withDensity_absolutelyContinuous' hw.aemeasurable <|
        hw_pos.mono fun _ hx ↦ hx.ne'
    filter_upwards [hμν.ae_eq (Lp.coeFn_smul c f)] with x hx
    rw [hx]
    exact smul_comm _ _ _

private theorem withDensityRootOfEqₗ_apply_ae
    {ν : Measure α} {p : ℝ}
    (hw : Measurable w) (hw_pos : ∀ᵐ x ∂μ, 0 < w x)
    (hw_top : ∀ᵐ x ∂μ, w x < ∞)
    (hν : μ.withDensity w = ν) (hp : 0 < p)
    (f : Lp E (ENNReal.ofReal p) ν) :
    (withDensityRootOfEqₗ hw hw_pos hw_top hν hp f : α → E) =ᵐ[μ]
      fun x ↦ withDensityRoot w p x • f x :=
  (withDensityRoot_smul_memLp_of_eq
    hw hw_top hν hp f).coeFn_toLp

/-- Rescaling a representative of an `Lᵖ μ` class by the reciprocal density
root gives an `Lᵖ ν` function when `ν = μ.withDensity w`. -/
theorem inv_withDensityRoot_smul_memLp_of_eq
    (hw : Measurable w) (hw_pos : ∀ᵐ x ∂μ, 0 < w x)
    (hw_top : ∀ᵐ x ∂μ, w x < ∞)
    {ν : Measure α} (hν : μ.withDensity w = ν)
    {p : ℝ} (hp : 0 < p) (f : Lp E (ENNReal.ofReal p) μ) :
    MemLp (fun x ↦ (withDensityRoot w p x)⁻¹ • f x)
      (ENNReal.ofReal p) ν := by
  have hroot_ne := withDensityRoot_ne_zero_ae hw_pos hw_top p
  have hident :
      (f : α → E) =ᵐ[μ]
        fun x ↦ withDensityRoot w p x •
          ((withDensityRoot w p x)⁻¹ • f x) := by
    filter_upwards [hroot_ne] with x hx
    rw [← mul_smul, mul_inv_cancel₀ hx, one_smul]
  have hmem :
      MemLp (fun x ↦ withDensityRoot w p x •
        ((withDensityRoot w p x)⁻¹ • f x))
        (ENNReal.ofReal p) μ :=
    MemLp.ae_eq hident (Lp.memLp f)
  have := (memLp_withDensityRoot_smul_iff
    hw hw_top hp).1 hmem
  rwa [hν] at this

/-- Reciprocal density-root rescaling from `Lᵖ μ` to `Lᵖ ν`, the inverse of
`withDensityRootOfEqₗ`. -/
def invWithDensityRootOfEq
    (hw : Measurable w) (hw_pos : ∀ᵐ x ∂μ, 0 < w x)
    (hw_top : ∀ᵐ x ∂μ, w x < ∞)
    {ν : Measure α} (hν : μ.withDensity w = ν)
    {p : ℝ} (hp : 0 < p) (f : Lp E (ENNReal.ofReal p) μ) :
    Lp E (ENNReal.ofReal p) ν :=
  (inv_withDensityRoot_smul_memLp_of_eq
    hw hw_pos hw_top hν hp f).toLp
      (fun x ↦ (withDensityRoot w p x)⁻¹ • f x)

private theorem coeFn_invWithDensityRootOfEq
    (hw : Measurable w) (hw_pos : ∀ᵐ x ∂μ, 0 < w x)
    (hw_top : ∀ᵐ x ∂μ, w x < ∞)
    {ν : Measure α} (hν : μ.withDensity w = ν)
    {p : ℝ} (hp : 0 < p) (f : Lp E (ENNReal.ofReal p) μ) :
    (invWithDensityRootOfEq hw hw_pos hw_top hν hp f : α → E) =ᵐ[ν]
      fun x ↦ (withDensityRoot w p x)⁻¹ • f x :=
  (inv_withDensityRoot_smul_memLp_of_eq
    hw hw_pos hw_top hν hp f).coeFn_toLp

/-- If `ν = μ.withDensity w`, density-root rescaling is the canonical linear
isometric equivalence from `Lᵖ ν` to `Lᵖ μ`. This equality-aware form avoids
transporting `Lᵖ` objects across an equality of measures. -/
def withDensityRootLIEOfEq
    {ν : Measure α} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hw : Measurable w) (hw_pos : ∀ᵐ x ∂μ, 0 < w x)
    (hw_top : ∀ᵐ x ∂μ, w x < ∞)
    (hν : μ.withDensity w = ν) (hp : 0 < p) :
    Lp E (ENNReal.ofReal p) ν ≃ₗᵢ[ℝ]
      Lp E (ENNReal.ofReal p) μ :=
  LinearIsometryEquiv.mk
    (LinearEquiv.mk
      (withDensityRootOfEqₗ hw hw_pos hw_top hν hp)
      (invWithDensityRootOfEq hw hw_pos hw_top hν hp)
      (by
        intro f
        apply Lp.ext
        have hνμ : ν ≪ μ := by
          rw [← hν]
          exact withDensity_absolutelyContinuous μ w
        have hout := coeFn_invWithDensityRootOfEq
          hw hw_pos hw_top hν hp
          (withDensityRootOfEqₗ hw hw_pos hw_top hν hp f)
        have hin := hνμ.ae_eq <|
          withDensityRootOfEqₗ_apply_ae hw hw_pos hw_top hν hp f
        have hroot_ne := hνμ.ae_le <|
          withDensityRoot_ne_zero_ae hw_pos hw_top p
        filter_upwards [hout, hin, hroot_ne] with x hxout hxin hxroot
        change
          (invWithDensityRootOfEq hw hw_pos hw_top hν hp
            (withDensityRootOfEqₗ hw hw_pos hw_top hν hp f) :
              α → E) x = f x
        rw [hxout, hxin, ← mul_smul, inv_mul_cancel₀ hxroot, one_smul])
      (by
        intro f
        apply Lp.ext
        have hμν : μ ≪ ν := by
          rw [← hν]
          exact withDensity_absolutelyContinuous' hw.aemeasurable <|
            hw_pos.mono fun _ hx ↦ hx.ne'
        have hout := withDensityRootOfEqₗ_apply_ae
          hw hw_pos hw_top hν hp
          (invWithDensityRootOfEq hw hw_pos hw_top hν hp f)
        have hin := hμν.ae_eq <|
          coeFn_invWithDensityRootOfEq hw hw_pos hw_top hν hp f
        have hroot_ne := withDensityRoot_ne_zero_ae hw_pos hw_top p
        filter_upwards [hout, hin, hroot_ne] with x hxout hxin hxroot
        change
          (withDensityRootOfEqₗ hw hw_pos hw_top hν hp
            (invWithDensityRootOfEq hw hw_pos hw_top hν hp f) :
              α → E) x = f x
        rw [hxout, hxin, ← mul_smul, mul_inv_cancel₀ hxroot, one_smul]))
    (by
      intro f
      change ‖(withDensityRoot_smul_memLp_of_eq
        hw hw_top hν hp f).toLp
          (fun x ↦ withDensityRoot w p x • f x)‖ = ‖f‖
      rw [Lp.norm_toLp, Lp.norm_def,
        eLpNorm_withDensityRoot_smul hw hw_top hp, hν])

/-- A representative of `withDensityRootLIEOfEq` is pointwise multiplication
by the real `p`-th root of the density. -/
theorem withDensityRootLIEOfEq_apply_ae
    {ν : Measure α} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hw : Measurable w) (hw_pos : ∀ᵐ x ∂μ, 0 < w x)
    (hw_top : ∀ᵐ x ∂μ, w x < ∞)
    (hν : μ.withDensity w = ν) (hp : 0 < p)
    (f : Lp E (ENNReal.ofReal p) ν) :
    (withDensityRootLIEOfEq hw hw_pos hw_top hν hp f : α → E) =ᵐ[μ]
      fun x ↦ withDensityRoot w p x • f x :=
  withDensityRootOfEqₗ_apply_ae hw hw_pos hw_top hν hp f

/-- A representative of the inverse of `withDensityRootLIEOfEq` is
pointwise multiplication by the reciprocal density root. -/
theorem withDensityRootLIEOfEq_symm_apply_ae
    {ν : Measure α} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hw : Measurable w) (hw_pos : ∀ᵐ x ∂μ, 0 < w x)
    (hw_top : ∀ᵐ x ∂μ, w x < ∞)
    (hν : μ.withDensity w = ν) (hp : 0 < p)
    (f : Lp E (ENNReal.ofReal p) μ) :
    ((withDensityRootLIEOfEq hw hw_pos hw_top hν hp).symm f :
        α → E) =ᵐ[ν]
      fun x ↦ (withDensityRoot w p x)⁻¹ • f x :=
  coeFn_invWithDensityRootOfEq hw hw_pos hw_top hν hp f

/-- Density-root rescaling is the canonical linear isometric equivalence from
`Lᵖ (μ.withDensity w)` to `Lᵖ μ`. -/
def withDensityRootLIE
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hw : Measurable w) (hw_pos : ∀ᵐ x ∂μ, 0 < w x)
    (hw_top : ∀ᵐ x ∂μ, w x < ∞)
    (hp : 0 < p) :
    Lp E (ENNReal.ofReal p) (μ.withDensity w) ≃ₗᵢ[ℝ]
      Lp E (ENNReal.ofReal p) μ :=
  withDensityRootLIEOfEq hw hw_pos hw_top rfl hp

/-- A representative of `withDensityRootLIE` is pointwise multiplication by
the real `p`-th root of the density. -/
theorem withDensityRootLIE_apply_ae
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hw : Measurable w) (hw_pos : ∀ᵐ x ∂μ, 0 < w x)
    (hw_top : ∀ᵐ x ∂μ, w x < ∞)
    (hp : 0 < p)
    (f : Lp E (ENNReal.ofReal p) (μ.withDensity w)) :
    (withDensityRootLIE hw hw_pos hw_top hp f : α → E) =ᵐ[μ]
      fun x ↦ withDensityRoot w p x • f x :=
  withDensityRootLIEOfEq_apply_ae hw hw_pos hw_top rfl hp f

/-- A representative of the inverse of `withDensityRootLIE` is pointwise
multiplication by the reciprocal density root. -/
theorem withDensityRootLIE_symm_apply_ae
    {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hw : Measurable w) (hw_pos : ∀ᵐ x ∂μ, 0 < w x)
    (hw_top : ∀ᵐ x ∂μ, w x < ∞)
    (hp : 0 < p) (f : Lp E (ENNReal.ofReal p) μ) :
    ((withDensityRootLIE hw hw_pos hw_top hp).symm f : α → E) =ᵐ[
      μ.withDensity w]
      fun x ↦ (withDensityRoot w p x)⁻¹ • f x :=
  withDensityRootLIEOfEq_symm_apply_ae hw hw_pos hw_top rfl hp f

end MeasureTheory.Lp
