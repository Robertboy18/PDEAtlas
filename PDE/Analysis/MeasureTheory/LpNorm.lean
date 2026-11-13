/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic.Positivity.Finset

/-!
# `Lᵖ` norm powers and exponent bookkeeping

At every positive finite exponent, the `p`-th power of the `Lᵖ` norm is the
integral of the pointwise norm to that power. This holds for arbitrary normed
additive groups, including at exponents below one. Real-valued and squared
versions are stated with natural powers and arbitrary almost-everywhere
representatives. `Lp.congrExponent` identifies `Lp` spaces at equal exponents.

`Fact` instances are declared for the exponents that Mathlib's
`fact_one_le_two_ennreal` does not cover: the numerals `1` and `2` in `ℝ≥0` and
cast to `ℝ≥0∞`, the real-exponent form `ENNReal.ofReal 2`, and the Hölder
conjugate `ENNReal.conjExponent p` of an exponent `p ≥ 1`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

/-! ## Exponent facts -/

namespace PDE

/-- The exponent `1 : ℝ≥0` is at least one. -/
instance fact_one_le_one_nnreal : Fact ((1 : ℝ≥0) ≤ 1) := ⟨le_rfl⟩

/-- The exponent `2 : ℝ≥0` is at least one. -/
instance fact_one_le_two_nnreal : Fact ((1 : ℝ≥0) ≤ 2) := ⟨by norm_num⟩

/-- The exponent `1 : ℝ≥0`, cast to `ℝ≥0∞`, is at least one. -/
instance fact_one_le_coe_one_nnreal : Fact (1 ≤ ((1 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The exponent `2 : ℝ≥0`, cast to `ℝ≥0∞`, is at least one. -/
instance fact_one_le_coe_two_nnreal : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The real-exponent form `ENNReal.ofReal 2` of the Hilbert exponent is at least one. -/
instance fact_one_le_ofReal_two : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩

/-- The real-exponent form `ENNReal.ofReal 4` of the exponent `4` is at least one. -/
instance fact_one_le_ofReal_four : Fact (1 ≤ ENNReal.ofReal (4 : ℝ)) := ⟨by norm_num⟩

/-- The Lebesgue exponent `4` is at least one. -/
instance fact_one_le_four_ennreal : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- An exponent `p : ℝ≥0` with `1 ≤ p` is at least one in `ℝ≥0∞`. -/
instance (priority := low) fact_one_le_coe_nnreal {p : ℝ≥0} [hp : Fact (1 ≤ p)] :
    Fact (1 ≤ (p : ℝ≥0∞)) :=
  ⟨by exact_mod_cast hp.out⟩

/-- The Hölder conjugate of an exponent `p ≥ 1` is again at least one. -/
instance fact_one_le_conjExponent (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Fact (1 ≤ ENNReal.conjExponent p) :=
  have : ENNReal.HolderConjugate (ENNReal.conjExponent p) p := inferInstance
  ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩

end PDE

namespace MeasureTheory

/-- The continuous linear identification of two `Lᵖ` spaces whose exponents
are propositionally equal, so statements need not expose casts between the
exponent indices. -/
def Lp.congrExponent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {X : Type*} [MeasurableSpace X]
    (h : p = q) (μ : Measure X) :
    Lp E p μ ≃L[ℝ] Lp E q μ := by
  subst q
  exact ContinuousLinearEquiv.refl ℝ (Lp E p μ)

/-- Applying `Lp.congrExponent` only changes the dependent exponent index. -/
theorem Lp.congrExponent_apply_heq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {X : Type*} [MeasurableSpace X]
    (h : p = q) (μ : Measure X) (f : Lp E p μ) :
    HEq (Lp.congrExponent h μ f) f := by
  subst q
  rfl

/-- Changing an equal exponent preserves the chosen function representative. -/
theorem Lp.coeFn_congrExponent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {X : Type*} [MeasurableSpace X]
    (h : p = q) (μ : Measure X) (f : Lp E p μ) :
    (Lp.congrExponent h μ f : X → E) = (f : X → E) := by
  subst q
  rfl

/-- Two `MemLp.toLp` representatives constructed at equal exponents are
heterogeneously equal. -/
theorem MemLp.toLp_heq_of_exponent_eq
    {E : Type*} [NormedAddCommGroup E]
    {p q : ℝ≥0∞} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → E}
    (h : p = q) (hp : MemLp f p μ) (hq : MemLp f q μ) :
    HEq (hp.toLp f) (hq.toLp f) := by
  subst q
  rfl

/-- The `Lᵖ` norm of a function equals the norm of any `Lp` element representing
it almost everywhere. -/
theorem Lp.lpNorm_eq_norm_of_ae_eq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ℝ≥0∞} {f : α → E}
    (v : Lp E p μ) (hrep : (v : α → E) =ᵐ[μ] f) :
    lpNorm f p μ = ‖v‖ := by
  rw [← toReal_eLpNorm, Lp.norm_def, eLpNorm_congr_ae hrep]

/-- At a positive finite exponent, the power of the `Lᵖ` norm is the
integral of the pointwise norm to that power. No triangle inequality is
needed, so exponents below one are included. -/
theorem Lp.norm_rpow_eq_integral
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {p : ℝ≥0∞} (hp_zero : p ≠ 0) (hp_top : p ≠ ∞)
    (u : Lp E p μ) :
    ‖u‖ ^ p.toReal = ∫ x, ‖u x‖ ^ p.toReal ∂μ := by
  have hnonneg : 0 ≤ ∫ x, ‖u x‖ ^ p.toReal ∂μ :=
    integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg (u x)) _
  rw [Lp.norm_def, (Lp.memLp u).eLpNorm_eq_integral_rpow_norm hp_zero hp_top,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _),
    Real.rpow_inv_rpow hnonneg (ENNReal.toReal_pos hp_zero hp_top).ne']

/--
For a real-valued `Lᵖ` function, the `p`-th power of its norm is the integral
of the `p`-th power of its absolute value.
-/
theorem norm_toLp_rpow_eq_integral_abs
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    ‖hf.toLp f‖ ^ p = ∫ x, |f x| ^ p ∂μ := by
  calc
    ‖hf.toLp f‖ ^ p = ∫ x, |(hf.toLp f) x| ^ p ∂μ := by
      simpa only [ENNReal.toReal_ofReal hp.le, Real.norm_eq_abs] using
        Lp.norm_rpow_eq_integral (ENNReal.ofReal_ne_zero_iff.mpr hp)
          ENNReal.ofReal_ne_top (hf.toLp f)
    _ = ∫ x, |f x| ^ p ∂μ :=
      integral_congr_ae (hf.coeFn_toLp.fun_comp fun z : ℝ ↦ |z| ^ p)

/-- In a Bochner `L²` space, the squared norm is the integral of the
pointwise squared norm. -/
theorem Lp.norm_sq_eq_integral_norm_sq
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    {μ : Measure X} (f : Lp E 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    Lp.norm_rpow_eq_integral two_ne_zero ENNReal.ofNat_ne_top f

/-- The lower integral of the squared pointwise norm is the squared `L²` norm,
for any function representing the same `Lp` element almost everywhere. -/
theorem Lp.lintegral_nnnorm_sq_eq_norm_sq_of_ae_eq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (u : Lp E 2 μ) {f : α → E}
    (hf : (u : α → E) =ᵐ[μ] f) :
    (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ) = ENNReal.ofReal (‖u‖ ^ 2) := by
  calc
    _ = ∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ :=
      lintegral_congr_ae (hf.fun_comp (fun x : E ↦ ‖x‖ₑ ^ 2)).symm
    _ = _ := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, Lp.enorm_def]
      simpa [ENNReal.rpow_two] using
        (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal)) (by norm_num)
          (Lp.aestronglyMeasurable u)).symm

/-- For a real-valued `L²` function, the squared norm is the integral of the
square of its representative. -/
theorem Lp.norm_sq_eq_integral_sq
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, (f x) ^ 2 ∂μ := by
  simpa only [Real.norm_eq_abs, sq_abs] using
    Lp.norm_sq_eq_integral_norm_sq f

/-- For a square-integrable real function, integrating its square gives the
square of its `L²` norm. -/
theorem MemLp.integral_sq_eq_lpNorm_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) :
    (∫ x, f x ^ 2 ∂μ) = lpNorm f 2 μ ^ 2 := by
  calc
    _ = ∫ x, ((hf.toLp f) x) ^ 2 ∂μ :=
      integral_congr_ae (hf.coeFn_toLp.fun_comp fun z : ℝ ↦ z ^ 2).symm
    _ = ‖hf.toLp f‖ ^ 2 := (Lp.norm_sq_eq_integral_sq _).symm
    _ = _ := by rw [Lp.norm_toLp, toReal_eLpNorm]

end MeasureTheory
