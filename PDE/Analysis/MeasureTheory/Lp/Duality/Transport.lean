/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.MeasureTheory.Lp.Duality.FiniteMeasure
public import PDE.Analysis.MeasureTheory.Lp.WithDensity

/-!
# Integral duality under change of density

The finite-exponent density-root isometries preserve the conjugate integral
pairing. At the `L¹` endpoint the dual `L∞` density is transported unchanged:
equivalent measures have the same almost-everywhere bounds.
-/

@[expose] public noncomputable section

open Filter
open scoped ENNReal NNReal

namespace MeasureTheory.Lp

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {w : α → ℝ≥0∞}

/-- An `L∞` representative is bounded almost everywhere by its `L∞` norm. -/
theorem norm_ae_le_norm_top (g : Lp ℝ ∞ ν) : ∀ᵐ x ∂ν, ‖g x‖ ≤ ‖g‖ := by
  have hfinite : eLpNormEssSup g ν ≠ ∞ := by
    rw [← eLpNorm_exponent_top (Lp.aestronglyMeasurable g)]
    exact (Lp.memLp g).eLpNorm_ne_top
  filter_upwards [ae_le_eLpNormEssSup (f := g) (μ := ν)] with x hx
  simpa only [toReal_enorm, Lp.norm_def,
    eLpNorm_exponent_top (Lp.aestronglyMeasurable g)] using
    ENNReal.toReal_mono hfinite hx

/-- Absolute continuity transports an `L∞` density and its norm bound to the new measure. -/
theorem exists_top_density_of_absolutelyContinuous (hμν : μ ≪ ν) (g : Lp ℝ ∞ ν) :
    ∃ G : Lp ℝ ∞ μ, ‖G‖ ≤ ‖g‖ ∧ (G : α → ℝ) =ᵐ[μ] g := by
  have hbound := hμν.ae_le (norm_ae_le_norm_top g)
  have hmem := memLp_top_of_bound ((Lp.aestronglyMeasurable g).mono_ac hμν) ‖g‖ hbound
  refine ⟨hmem.toLp g, ?_, hmem.coeFn_toLp⟩
  rw [Lp.norm_toLp, eLpNorm_exponent_top hmem.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (eLpNormEssSup_le_of_ae_bound hbound)).trans_eq
    (ENNReal.toReal_ofReal (norm_nonneg g))

/-- At conjugate exponents `1` and `∞`, density-root transport preserves the pairing. -/
theorem lpPairing_withDensity_top {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    [ENNReal.HolderConjugate (ENNReal.ofReal p) ∞] (hp : 0 < p)
    (hw : Measurable w) (hw_pos : ∀ᵐ x ∂μ, 0 < w x)
    (hw_top : ∀ᵐ x ∂μ, w x < ∞) (hν : μ.withDensity w = ν)
    (g : Lp ℝ ∞ ν) (G : Lp ℝ ∞ μ) (hG : (G : α → ℝ) =ᵐ[μ] g)
    (f : Lp ℝ (ENNReal.ofReal p) ν) :
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ ∞ (ENNReal.ofReal p) G
        (withDensityRootLIEOfEq hw hw_pos hw_top hν hp f) =
      (ContinuousLinearMap.mul ℝ ℝ).lpPairing ν ∞ (ENNReal.ofReal p) g f := by
  have hpone : p = 1 := by
    have h := congrArg ENNReal.toReal
      ((ENNReal.HolderConjugate.eq_top_iff_eq_one ∞ (ENNReal.ofReal p)).mp rfl)
    simpa only [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_one] using h
  subst p
  have hchange : (∫ x, g x * f x ∂ν) =
      ∫ x, (w x).toReal • (g x * f x) ∂μ := by
    simpa only [hν] using
      integral_withDensity_eq_integral_toReal_smul hw hw_top (fun x ↦ g x * f x)
  rw [ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.lpPairing_eq_integral]
  simp only [ContinuousLinearMap.mul_apply']
  rw [hchange]
  apply integral_congr_ae
  filter_upwards [hG,
    withDensityRootLIEOfEq_apply_ae hw hw_pos hw_top hν hp f]
    with x hGx hfx
  simp only [hGx, hfx, withDensityRoot, densityRoot,
    div_one, Real.rpow_one, smul_eq_mul]
  exact mul_left_comm _ _ _

/-- Conjugate density roots multiply to the original density, so their isometries
preserve the integral pairing for two finite conjugate exponents. -/
theorem lpPairing_withDensity_of_ne_top {p q : ℝ}
    [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)]
    [ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q)]
    (hp : 0 < p) (hq : 0 < q)
    (hw : Measurable w) (hw_pos : ∀ᵐ x ∂μ, 0 < w x)
    (hw_top : ∀ᵐ x ∂μ, w x < ∞) (hν : μ.withDensity w = ν)
    (g : Lp ℝ (ENNReal.ofReal q) ν) (f : Lp ℝ (ENNReal.ofReal p) ν) :
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ (ENNReal.ofReal q) (ENNReal.ofReal p)
        (withDensityRootLIEOfEq hw hw_pos hw_top hν hq g)
        (withDensityRootLIEOfEq hw hw_pos hw_top hν hp f) =
      (ContinuousLinearMap.mul ℝ ℝ).lpPairing ν (ENNReal.ofReal q) (ENNReal.ofReal p)
        g f := by
  have hpq : p.HolderConjugate q := by
    simpa only [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq.le] using
      (ENNReal.HolderConjugate.toReal_of_ne_top
        (p := ENNReal.ofReal p) (q := ENNReal.ofReal q)
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hchange : (∫ x, g x * f x ∂ν) =
      ∫ x, (w x).toReal • (g x * f x) ∂μ := by
    simpa only [hν] using
      integral_withDensity_eq_integral_toReal_smul hw hw_top (fun x ↦ g x * f x)
  rw [ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.lpPairing_eq_integral]
  simp only [ContinuousLinearMap.mul_apply']
  rw [hchange]
  apply integral_congr_ae
  filter_upwards [hw_pos, hw_top,
    withDensityRootLIEOfEq_apply_ae hw hw_pos hw_top hν hq g,
    withDensityRootLIEOfEq_apply_ae hw hw_pos hw_top hν hp f]
    with x hpos htop hg hf
  simp only [hg, hf, withDensityRoot, densityRoot,
    smul_eq_mul]
  rw [mul_mul_mul_comm, ← Real.rpow_add (ENNReal.toReal_pos hpos.ne' htop.ne),
    one_div, one_div, hpq.symm.inv_add_inv_eq_one, Real.rpow_one]

end MeasureTheory.Lp
