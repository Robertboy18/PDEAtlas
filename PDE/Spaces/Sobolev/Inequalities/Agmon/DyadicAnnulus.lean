/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import PDE.Analysis.MeasureTheory.Lp.Composition.Dilation
public import PDE.Spaces.Sobolev.Inequalities.Agmon.Annulus

/-!
# Agmon's inequality on the dyadic annuli `R < |ξ| < 2R`

A function on `ℝ³` whose derivatives satisfy weighted `L²` bounds decays at infinity, and the
usual proof is dyadic. On each annulus `A_R = {R < |ξ| < 2R}` it needs a bound for the supremum
by `L²` norms over `A_R`, with a constant that does not depend on `R`. Rescaling Agmon's
inequality on `1 < |y| < 2` gives

`|u(ξ)| ≤ C (R^{-3/2} ‖u‖_{L²(A_R)} + ‖Du‖_{L²(A_R)}^{1/2} ‖D²u‖_{L²(A_R)}^{1/2})`,  `ξ ∈ A_R`,

for every `R > 0` and every `C²` function `u : ℝ³ → F` with values in a real normed space.
Annuli `r₁ < |ξ| < r₂` with a ratio other than two are not treated.

## Main results

* `eLpNorm_comp_smul_restrict`: for an additive Haar measure on a finite-dimensional real space,
  a measurable set `s`, `a ≠ 0` and every exponent `p`, the `Lᵖ` seminorm of `y ↦ g (a y)` over
  the preimage of `s` is the dilation factor times the seminorm of `g` over `s`. This is
  `MeasureTheory.eLpNorm_comp_smul` for a restricted measure.
* `exists_norm_le_dyadicAnnulus`: the inequality above, with `C` independent of `R` and `u`.

## How it works

For `v(y) = u(R y)` the annulus `A_R` becomes `1 < |y| < 2`, where `exists_norm_le_unitAnnulus`
applies. A change of variables gives `‖v‖_{L²} = R^{-3/2} ‖u‖_{L²(A_R)}`, and each derivative
brings a factor `R`: `‖Dv‖ = R^{-1/2} ‖Du‖` and `‖D²v‖ = R^{1/2} ‖D²u‖`, with the norms over the
two annuli. In the product `‖Dv‖^{1/2} ‖D²v‖^{1/2}` the powers of `R` cancel.

## References

* T. Y. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Section 2.1, Step 3 of the proof
  of Proposition 4, which uses Agmon's inequality on the dyadic annuli.
  <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Real Module
open scoped ENNReal NNReal

namespace PDE.Analysis

/-- **Dilation and restriction.** The `Lᵖ` seminorm of `y ↦ g (a • y)` over the preimage of `s`
under the dilation is the dilation factor times the seminorm of `g` over `s`. -/
theorem eLpNorm_comp_smul_restrict {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
    {μ : Measure E} [μ.IsAddHaarMeasure] {g : E → F} {s : Set E} (hs : MeasurableSet s)
    (hg : AEStronglyMeasurable g (μ.restrict s)) {a : ℝ} (ha : a ≠ 0) (p : ℝ≥0∞) :
    eLpNorm (fun y ↦ g (a • y)) p (μ.restrict ((fun y : E ↦ a • y) ⁻¹' s)) =
      dilationFactor E a p * eLpNorm g p (μ.restrict s) := by
  have hs' : MeasurableSet ((fun y : E ↦ a • y) ⁻¹' s) := (continuous_const_smul a).measurable hs
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs'.nullMeasurableSet,
    ← eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]
  have h : ((fun y : E ↦ a • y) ⁻¹' s).indicator (fun y ↦ g (a • y)) =
      fun y ↦ (s.indicator g) (a • y) := by
    funext y
    by_cases hy : a • y ∈ s
    · rw [indicator_of_mem (show y ∈ (fun y : E ↦ a • y) ⁻¹' s from hy), indicator_of_mem hy]
    · rw [indicator_of_notMem (show y ∉ (fun y : E ↦ a • y) ⁻¹' s from hy),
        indicator_of_notMem hy]
  rw [h]
  exact eLpNorm_comp_smul ((aestronglyMeasurable_indicator_iff hs).2 hg) ha p

/-- A pointwise bound `|f| ≤ c |g|` between continuous functions gives the same bound for the
`L²` norms over the annulus `1 < |y| < 2`. -/
private theorem lpNorm_le_mul_of_norm_le {G H : Type*} [NormedAddCommGroup G]
    [NormedAddCommGroup H] {f : ℝ^3 → G} {g : ℝ^3 → H} {c : ℝ} (hc : 0 ≤ c) (hg : Continuous g)
    (h : ∀ y, ‖f y‖ ≤ c * ‖g y‖) :
    lpNorm f 2 (volume.restrict (unitAnnulus (ℝ^3))) ≤
      c * lpNorm g 2 (volume.restrict (unitAnnulus (ℝ^3))) := by
  have hm : MemLp (fun y ↦ c * ‖g y‖) 2 (volume.restrict (unitAnnulus (ℝ^3))) :=
    memLp_restrict_unitAnnulus (continuous_const.mul hg.norm) 2
  refine (lpNorm_mono_real hm h).trans_eq ?_
  have h2 := lpNorm_const_smul (p := 2) c (fun y ↦ ‖g y‖)
    (volume.restrict (unitAnnulus (ℝ^3)))
  rw [show (c • fun y ↦ ‖g y‖) = fun y ↦ c * ‖g y‖ from rfl,
    lpNorm_norm hg.aestronglyMeasurable] at h2
  simpa [abs_of_nonneg hc] using h2

/-- The dilation factor of `ℝ³` in `L²` is `R^{-3/2}`. -/
private theorem toReal_dilationFactor_three {R : ℝ} (hR : 0 < R) :
    (dilationFactor (ℝ^3) R 2).toReal = R ^ (-(3 / 2) : ℝ) := by
  have h3 : (R ^ 3)⁻¹ = R ^ (-(3 : ℝ)) := by
    rw [Real.rpow_neg hR.le, ← Real.rpow_natCast]
    norm_num
  rw [dilationFactor, finrank_euclideanSpace_fin, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.2 (pow_pos hR 3)), h3,
    ← Real.rpow_mul hR.le]
  norm_num

/-- The dilation by `R` maps the annulus `1 < |y| < 2` onto `R < |ξ| < 2R`. -/
private theorem preimage_smul_dyadicAnnulus {R : ℝ} (hR : 0 < R) :
    (fun y : ℝ^3 ↦ R • y) ⁻¹' {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R} = unitAnnulus (ℝ^3) := by
  ext y
  change (R < ‖R • y‖ ∧ ‖R • y‖ < 2 * R) ↔ (1 < ‖y‖ ∧ ‖y‖ < 2)
  rw [norm_smul, Real.norm_of_nonneg hR.le]
  constructor
  · rintro ⟨a, b⟩
    exact ⟨by nlinarith, by nlinarith⟩
  · rintro ⟨a, b⟩
    exact ⟨by nlinarith, by nlinarith⟩

/-- The `L²` norm over the annulus `1 < |y| < 2` of `y ↦ g (R y)` is `R^{-3/2}` times the norm of
`g` over `R < |ξ| < 2R`. -/
private theorem lpNorm_comp_smul_unitAnnulus {G : Type*} [NormedAddCommGroup G] {g : ℝ^3 → G}
    (hg : Continuous g) {R : ℝ} (hR : 0 < R) :
    lpNorm (fun y ↦ g (R • y)) 2 (volume.restrict (unitAnnulus (ℝ^3))) =
      R ^ (-(3 / 2) : ℝ) * lpNorm g 2 (volume.restrict {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R}) := by
  have hSm : MeasurableSet {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R} :=
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).measurableSet
  have h := eLpNorm_comp_smul_restrict (μ := (volume : Measure (ℝ^3))) hSm
    hg.aestronglyMeasurable hR.ne' 2
  rw [preimage_smul_dyadicAnnulus hR] at h
  have h' := congrArg ENNReal.toReal h
  rwa [ENNReal.toReal_mul, toReal_dilationFactor_three hR] at h'

/-- **Agmon's inequality on the dyadic annuli of `ℝ³`.** There is a constant `C` such that, for
every `R > 0`, every `C²` function `u : ℝ³ → F` and every point `ξ` with `R < |ξ| < 2R`,
`|u(ξ)| ≤ C (R^{-3/2} ‖u‖_{L²(A_R)} + ‖Du‖_{L²(A_R)}^{1/2} ‖D²u‖_{L²(A_R)}^{1/2})`, where all
norms are over `A_R = {R < |ξ| < 2R}`. The constant does not depend on `R`, which is what a
dyadic decay argument needs. The proof applies `exists_norm_le_unitAnnulus` to
`v(y) = u(R y)`. -/
theorem exists_norm_le_dyadicAnnulus {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∀ u : ℝ^3 → F, ContDiff ℝ 2 u →
      ∀ ξ : ℝ^3, R < ‖ξ‖ → ‖ξ‖ < 2 * R →
        ‖u ξ‖ ≤ C * (R ^ (-(3 / 2) : ℝ) *
            lpNorm u 2 (volume.restrict {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R}) +
          √(lpNorm (fderiv ℝ u) 2 (volume.restrict {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R})) *
            √(lpNorm (fderiv ℝ (fderiv ℝ u)) 2
              (volume.restrict {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R}))) := by
  obtain ⟨C, hC, h⟩ := exists_norm_le_unitAnnulus (F := F)
  refine ⟨C, hC, fun R hR u hu ξ h1 h2 ↦ ?_⟩
  set S : Set (ℝ^3) := {ξ : ℝ^3 | R < ‖ξ‖ ∧ ‖ξ‖ < 2 * R} with hS
  have hu1 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  -- the rescaled function and its derivatives
  have hv : ContDiff ℝ 2 (fun y ↦ u (R • y)) := hu.comp (contDiff_const_smul R)
  have hd1 : fderiv ℝ (fun y ↦ u (R • y)) = fun y ↦ R • fderiv ℝ u (R • y) :=
    funext fun y ↦ fderiv_comp_smul R
  have hd2 : fderiv ℝ (fderiv ℝ (fun y ↦ u (R • y))) =
      fun y ↦ R • R • fderiv ℝ (fderiv ℝ u) (R • y) := by
    rw [hd1]
    funext y
    have hdiff : DifferentiableAt ℝ (fun y ↦ fderiv ℝ u (R • y)) y :=
      ((hu1.differentiable one_ne_zero).comp (differentiable_id.const_smul R)) y
    refine (fderiv_const_smul hdiff R).trans ?_
    rw [fderiv_comp_smul R]
  have hy : R⁻¹ • ξ ∈ unitAnnulus (ℝ^3) := by
    rw [← preimage_smul_dyadicAnnulus hR]
    change R • R⁻¹ • ξ ∈ S
    rw [smul_inv_smul₀ hR.ne']
    exact ⟨h1, h2⟩
  have key := h (fun y ↦ u (R • y)) hv (R⁻¹ • ξ) hy
  rw [smul_inv_smul₀ hR.ne'] at key
  -- the three norms
  have e1 : lpNorm (fderiv ℝ (fun y ↦ u (R • y))) 2 (volume.restrict (unitAnnulus (ℝ^3))) ≤
      R * (R ^ (-(3 / 2) : ℝ) * lpNorm (fderiv ℝ u) 2 (volume.restrict S)) := by
    rw [← lpNorm_comp_smul_unitAnnulus hu1.continuous hR]
    refine lpNorm_le_mul_of_norm_le hR.le (hu1.continuous.comp (continuous_const_smul R))
      fun y ↦ ?_
    rw [congrFun hd1 y]
    exact (ContinuousLinearMap.opNorm_smul_le R _).trans_eq
      (by rw [Real.norm_of_nonneg hR.le])
  have e2 : lpNorm (fderiv ℝ (fderiv ℝ (fun y ↦ u (R • y)))) 2
      (volume.restrict (unitAnnulus (ℝ^3))) ≤ R * R *
        (R ^ (-(3 / 2) : ℝ) * lpNorm (fderiv ℝ (fderiv ℝ u)) 2 (volume.restrict S)) := by
    rw [← lpNorm_comp_smul_unitAnnulus (hu1.continuous_fderiv one_ne_zero) hR]
    refine lpNorm_le_mul_of_norm_le (mul_nonneg hR.le hR.le)
      ((hu1.continuous_fderiv one_ne_zero).comp (continuous_const_smul R)) fun y ↦ ?_
    rw [congrFun hd2 y, mul_assoc]
    refine (ContinuousLinearMap.opNorm_smul_le R _).trans ?_
    rw [Real.norm_of_nonneg hR.le]
    refine mul_le_mul_of_nonneg_left ?_ hR.le
    exact (ContinuousLinearMap.opNorm_smul_le R _).trans_eq
      (by rw [Real.norm_of_nonneg hR.le])
  rw [lpNorm_comp_smul_unitAnnulus hu.continuous hR] at key
  -- the powers of `R` cancel in the product
  set D : ℝ := R ^ (-(3 / 2) : ℝ) with hD
  have hD0 : 0 ≤ D := Real.rpow_nonneg hR.le _
  have hD2 : R * D * (R * (R * D)) = 1 := by
    have e : R * D * (R * (R * D)) = D ^ 2 * R ^ 3 := by ring
    rw [e, hD, ← Real.rpow_natCast, ← Real.rpow_mul hR.le, ← Real.rpow_natCast R 3,
      ← Real.rpow_add hR]
    norm_num
  have hprod : √(R * (D * lpNorm (fderiv ℝ u) 2 (volume.restrict S))) *
      √(R * R * (D * lpNorm (fderiv ℝ (fderiv ℝ u)) 2 (volume.restrict S))) =
        √(lpNorm (fderiv ℝ u) 2 (volume.restrict S)) *
          √(lpNorm (fderiv ℝ (fderiv ℝ u)) 2 (volume.restrict S)) := by
    have ha : 0 ≤ lpNorm (fderiv ℝ u) 2 (volume.restrict S) := lpNorm_nonneg
    have hb : 0 ≤ lpNorm (fderiv ℝ (fderiv ℝ u)) 2 (volume.restrict S) := lpNorm_nonneg
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul ha]
    congr 1
    calc R * (D * lpNorm (fderiv ℝ u) 2 (volume.restrict S)) *
          (R * R * (D * lpNorm (fderiv ℝ (fderiv ℝ u)) 2 (volume.restrict S)))
        = R * D * (R * (R * D)) * (lpNorm (fderiv ℝ u) 2 (volume.restrict S) *
          lpNorm (fderiv ℝ (fderiv ℝ u)) 2 (volume.restrict S)) := by ring
      _ = _ := by rw [hD2, one_mul]
  refine key.trans (mul_le_mul_of_nonneg_left ?_ hC)
  rw [← hprod]
  exact add_le_add le_rfl (mul_le_mul (Real.sqrt_le_sqrt e1) (Real.sqrt_le_sqrt e2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end PDE.Analysis
