/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Inequalities.Morrey.Exponent
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.MetricSpace.HolderNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# One-Dimensional Morrey Estimates

For `1 < p ≤ ∞`, the fundamental theorem of calculus and Hölder's inequality
give

`|u(y) - u(x)| ≤ ‖u'‖_{L^p(ℝ)} |y - x|^(1 - 1/p)`.

The estimate is stated first with extended norms, then with finite real
norms, and finally as `HolderWith` and `MemHolder` conclusions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.6.2, Theorem 4 and its proof, pp. 280-283.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace


open MeasureTheory Set
open scoped ENNReal

/-- **One-dimensional Morrey inequality**, the Hölder seminorm bound of Evans §5.6.2, Theorem 4,
for `n = 1` and with constant one.

For every `1 < p ≤ ∞`, a continuously differentiable real-valued function satisfies

`|u(y) - u(x)| ≤ ‖u'‖_{Lᵖ(ℝ)} |y - x|^(1 - 1/p)`.

The statement uses `ℝ≥0∞` throughout, so it remains meaningful without a separate finiteness
assumption on the global `Lᵖ` seminorm.  When that seminorm is finite, the estimate gives the
usual `(1 - 1/p)`-Hölder bound. -/
theorem enorm_sub_le_eLpNorm_deriv_mul_rpow
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) {p : ℝ≥0∞}
    (hp : (1 : ℝ≥0∞) < p) (x y : ℝ) :
    ‖u y - u x‖ₑ ≤
      eLpNorm (deriv u) p volume *
        ENNReal.ofReal |y - x| ^ morreyExponent 1 p := by
  wlog hxy : x ≤ y generalizing x y with h
  · have hyx : y ≤ x := le_of_not_ge hxy
    simpa only [enorm_sub_rev, abs_sub_comm] using h y x hyx
  have hcontDeriv : Continuous (deriv u) := by
    simpa using hu.continuous_deriv
  have hmeasDeriv : AEStronglyMeasurable (deriv u)
      (volume.restrict (Icc x y)) :=
    hcontDeriv.aestronglyMeasurable
  have hOneLeP : (1 : ℝ≥0∞) ≤ p := hp.le
  have hLocal :
      eLpNorm (deriv u) 1 (volume.restrict (Icc x y)) ≤
        eLpNorm (deriv u) p (volume.restrict (Icc x y)) *
          (volume.restrict (Icc x y)) univ ^
            (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ hOneLeP hmeasDeriv
  have hRestrict :
      eLpNorm (deriv u) p (volume.restrict (Icc x y)) ≤
        eLpNorm (deriv u) p volume :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  calc
    ‖u y - u x‖ₑ
        ≤ ∫⁻ z in Icc x y, ‖deriv u z‖ₑ :=
      enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hu.contDiffOn hxy
    _ = eLpNorm (deriv u) 1 (volume.restrict (Icc x y)) := by
      symm
      exact eLpNorm_one_eq_lintegral_enorm hmeasDeriv
    _ ≤ eLpNorm (deriv u) p (volume.restrict (Icc x y)) *
          (volume.restrict (Icc x y)) univ ^
            (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) :=
      hLocal
    _ ≤ eLpNorm (deriv u) p volume *
          (volume.restrict (Icc x y)) univ ^
            (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) := by
      gcongr
    _ = eLpNorm (deriv u) p volume *
          ENNReal.ofReal |y - x| ^ morreyExponent 1 p := by
      simp [Real.volume_Icc, morreyExponent,
        abs_of_nonneg (sub_nonneg.mpr hxy)]

/-- The finite-norm form of the one-dimensional Morrey estimate: if `u` is `C¹` on `ℝ`,
`1 < p ≤ ∞` and `‖u'‖_{Lᵖ(ℝ)}` is finite, then `|u y - u x| ≤ ‖u'‖_{Lᵖ(ℝ)} |y - x|^(1 - 1/p)`. -/
theorem norm_sub_le_eLpNorm_deriv_toReal_mul_rpow
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) {p : ℝ≥0∞}
    (hp : (1 : ℝ≥0∞) < p)
    (hfinite : eLpNorm (deriv u) p volume ≠ ∞) (x y : ℝ) :
    |u y - u x| ≤
      (eLpNorm (deriv u) p volume).toReal *
        |y - x| ^ morreyExponent 1 p := by
  have h := enorm_sub_le_eLpNorm_deriv_mul_rpow u hu hp x y
  have hdistFinite : ENNReal.ofReal |y - x| ^ morreyExponent 1 p ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_nonneg (morreyExponent_one_pos hp).le ENNReal.ofReal_ne_top
  have hrightFinite :
      eLpNorm (deriv u) p volume *
          ENNReal.ofReal |y - x| ^ morreyExponent 1 p ≠ ∞ :=
    ENNReal.mul_ne_top hfinite hdistFinite
  have hreal := ENNReal.toReal_mono hrightFinite h
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hreal
  simpa [ENNReal.toReal_ofReal (abs_nonneg _), Real.norm_eq_abs] using hreal

/-- The one-dimensional Morrey inequality as a Mathlib `HolderWith` statement: if `u` is `C¹` on
`ℝ`, `1 < p ≤ ∞` and `‖u'‖_{Lᵖ(ℝ)}` is finite, then `u` is Hölder continuous with exponent
`1 - 1/p` and constant `‖u'‖_{Lᵖ(ℝ)}`. -/
theorem holderWith_morreyExponent_one
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) {p : ℝ≥0∞}
    (hp : (1 : ℝ≥0∞) < p)
    (hfinite : eLpNorm (deriv u) p volume ≠ ∞) :
    HolderWith (eLpNorm (deriv u) p volume).toNNReal
      (morreyExponent 1 p).toNNReal u := by
  intro x y
  have h := enorm_sub_le_eLpNorm_deriv_mul_rpow u hu hp x y
  have hgamma : 0 ≤ morreyExponent 1 p :=
    (morreyExponent_one_pos hp).le
  rw [Real.enorm_eq_ofReal_abs] at h
  simpa [edist_dist, Real.dist_eq, abs_sub_comm,
    ENNReal.coe_toNNReal hfinite, Real.coe_toNNReal _ hgamma] using h

/-- A `C¹` real-valued function on the line whose derivative has finite `Lᵖ` seminorm belongs to
the global Hölder class with exponent `1 - 1/p`, for every `1 < p ≤ ∞`.

This is the `MemHolder` form of the one-dimensional Morrey inequality (Evans §5.6.2,
Theorem 4). -/
theorem memHolder_morreyExponent_one
    (u : ℝ → ℝ) (hu : ContDiff ℝ 1 u) {p : ℝ≥0∞}
    (hp : (1 : ℝ≥0∞) < p)
    (hfinite : eLpNorm (deriv u) p volume ≠ ∞) :
    MemHolder (morreyExponent 1 p).toNNReal u :=
  ⟨(eLpNorm (deriv u) p volume).toNNReal,
    holderWith_morreyExponent_one u hu hp hfinite⟩

end SobolevSpace
