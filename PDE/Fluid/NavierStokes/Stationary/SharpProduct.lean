/-
Copyright (c) 2026 PDEAtlas Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDEAtlas Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import PDE.Fluid.NavierStokes.Stationary.Trilinear
public import PDE.Fluid.NavierStokes.Stationary.SharpSobolev
public import PDE.Analysis.MeasureTheory.Lp.EuclideanFields
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import PDE.Analysis.MeasureTheory.Lp.IntegralPower
import PDE.Spaces.Sobolev.Inequalities.Sobolev.FirstOrder.ThreeDimensionalProduct

/-!
# Products of `H¹(ℝ³)` fields with the sharp Sobolev constant

For fields `f` in `H¹(ℝ³; ℝᵐ)` and `g` in `H¹(ℝ³; ℝᵏ)`, the product of their lengths satisfies

`‖|f| |g|‖₂ ≤ K₄ ‖∇f‖₂ ‖g‖₂^{1/2} ‖∇g‖₂^{1/2}`,  `K₄ = 2 / (3^{3/4} π)`,

the product estimate (A.1) of Hou, Wang and Yang. For `g = f` it gives
`‖f‖₄² ≤ K₄ ‖f‖₂^{1/2} ‖∇f‖₂^{3/2}` and `‖f‖₄² ≤ (‖f‖₂² + ‖∇f‖₂²) / (2π)`. A field with `m`
components is a finite family `f : ι → H¹(ℝ³)`, with `‖f‖₂² = ∑ᵢ ‖fᵢ‖₂²` and
`‖∇f‖₂² = ∑ᵢ ‖∇fᵢ‖₂²`, and a velocity field of `H¹(ℝ³)³` is the family of its three components.
The domain is `ℝ³`; other dimensions have other exponents and constants and are not stated.

## Main results

* `SobolevSpace.Inequalities.sobolevProductConstantThree`: the constant `K₄`, with
  `sharpSobolevConstant_three_rpow_three_halves` (`K_s^{3/2} = K₄`, where `K_s` is
  `sharpSobolevConstant 3`) and `three_rpow_div_four_mul_sobolevProductConstantThree`
  (`(3^{3/4} / 4) K₄ = 1 / (2π)`).
* `SobolevSpace.Inequalities.rpow_half_mul_rpow_three_halves_le` (all real `a, b ≥ 0`):
  `a^{1/2} b^{3/2} ≤ (3^{3/4} / 4) (a² + b²)`.
* `SobolevSpace.Inequalities.familyRepresentative`: the field of a family, as a function, with
  `memLp_two_familyRepresentative`, `memLp_six_familyRepresentative` and
  `toReal_eLpNorm_two_familyRepresentative` (all finite families): it lies in `L²` and in `L⁶`,
  and its `L²` norm is `(∑ᵢ ‖fᵢ‖₂²)^{1/2}`.
* `SobolevSpace.Inequalities.toReal_eLpNorm_six_familyRepresentative_le` (all finite families):
  `‖f‖₆ ≤ K_s ‖∇f‖₂`.
* `SobolevSpace.Inequalities.toReal_eLpNorm_norm_mul_norm_familyRepresentative_le` (all finite
  families `f`, `g`, with any two numbers of components): the estimate (A.1).
* `SobolevSpace.Inequalities.toReal_eLpNorm_four_familyRepresentative_sq_le` and
  `toReal_eLpNorm_four_familyRepresentative_sq_le_add` (all finite families): the two `L⁴` bounds.
* In `NavierStokes.Stationary`, the same statements for the velocity fields of `H¹(ℝ³)³`, with
  `representative`, `massCLM` and `gradientCLM`: `memLp_six_representative`,
  `toReal_eLpNorm_six_representative_le`, `toReal_eLpNorm_norm_mul_norm_representative_le`,
  `toReal_eLpNorm_four_representative_sq_le` and `toReal_eLpNorm_four_representative_sq_le_add`,
  through `representative_eq_familyRepresentative`, `norm_massCLM_sq` and `norm_gradientCLM_sq`.
  `toReal_eLpNorm_two_representative` (all fields of `H¹(ℝⁿ)ⁿ`): the `L²` norm of `v` is
  `‖massCLM v‖`.

## How it works

The sharp Sobolev inequality `‖u‖₆ ≤ K_s ‖∇u‖₂` for a scalar `u` in `H¹(ℝ³)`, with
`K_s = 2^{2/3} / (√3 π^{2/3})`, is `toReal_eLpNorm_six_le_sharp`, and `K_s` is
`sharpSobolevConstant 3` (`sharpSobolevConstant_three`). Minkowski's inequality in `L³` for the
squares of the components (`MeasureTheory.eLpNorm_euclidean_rpow_two_le_sum`) passes it to a
field with finitely many components:

`‖u‖₆² = ‖∑ᵢ uᵢ²‖₃ ≤ ∑ᵢ ‖uᵢ²‖₃ = ∑ᵢ ‖uᵢ‖₆² ≤ K_s² ∑ᵢ ‖∇uᵢ‖₂² = K_s² ‖∇u‖₂²`.

The paper passes from scalar functions to fields with the inequality `|∇|u|| ≤ |∇u|` instead; the
constant is the same, and the chain rule for `|u|` is not needed here. Hölder's inequality with
the exponents `6` and `3`, and once more with `4` and `12` for `|g| = |g|^{1/2} |g|^{1/2}`, gives
`‖|f| |g|‖₂ ≤ ‖f‖₆ ‖g‖₃ ≤ ‖f‖₆ ‖g‖₂^{1/2} ‖g‖₆^{1/2}`
(`MeasureTheory.eLpNorm_norm_mul_norm_two_le`). The Sobolev inequality for `f` and for `g` then
bounds the right side by `K₄ ‖∇f‖₂ ‖g‖₂^{1/2} ‖∇g‖₂^{1/2}`, since `K₄ = K_s^{3/2}`. For `g = f`
the left side is `‖f‖₄²` (`MeasureTheory.eLpNorm_norm_mul_norm_self`). The weighted mean
inequality `a^{1/2} b^{3/2} ≤ (3^{3/4} / 4) (a² + b²)` and `(3^{3/4} / 4) K₄ = 1 / (2π)` give the
second `L⁴` bound.

Ladyzhenskaya's inequality in PDEAtlas has a constant larger by the factor `π/2`:
`NavierStokes.l4_ladyzhenskaya_gradient`, `27 ‖u‖₄⁸ ≤ ‖u‖₂² ‖∇u‖₂⁶` for a scalar `u`, is
`‖u‖₄² ≤ 3^{-3/4} ‖u‖₂^{1/2} ‖∇u‖₂^{3/2}`, and `3^{-3/4} = (π/2) K₄`. For velocity fields,
`NavierStokes.Stationary.toReal_eLpNorm_representative_le_half` gives `‖v‖₄² ≤ ‖v‖² / 4`, against
`‖v‖² / (2π)` here, where `‖v‖² = ‖massCLM v‖² + ‖gradientCLM v‖²`
(`NavierStokes.Stationary.norm_sq_eq_mass_add_gradient`).

## References

* G. Talenti, "Best constant in Sobolev inequality", *Ann. Mat. Pura Appl.* 110 (1976), 353-372.
  <https://doi.org/10.1007/BF02418013>
* T. Hou, Y. Wang and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116, Appendix A, Lemma 6 with (A.1)
  and its proof. <https://arxiv.org/abs/2509.25116>
-/

@[expose] public noncomputable section

set_option linter.missingDocs true

open MeasureTheory SobolevSpace SobolevSpace.GraphSpace SobolevSpace.Inequalities
open scoped ENNReal Sobolev Real

namespace SobolevSpace.Inequalities

/-! ## The constants -/

/-- The constant `K₄ = 2 / (3^{3/4} π)` of the product estimate (A.1) of Hou, Wang and Yang,
`‖f g‖₂ ≤ K₄ ‖∇f‖₂ ‖g‖₂^{1/2} ‖∇g‖₂^{1/2}`. -/
def sobolevProductConstantThree : ℝ := 2 / (3 ^ (3 / 4 : ℝ) * π)

/-- The product constant `K₄` is positive. -/
theorem sobolevProductConstantThree_pos : 0 < sobolevProductConstantThree := by
  unfold sobolevProductConstantThree
  positivity

/-- For a real `x ≥ 0`, `x ^ (3 / 2) = x * x ^ (1 / 2)`, where the exponents are real. -/
theorem rpow_three_halves_eq_mul_rpow_half {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * x ^ (1 / 2 : ℝ) := by
  rw [Real.rpow_of_add_eq hx (by norm_num) (by norm_num : (1 : ℝ) + 1 / 2 = 3 / 2),
    Real.rpow_one]

/-- The two constants are linked by `K_s ^ (3 / 2) = K₄`:
`(2^{2/3} / (√3 π^{2/3}))^{3/2} = 2 / (3^{3/4} π)`. -/
theorem sharpSobolevConstant_three_rpow_three_halves :
    sharpSobolevConstant 3 ^ (3 / 2 : ℝ) = sobolevProductConstantThree := by
  have h2 : ((2 : ℝ) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = 2 := by
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have h3 : (√3 : ℝ) ^ (3 / 2 : ℝ) = (3 : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hπ : (π ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = π := by
    rw [← Real.rpow_mul Real.pi_pos.le]
    norm_num
  rw [sharpSobolevConstant_three]
  unfold sobolevProductConstantThree
  rw [Real.div_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity), h2, h3, hπ]

/-- `K_s * K_s ^ (1 / 2) = K₄`. This is the form in which the Sobolev inequality for `f` and
the square root of the Sobolev inequality for `g` combine in (A.1). -/
theorem sharpSobolevConstant_three_mul_rpow_half :
    sharpSobolevConstant 3 * sharpSobolevConstant 3 ^ (1 / 2 : ℝ) =
      sobolevProductConstantThree := by
  rw [← sharpSobolevConstant_three_rpow_three_halves,
    rpow_three_halves_eq_mul_rpow_half (sharpSobolevConstant_pos le_rfl).le]

/-- `(3^{3/4} / 4) K₄ = 1 / (2π)`: the constant of the weighted mean inequality
`rpow_half_mul_rpow_three_halves_le` times `K₄`. -/
theorem three_rpow_div_four_mul_sobolevProductConstantThree :
    3 ^ (3 / 4 : ℝ) / 4 * sobolevProductConstantThree = 1 / (2 * π) := by
  unfold sobolevProductConstantThree
  rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- **A weighted mean inequality.** For real `a, b ≥ 0`,
`a ^ (1 / 2) * b ^ (3 / 2) ≤ (3 ^ (3 / 4) / 4) * (a ^ 2 + b ^ 2)`, where the exponents `1 / 2`,
`3 / 2` and `3 / 4` are real. It is the inequality between the geometric and the arithmetic
mean of `a ^ 2` and `b ^ 2 / 3` with the weights `1 / 4` and `3 / 4`. -/
theorem rpow_half_mul_rpow_three_halves_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ (1 / 2 : ℝ) * b ^ (3 / 2 : ℝ) ≤ 3 ^ (3 / 4 : ℝ) / 4 * (a ^ 2 + b ^ 2) := by
  have hc : (0 : ℝ) < 3 ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hA : (a ^ 2) ^ (1 / 4 : ℝ) = a ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul ha]
    norm_num
  have hB : (b ^ 2 / 3) ^ (3 / 4 : ℝ) = b ^ (3 / 2 : ℝ) / 3 ^ (3 / 4 : ℝ) := by
    rw [Real.div_rpow (sq_nonneg b) (by norm_num), ← Real.rpow_two, ← Real.rpow_mul hb]
    norm_num
  have h := Real.geom_mean_le_arith_mean2_weighted (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (0 : ℝ) ≤ 3 / 4) (sq_nonneg a)
    (div_nonneg (sq_nonneg b) (by norm_num : (0 : ℝ) ≤ 3))
    (by norm_num : (1 / 4 : ℝ) + 3 / 4 = 1)
  rw [hA, hB] at h
  have h' : a ^ (1 / 2 : ℝ) * b ^ (3 / 2 : ℝ) / 3 ^ (3 / 4 : ℝ) ≤ (a ^ 2 + b ^ 2) / 4 := by
    calc a ^ (1 / 2 : ℝ) * b ^ (3 / 2 : ℝ) / 3 ^ (3 / 4 : ℝ)
        = a ^ (1 / 2 : ℝ) * (b ^ (3 / 2 : ℝ) / 3 ^ (3 / 4 : ℝ)) := mul_div_assoc _ _ _
      _ ≤ 1 / 4 * a ^ 2 + 3 / 4 * (b ^ 2 / 3) := h
      _ = (a ^ 2 + b ^ 2) / 4 := by ring
  calc a ^ (1 / 2 : ℝ) * b ^ (3 / 2 : ℝ)
      ≤ (a ^ 2 + b ^ 2) / 4 * 3 ^ (3 / 4 : ℝ) := (div_le_iff₀ hc).mp h'
    _ = 3 ^ (3 / 4 : ℝ) / 4 * (a ^ 2 + b ^ 2) := by ring

end SobolevSpace.Inequalities

namespace SobolevSpace.Inequalities

/-! ## Fields with finitely many components in `H¹(ℝ³)` -/

/-- The Euclidean field whose components are the chosen representatives of a family of functions
of `H¹(ℝ³)`: the element `(fᵢ)ᵢ` of `H¹(ℝ³; ℝᵐ)` as a function on `ℝ³`. -/
def familyRepresentative {ι : Type*} (f : ι → H¹(ℝ^3)) (x : ℝ^3) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ baseRepresentative (f i) x

/-- The components of the field of a family are the representatives of its members. -/
theorem familyRepresentative_apply {ι : Type*} (f : ι → H¹(ℝ^3)) (x : ℝ^3) (i : ι) :
    familyRepresentative f x i = baseRepresentative (f i) x :=
  rfl

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The field of a finite family of functions of `H¹(ℝ³)` is square integrable. -/
theorem memLp_two_familyRepresentative (f : ι → H¹(ℝ^3)) :
    MemLp (familyRepresentative f) 2 volume := by
  refine memLp_piLp_iff.mpr fun i ↦ ?_
  have hi := Lp.memLp (wkpBaseCoordinateCLM (f i))
  simp only [domainMeasure, Measure.restrict_univ] at hi
  exact hi

/-- The field of a finite family of functions of `H¹(ℝ³)` lies in `L⁶`, since each member does
(`memLp_six_H1`). -/
theorem memLp_six_familyRepresentative (f : ι → H¹(ℝ^3)) :
    MemLp (familyRepresentative f) 6 volume := by
  refine memLp_piLp_iff.mpr fun i ↦ ?_
  have hi := memLp_six_H1 (f i)
  simp only [domainMeasure, Measure.restrict_univ, ENNReal.ofReal_ofNat] at hi
  exact hi

/-- The `L²` norm of the field of a finite family is `(∑ᵢ ‖fᵢ‖₂²)^{1/2}`. -/
theorem toReal_eLpNorm_two_familyRepresentative (f : ι → H¹(ℝ^3)) :
    (eLpNorm (familyRepresentative f) 2 volume).toReal =
      √(∑ i, ‖wkpBaseCoordinateCLM (f i)‖ ^ 2) := by
  have hint (i : ι) : Integrable (fun x ↦ familyRepresentative f x i ^ 2) := by
    have hi := Lp.memLp (wkpBaseCoordinateCLM (f i))
    simp only [domainMeasure, Measure.restrict_univ] at hi
    exact hi.integrable_sq
  have hcomp (i : ι) :
      ∫ x, familyRepresentative f x i ^ 2 = ‖wkpBaseCoordinateCLM (f i)‖ ^ 2 := by
    rw [Lp.norm_sq_eq_integral_sq]
    simp only [domainMeasure, Measure.restrict_univ]
    rfl
  have hsq : ∫ x, ‖familyRepresentative f x‖ ^ 2 = ∑ i, ‖wkpBaseCoordinateCLM (f i)‖ ^ 2 := by
    simp_rw [EuclideanSpace.real_norm_sq_eq]
    rw [integral_finsetSum _ fun i _ ↦ hint i]
    exact Finset.sum_congr rfl fun i _ ↦ hcomp i
  have h := integral_norm_pow_eq_lpNorm_pow
    (memLp_two_familyRepresentative f).aestronglyMeasurable (by norm_num : 0 < (2 : ℕ))
  simp only [Nat.cast_ofNat] at h
  rw [hsq, ← toReal_eLpNorm] at h
  rw [h, Real.sqrt_sq ENNReal.toReal_nonneg]

/-- **The sharp Sobolev inequality for fields with `m` components**, from the scalar inequality
`toReal_eLpNorm_six_le_sharp`:
for a finite family `f` of functions of `H¹(ℝ³)`, `‖f‖₆ ≤ K_s ‖∇f‖₂`, where `‖f‖₆` is the `L⁶`
norm of the length of the field and `‖∇f‖₂² = ∑ᵢ ‖∇fᵢ‖₂²`.

Hou, Wang and Yang obtain this from the scalar inequality for `|f|` and `|∇|f|| ≤ |∇f|`. Here
the scalar inequality is applied to each component, and Minkowski's inequality in `L³` for the
squares of the components (`MeasureTheory.eLpNorm_euclidean_rpow_two_le_sum`) gives

`‖f‖₆² = ‖∑ᵢ fᵢ²‖₃ ≤ ∑ᵢ ‖fᵢ‖₆² ≤ K_s² ∑ᵢ ‖∇fᵢ‖₂² = K_s² ‖∇f‖₂²`. -/
theorem toReal_eLpNorm_six_familyRepresentative_le (f : ι → H¹(ℝ^3)) :
    (eLpNorm (familyRepresentative f) 6 volume).toReal ≤ sharpSobolevConstant 3 *
      √(∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖ ^ 2) := by
  have hK : 0 ≤ sharpSobolevConstant 3 := (sharpSobolevConstant_pos le_rfl).le
  have hN2 : √(∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖ ^ 2) ^ 2 =
      ∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
  have hcomp (i : ι) : eLpNorm (fun x ↦ familyRepresentative f x i) 6 volume ≤
      ENNReal.ofReal
        (sharpSobolevConstant 3 * ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖) := by
    rw [ENNReal.le_ofReal_iff_toReal_le
      (memLp_piLp_iff.mp (memLp_six_familyRepresentative f) i).eLpNorm_ne_top
      (mul_nonneg hK (norm_nonneg _))]
    rw [sharpSobolevConstant_three]
    exact toReal_eLpNorm_six_le_sharp (f i)
  have hsq : (sharpSobolevConstant 3 *
      √(∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖ ^ 2)) ^ 2 = ∑ i,
        (sharpSobolevConstant 3 * ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖) ^ 2 := by
    rw [mul_pow, hN2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (mul_pow _ _ _).symm
  have hmain : eLpNorm (familyRepresentative f) 6 volume ^ (2 : ℝ) ≤
      ENNReal.ofReal ((sharpSobolevConstant 3 *
        √(∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖ ^ 2)) ^ 2) := by
    calc eLpNorm (familyRepresentative f) 6 volume ^ (2 : ℝ)
        ≤ ∑ i, eLpNorm (fun x ↦ familyRepresentative f x i) 6 volume ^ (2 : ℝ) :=
          eLpNorm_euclidean_rpow_two_le_sum
            (memLp_two_familyRepresentative f).aestronglyMeasurable (p := 3) (by norm_num)
            (by norm_num)
      _ ≤ ∑ i, ENNReal.ofReal (sharpSobolevConstant 3 *
            ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖) ^ (2 : ℝ) :=
          Finset.sum_le_sum fun i _ ↦ ENNReal.rpow_le_rpow (hcomp i) (by norm_num)
      _ = _ := by
          rw [hsq, ENNReal.ofReal_sum_of_nonneg fun i _ ↦ sq_nonneg _]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [ENNReal.rpow_two, ENNReal.ofReal_pow (mul_nonneg hK (norm_nonneg _))]
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmain
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (sq_nonneg _), Real.rpow_two] at h2
  exact (pow_le_pow_iff_left₀ ENNReal.toReal_nonneg (mul_nonneg hK (Real.sqrt_nonneg _))
    two_ne_zero).mp h2

/-- **The product estimate (A.1) of Hou, Wang and Yang** (their Lemma 6), from the sharp
Sobolev inequality: for `f` in `H¹(ℝ³; ℝᵐ)` and `g` in `H¹(ℝ³; ℝᵏ)`, given as finite families
of functions of `H¹(ℝ³)`,

`‖f g‖₂ ≤ K₄ ‖∇f‖₂ ‖g‖₂^{1/2} ‖∇g‖₂^{1/2}`, `K₄ = 2 / (3^{3/4} π)`.

Here `f g` is the tensor product, whose length at `x` is the product of the lengths of `f x`
and `g x`, and `‖g‖₂² = ∑ᵢ ‖gᵢ‖₂²`, `‖∇g‖₂² = ∑ᵢ ‖∇gᵢ‖₂²`. This constant enters the smallness
conditions (4.94) and (4.108) of the paper.

The proof is `‖f g‖₂ ≤ ‖f‖₆ ‖g‖₂^{1/2} ‖g‖₆^{1/2}` (`MeasureTheory.eLpNorm_norm_mul_norm_two_le`),
then the Sobolev inequality for `f` and for `g`, and `K_s * K_s ^ (1 / 2) = K₄`. -/
theorem toReal_eLpNorm_norm_mul_norm_familyRepresentative_le (f : ι → H¹(ℝ^3)) (g : κ → H¹(ℝ^3)) :
    (eLpNorm (fun x ↦ ‖familyRepresentative f x‖ * ‖familyRepresentative g x‖) 2
        volume).toReal ≤
      sobolevProductConstantThree *
        √(∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖ ^ 2) *
        √(∑ i, ‖wkpBaseCoordinateCLM (g i)‖ ^ 2) ^ (1 / 2 : ℝ) *
        √(∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (g i)‖ ^ 2) ^ (1 / 2 : ℝ) := by
  have hK : 0 ≤ sharpSobolevConstant 3 := (sharpSobolevConstant_pos le_rfl).le
  have hf6 := memLp_six_familyRepresentative f
  have hg2 := memLp_two_familyRepresentative g
  have hg6 := memLp_six_familyRepresentative g
  have hfin : eLpNorm (familyRepresentative f) 6 volume *
      (eLpNorm (familyRepresentative g) 2 volume ^ (1 / 2 : ℝ) *
        eLpNorm (familyRepresentative g) 6 volume ^ (1 / 2 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top hf6.eLpNorm_ne_top
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hg2.eLpNorm_ne_top)
        (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hg6.eLpNorm_ne_top))
  have h := ENNReal.toReal_mono hfin
    (eLpNorm_norm_mul_norm_two_le hf6.aestronglyMeasurable hg2.aestronglyMeasurable)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
    toReal_eLpNorm_two_familyRepresentative] at h
  have hf := toReal_eLpNorm_six_familyRepresentative_le f
  have hg := toReal_eLpNorm_six_familyRepresentative_le g
  have hm : 0 ≤ √(∑ i, ‖wkpBaseCoordinateCLM (g i)‖ ^ 2) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hg' : (eLpNorm (familyRepresentative g) 6 volume).toReal ^ (1 / 2 : ℝ) ≤
      sharpSobolevConstant 3 ^ (1 / 2 : ℝ) *
        √(∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (g i)‖ ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.mul_rpow hK (Real.sqrt_nonneg _)]
    exact Real.rpow_le_rpow ENNReal.toReal_nonneg hg (by norm_num)
  calc _ ≤ (eLpNorm (familyRepresentative f) 6 volume).toReal *
          (√(∑ i, ‖wkpBaseCoordinateCLM (g i)‖ ^ 2) ^ (1 / 2 : ℝ) *
            (eLpNorm (familyRepresentative g) 6 volume).toReal ^ (1 / 2 : ℝ)) := h
    _ ≤ sharpSobolevConstant 3 *
          √(∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖ ^ 2) *
          (√(∑ i, ‖wkpBaseCoordinateCLM (g i)‖ ^ 2) ^ (1 / 2 : ℝ) *
            (sharpSobolevConstant 3 ^ (1 / 2 : ℝ) *
              √(∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (g i)‖ ^ 2) ^ (1 / 2 : ℝ))) :=
        mul_le_mul hf (mul_le_mul_of_nonneg_left hg' hm)
          (mul_nonneg hm (Real.rpow_nonneg ENNReal.toReal_nonneg _))
          (mul_nonneg hK (Real.sqrt_nonneg _))
    _ = sharpSobolevConstant 3 * sharpSobolevConstant 3 ^ (1 / 2 : ℝ) *
          √(∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖ ^ 2) *
          √(∑ i, ‖wkpBaseCoordinateCLM (g i)‖ ^ 2) ^ (1 / 2 : ℝ) *
          √(∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (g i)‖ ^ 2) ^ (1 / 2 : ℝ) := by
        ring
    _ = _ := by rw [sharpSobolevConstant_three_mul_rpow_half]

/-- **The first `L⁴` bound of Lemma 6** of Hou, Wang and Yang, from the sharp Sobolev
inequality: for `f` in `H¹(ℝ³; ℝᵐ)`,

`‖f‖₄² ≤ K₄ ‖f‖₂^{1/2} ‖∇f‖₂^{3/2}`, `K₄ = 2 / (3^{3/4} π)`.

It is (A.1) with `g = f`, since `‖f f‖₂ = ‖|f|²‖₂ = ‖f‖₄²`. -/
theorem toReal_eLpNorm_four_familyRepresentative_sq_le (f : ι → H¹(ℝ^3)) :
    (eLpNorm (familyRepresentative f) 4 volume).toReal ^ 2 ≤
      sobolevProductConstantThree * √(∑ i, ‖wkpBaseCoordinateCLM (f i)‖ ^ 2) ^ (1 / 2 : ℝ) *
        √(∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖ ^ 2) ^ (3 / 2 : ℝ) := by
  have h := toReal_eLpNorm_norm_mul_norm_familyRepresentative_le f f
  rw [eLpNorm_norm_mul_norm_self (memLp_two_familyRepresentative f).aestronglyMeasurable,
    ← ENNReal.toReal_rpow, Real.rpow_two] at h
  calc _ ≤ _ := h
    _ = _ := by
        rw [rpow_three_halves_eq_mul_rpow_half (Real.sqrt_nonneg _)]
        ring

/-- **The second `L⁴` bound of Lemma 6** of Hou, Wang and Yang, from the sharp Sobolev
inequality: for `f` in `H¹(ℝ³; ℝᵐ)`,

`‖f‖₄² ≤ (‖f‖₂² + ‖∇f‖₂²) / (2π)`.

The proof is the first bound, the weighted mean inequality
`a^{1/2} b^{3/2} ≤ (3^{3/4} / 4) (a² + b²)` and `(3^{3/4} / 4) K₄ = 1 / (2π)`. -/
theorem toReal_eLpNorm_four_familyRepresentative_sq_le_add (f : ι → H¹(ℝ^3)) :
    (eLpNorm (familyRepresentative f) 4 volume).toReal ^ 2 ≤
      (∑ i, ‖wkpBaseCoordinateCLM (f i)‖ ^ 2 +
        ∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖ ^ 2) / (2 * π) := by
  have ha : √(∑ i, ‖wkpBaseCoordinateCLM (f i)‖ ^ 2) ^ 2 =
      ∑ i, ‖wkpBaseCoordinateCLM (f i)‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
  have hb : √(∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖ ^ 2) ^ 2 =
      ∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖ ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)
  calc _ ≤ sobolevProductConstantThree *
          √(∑ i, ‖wkpBaseCoordinateCLM (f i)‖ ^ 2) ^ (1 / 2 : ℝ) *
          √(∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖ ^ 2) ^ (3 / 2 : ℝ) :=
        toReal_eLpNorm_four_familyRepresentative_sq_le f
    _ = sobolevProductConstantThree *
          (√(∑ i, ‖wkpBaseCoordinateCLM (f i)‖ ^ 2) ^ (1 / 2 : ℝ) *
            √(∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖ ^ 2) ^ (3 / 2 : ℝ)) :=
        mul_assoc _ _ _
    _ ≤ sobolevProductConstantThree * (3 ^ (3 / 4 : ℝ) / 4 *
          (√(∑ i, ‖wkpBaseCoordinateCLM (f i)‖ ^ 2) ^ 2 +
            √(∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖ ^ 2) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (rpow_half_mul_rpow_three_halves_le (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          sobolevProductConstantThree_pos.le
    _ = 3 ^ (3 / 4 : ℝ) / 4 * sobolevProductConstantThree *
          (∑ i, ‖wkpBaseCoordinateCLM (f i)‖ ^ 2 +
            ∑ i, ‖NavierStokes.Stationary.scalarGradientCLM (f i)‖ ^ 2) := by
        rw [ha, hb]
        ring
    _ = _ := by
        rw [three_rpow_div_four_mul_sobolevProductConstantThree]
        ring

end SobolevSpace.Inequalities

namespace NavierStokes.Stationary

/-! ## Velocity fields of `H¹(ℝ³)³` -/

/-- The squared gradient norm of a velocity field is the sum of the squared gradient norms of
its components: `‖∇v‖₂² = ∑ᵢ ‖∇vᵢ‖₂²`. -/
theorem norm_gradientCLM_sq {n : ℕ} (v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) :
    ‖gradientCLM v‖ ^ 2 = ∑ i : Fin n, ‖scalarGradientCLM (v i)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

/-- The squared mass norm of a velocity field is the sum of the squared `L²` norms of its
components: `‖v‖₂² = ∑ᵢ ‖vᵢ‖₂²`. -/
theorem norm_massCLM_sq {n : ℕ} (v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) :
    ‖massCLM v‖ ^ 2 = ∑ i : Fin n, ‖wkpBaseCoordinateCLM (v i)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

/-- The `L²` norm of the representative of a field of `H¹(ℝⁿ)ⁿ` is its mass norm:
`‖v‖₂ = ‖massCLM v‖`. This is `integral_norm_representative_sq` for the seminorm `eLpNorm`. -/
theorem toReal_eLpNorm_two_representative {n : ℕ} (v : PiLp 2 (fun _ : Fin n ↦ H¹(ℝ^n))) :
    (eLpNorm (representative v) 2 volume).toReal = ‖massCLM v‖ := by
  have h := integral_norm_pow_eq_lpNorm_pow (memLp_representative v).aestronglyMeasurable
    (by norm_num : 0 < (2 : ℕ))
  simp only [Nat.cast_ofNat] at h
  rw [integral_norm_representative_sq v, ← toReal_eLpNorm] at h
  exact (pow_left_inj₀ ENNReal.toReal_nonneg (norm_nonneg _) two_ne_zero).mp h.symm

local notation "E" => PiLp 2 (fun _ : Fin 3 ↦ H¹(ℝ^3))

/-- The representative of a velocity field of `H¹(ℝ³)³` is the field of the family of its three
components. -/
theorem representative_eq_familyRepresentative (v : E) :
    representative v = familyRepresentative fun i ↦ v i :=
  rfl

/-- The representative of every field of `H¹(ℝ³)³` lies in `L⁶(ℝ³; ℝ³)`. -/
theorem memLp_six_representative (v : E) : MemLp (representative v) 6 volume :=
  memLp_six_familyRepresentative fun i ↦ v i

/-- **The sharp Sobolev inequality for velocity fields**: every `v` in `H¹(ℝ³)³` has
`‖v‖₆ ≤ K_s ‖∇v‖₂`. The case of three components of
`SobolevSpace.Inequalities.toReal_eLpNorm_six_familyRepresentative_le`. -/
theorem toReal_eLpNorm_six_representative_le (v : E) :
    (eLpNorm (representative v) 6 volume).toReal ≤
      sharpSobolevConstant 3 * ‖gradientCLM v‖ := by
  have h := toReal_eLpNorm_six_familyRepresentative_le fun i ↦ v i
  rw [← norm_gradientCLM_sq v, Real.sqrt_sq (norm_nonneg _)] at h
  exact h

/-- **The product estimate (A.1) for velocity fields**: for `f`, `g` in `H¹(ℝ³)³`,

`‖f g‖₂ ≤ K₄ ‖∇f‖₂ ‖g‖₂^{1/2} ‖∇g‖₂^{1/2}`,

with the norms `‖gradientCLM f‖`, `‖massCLM g‖` and `‖gradientCLM g‖`. The case of three
components of `SobolevSpace.Inequalities.toReal_eLpNorm_norm_mul_norm_familyRepresentative_le`. -/
theorem toReal_eLpNorm_norm_mul_norm_representative_le (f g : E) :
    (eLpNorm (fun x ↦ ‖representative f x‖ * ‖representative g x‖) 2 volume).toReal ≤
      sobolevProductConstantThree * ‖gradientCLM f‖ * ‖massCLM g‖ ^ (1 / 2 : ℝ) *
        ‖gradientCLM g‖ ^ (1 / 2 : ℝ) := by
  have h := toReal_eLpNorm_norm_mul_norm_familyRepresentative_le (fun i ↦ f i)
    (fun i ↦ g i)
  rw [← norm_gradientCLM_sq f, ← norm_massCLM_sq g, ← norm_gradientCLM_sq g] at h
  simp only [Real.sqrt_sq_eq_abs, abs_norm] at h
  exact h

/-- **The first `L⁴` bound of Lemma 6 for velocity fields**: for `f` in `H¹(ℝ³)³`,
`‖f‖₄² ≤ K₄ ‖f‖₂^{1/2} ‖∇f‖₂^{3/2}`. -/
theorem toReal_eLpNorm_four_representative_sq_le (f : E) :
    (eLpNorm (representative f) 4 volume).toReal ^ 2 ≤
      sobolevProductConstantThree * ‖massCLM f‖ ^ (1 / 2 : ℝ) *
        ‖gradientCLM f‖ ^ (3 / 2 : ℝ) := by
  have h := toReal_eLpNorm_four_familyRepresentative_sq_le fun i ↦ f i
  rw [← norm_massCLM_sq f, ← norm_gradientCLM_sq f] at h
  simp only [Real.sqrt_sq_eq_abs, abs_norm] at h
  exact h

/-- **The second `L⁴` bound of Lemma 6 for velocity fields**: for `f` in `H¹(ℝ³)³`,
`‖f‖₄² ≤ (‖f‖₂² + ‖∇f‖₂²) / (2π)`. The right side is `‖f‖² / (2π)` for the norm of `H¹(ℝ³)³`,
by `norm_sq_eq_mass_add_gradient`. -/
theorem toReal_eLpNorm_four_representative_sq_le_add (f : E) :
    (eLpNorm (representative f) 4 volume).toReal ^ 2 ≤
      (‖massCLM f‖ ^ 2 + ‖gradientCLM f‖ ^ 2) / (2 * π) := by
  have h := toReal_eLpNorm_four_familyRepresentative_sq_le_add fun i ↦ f i
  rw [← norm_massCLM_sq f, ← norm_gradientCLM_sq f] at h
  exact h

end NavierStokes.Stationary
