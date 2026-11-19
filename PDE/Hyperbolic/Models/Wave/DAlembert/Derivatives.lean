/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.DAlembert.Formula
public import PDE.FDeriv.PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Derivatives of the one-dimensional d'Alembert formula

For displacement `g ∈ C²` and velocity `h ∈ C¹`, the d'Alembert formula is
`C²` in spacetime. Its two pure second derivatives agree, giving the wave
equation. The first derivatives follow from the chain rule and the fundamental
theorem of calculus at the two characteristic endpoints `x ± t`. This is the calculation that
proves Evans, §2.4.1, Theorem 1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (partialDeriv)

namespace WaveEquation

open scoped Interval

/-- The characteristic coordinate `x + s t`, with time in the zeroth coordinate. -/
noncomputable def characteristicCoordinate (s : ℝ) : ℝ^2 →L[ℝ] ℝ :=
  EuclideanSpace.proj (1 : Fin 2) + s • EuclideanSpace.proj (0 : Fin 2)

/-- The derivative of an integral with characteristic endpoints comes from its two endpoints. -/
theorem hasFDerivAt_characteristicIntegral (h : ℝ → ℝ) (hh : Continuous h) (p : ℝ^2) :
    HasFDerivAt (fun q : ℝ^2 ↦ ∫ y in (q 1 - q 0)..(q 1 + q 0), h y)
      (h (p 1 + p 0) • characteristicCoordinate 1 -
        h (p 1 - p 0) • characteristicCoordinate (-1)) p := by
  let L := (characteristicCoordinate (-1)).prod (characteristicCoordinate 1)
  have hi := (intervalIntegral.integral_hasFDerivAt (hh.intervalIntegrable (L p).1 (L p).2)
    hh.aestronglyMeasurable.stronglyMeasurableAtFilter
    hh.aestronglyMeasurable.stronglyMeasurableAtFilter
    hh.continuousAt hh.continuousAt).comp p L.hasFDerivAt
  convert hi using 1
  · ext q
    simp [L, characteristicCoordinate, sub_eq_add_neg]
  · ext q
    simp [L, characteristicCoordinate, mul_comm, sub_eq_add_neg, mul_add]

/-- The full spacetime derivative of d'Alembert's formula. Only one displacement derivative
and continuity of the velocity are needed for this first derivative. -/
theorem hasFDerivAt_dAlembertFormula
    (g h : ℝ → ℝ) (hg : Differentiable ℝ g) (hh : Continuous h) (p : ℝ^2) :
    HasFDerivAt (fun q : ℝ^2 ↦ dAlembertFormula g h (q 1) (q 0))
      ((1 / 2 : ℝ) •
          (deriv g (p 1 + p 0) • characteristicCoordinate 1 +
            deriv g (p 1 - p 0) • characteristicCoordinate (-1)) +
        (1 / 2 : ℝ) •
          (h (p 1 + p 0) • characteristicCoordinate 1 -
            h (p 1 - p 0) • characteristicCoordinate (-1))) p := by
  have hp := (hg (characteristicCoordinate 1 p)).hasDerivAt.comp_hasFDerivAt p
    (characteristicCoordinate 1).hasFDerivAt
  have hm := (hg (characteristicCoordinate (-1) p)).hasDerivAt.comp_hasFDerivAt p
    (characteristicCoordinate (-1)).hasFDerivAt
  convert (HasFDerivAt.const_mul (hp.add hm) (1 / 2 : ℝ)).add
    ((hasFDerivAt_characteristicIntegral h hh p).const_mul (1 / 2 : ℝ)) using 1 <;> ext q <;>
    simp [dAlembertFormula, characteristicCoordinate, Function.comp_def, sub_eq_add_neg]

private theorem hasFDerivAt_characteristicCombination (f g : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (s : ℝ) (p : ℝ^2) :
    HasFDerivAt
      (fun q ↦ (1 / 2 : ℝ) * (f (q 1 + q 0) + s * f (q 1 - q 0)) +
        (1 / 2 : ℝ) * (g (q 1 + q 0) - s * g (q 1 - q 0)))
      ((1 / 2 : ℝ) •
          (deriv f (p 1 + p 0) • characteristicCoordinate 1 +
            s • (deriv f (p 1 - p 0) • characteristicCoordinate (-1))) +
        (1 / 2 : ℝ) •
          (deriv g (p 1 + p 0) • characteristicCoordinate 1 -
            s • (deriv g (p 1 - p 0) • characteristicCoordinate (-1)))) p := by
  have hf' (v : ℝ) := (hf (characteristicCoordinate v p)).hasDerivAt.comp_hasFDerivAt p
    (characteristicCoordinate v).hasFDerivAt
  have hg' (v : ℝ) := (hg (characteristicCoordinate v p)).hasDerivAt.comp_hasFDerivAt p
    (characteristicCoordinate v).hasFDerivAt
  convert (HasFDerivAt.const_mul ((hf' 1).add (HasFDerivAt.const_mul (hf' (-1)) s)) (1 / 2 : ℝ)).add
    (HasFDerivAt.const_mul ((hg' 1).sub (HasFDerivAt.const_mul (hg' (-1)) s))
      (1 / 2 : ℝ)) using 1 <;> ext q <;>
    simp [characteristicCoordinate, Function.comp_def, sub_eq_add_neg]

/-- A `C¹` integrand has a `C²` primitive. This is the fundamental
theorem of calculus in the form needed by d'Alembert's integral term. -/
private theorem contDiff_two_intervalIntegral_right
    (h : ℝ → ℝ) (hh : ContDiff ℝ 1 h) :
    ContDiff ℝ 2 (fun u ↦ ∫ x in (0 : ℝ)..u, h x) := by
  apply (contDiff_succ_iff_deriv (n := 1)).2
  refine ⟨intervalIntegral.differentiable_integral_of_continuous hh.continuous, ?_, ?_⟩
  · simp
  · have hderiv : deriv (fun u ↦ ∫ x in (0 : ℝ)..u, h x) = h := by
      funext u
      exact intervalIntegral.deriv_integral_right (hh.continuous.intervalIntegrable 0 u)
        hh.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hh.continuous.continuousAt
    rw [hderiv]
    exact hh

/-- D'Alembert's formula is `C²` in spacetime for `C²` displacement and `C¹` velocity. -/
theorem contDiff_two_dAlembertFormula (g h : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) :
    ContDiff ℝ 2 (fun p : ℝ^2 ↦ dAlembertFormula g h (p 1) (p 0)) := by
  let F : ℝ → ℝ := fun u ↦ ∫ x in (0 : ℝ)..u, h x
  have hF : ContDiff ℝ 2 F := contDiff_two_intervalIntegral_right h hh
  have heq : (fun p : ℝ^2 ↦ dAlembertFormula g h (p 1) (p 0)) = fun p ↦ (1 / 2 : ℝ) *
          (g (characteristicCoordinate 1 p) + g (characteristicCoordinate (-1) p)) + (1 / 2 : ℝ) *
          (F (characteristicCoordinate 1 p) - F (characteristicCoordinate (-1) p)) := by
    ext p
    change (1 / 2 : ℝ) * (g (p 1 + p 0) + g (p 1 - p 0)) +
        (1 / 2 : ℝ) * (∫ y in (p 1 - p 0)..(p 1 + p 0), h y) =
      (1 / 2 : ℝ) * (g (p 1 + 1 * p 0) + g (p 1 + (-1) * p 0)) +
        (1 / 2 : ℝ) * ((∫ y in 0..(p 1 + 1 * p 0), h y) - ∫ y in 0..(p 1 + (-1) * p 0), h y)
    simp only [one_mul, neg_one_mul, ← sub_eq_add_neg]
    rw [intervalIntegral.integral_interval_sub_left (hh.continuous.intervalIntegrable 0 (p 1 + p 0))
      (hh.continuous.intervalIntegrable 0 (p 1 - p 0))]
  rw [heq]
  exact (contDiff_const.mul ((hg.fun_comp (characteristicCoordinate 1).contDiff).add
    (hg.fun_comp (characteristicCoordinate (-1)).contDiff))).add
    (contDiff_const.mul ((hF.fun_comp (characteristicCoordinate 1).contDiff).sub
      (hF.fun_comp (characteristicCoordinate (-1)).contDiff)))

/-- The time derivative averages the velocity and takes the difference of the displacement
derivatives at the two characteristic endpoints. -/
theorem partialDeriv_dAlembert_time
    (g h : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) (p : ℝ^2) :
    (∂[0] (fun q : ℝ^2 ↦ dAlembertFormula g h (q 1) (q 0))) p =
      (1 / 2 : ℝ) * (deriv g (p 1 + p 0) - deriv g (p 1 - p 0)) +
        (1 / 2 : ℝ) * (h (p 1 + p 0) + h (p 1 - p 0)) := by
  rw [partialDeriv, (hasFDerivAt_dAlembertFormula g h
    (hg.differentiable (by norm_num)) hh.continuous p).fderiv]
  simp [characteristicCoordinate, sub_eq_add_neg, mul_add]

/-- The space derivative averages the displacement derivative and takes the velocity difference
at the two characteristic endpoints. -/
theorem partialDeriv_dAlembert_space
    (g h : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) (p : ℝ^2) :
    (∂[1] (fun q : ℝ^2 ↦ dAlembertFormula g h (q 1) (q 0))) p =
      (1 / 2 : ℝ) * (deriv g (p 1 + p 0) + deriv g (p 1 - p 0)) +
        (1 / 2 : ℝ) * (h (p 1 + p 0) - h (p 1 - p 0)) := by
  rw [partialDeriv, (hasFDerivAt_dAlembertFormula g h
    (hg.differentiable (by norm_num)) hh.continuous p).fderiv]
  simp [characteristicCoordinate, sub_eq_add_neg, mul_add]

/-- The second time derivative is the sum of the averaged second displacement derivative and
the endpoint difference of the velocity derivative. -/
theorem partialDeriv2_dAlembert_time
    (g h : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) (p : ℝ^2) :
    (∂[0] (fun q ↦ (∂[0] (fun r : ℝ^2 ↦ dAlembertFormula g h (r 1) (r 0))) q)) p =
      (1 / 2 : ℝ) * (deriv (deriv g) (p 1 + p 0) + deriv (deriv g) (p 1 - p 0)) + (1 / 2 : ℝ) *
      (deriv h (p 1 + p 0) - deriv h (p 1 - p 0)) := by
  simp_rw [partialDeriv_dAlembert_time g h hg hh]
  have hd := hasFDerivAt_characteristicCombination (deriv g) h
    hg.differentiable_deriv_two (hh.differentiable (by norm_num)) (-1) p
  simp only [neg_one_mul, sub_neg_eq_add, ← sub_eq_add_neg] at hd
  rw [partialDeriv, hd.fderiv]
  simp [characteristicCoordinate, sub_eq_add_neg, mul_add]

/-- The second space derivative has the same formula as the second time derivative. -/
theorem partialDeriv2_dAlembert_space
    (g h : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) (p : ℝ^2) :
    (∂[1] (fun q ↦ (∂[1] (fun r : ℝ^2 ↦ dAlembertFormula g h (r 1) (r 0))) q)) p =
      (1 / 2 : ℝ) * (deriv (deriv g) (p 1 + p 0) + deriv (deriv g) (p 1 - p 0)) + (1 / 2 : ℝ) *
      (deriv h (p 1 + p 0) - deriv h (p 1 - p 0)) := by
  simp_rw [partialDeriv_dAlembert_space g h hg hh]
  have hd := hasFDerivAt_characteristicCombination (deriv g) h
    hg.differentiable_deriv_two (hh.differentiable (by norm_num)) 1 p
  simp only [one_mul, one_smul] at hd
  rw [partialDeriv, hd.fderiv]
  simp [characteristicCoordinate, sub_eq_add_neg, mul_add]

end WaveEquation
