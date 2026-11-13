/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Integrated.GardingBounds
public import PDE.Parabolic.Heat.Variational.MeasurableExistence

/-!
# Data-only parabolic estimates for raw measurable coefficients

The three-term constant depends only on the ellipticity, coefficient bound,
dimension, and interval length. The forcing has its original spatial L² norm.
The estimate is Evans's (20) in §7.1.2, Theorem 2, which he proves for the Galerkin
approximations; `weakSolution_three_term_bound` states it for the weak solution.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §7.1.2, Theorem 2 (Energy estimates), (20), pp. 376-378.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

open Filter MeasureTheory Set
open scoped ENNReal NNReal

namespace HeatEquation.Variational.BoundedMeasurableCoefficients

open PDE.Analysis.Evolution SobolevSpace SobolevSpace.GraphSpace

attribute [local instance] h10NormedAddCommGroup h10InnerProductSpace

variable {n : ℕ} {Ω : Set (ℝ^n)} {a b : ℝ}

/-- The pivot load map is contractive on Bochner L². -/
theorem norm_pivotLoadLp_le (hΩopen : IsOpen Ω)
    (f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))) :
    ‖(h10L2GelfandTriple hΩopen).pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f‖ ≤
      ‖f‖ := by
  have hnorm : ‖(h10L2GelfandTriple hΩopen).pivotToDual‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ by
      simpa only [one_mul] using norm_pivotLoad_le hΩopen v
  exact ((h10L2GelfandTriple hΩopen).pivotToDual.norm_compLp_le f).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hnorm (norm_nonneg f))

/-- The three-term estimate of Evans's (20) for the weak solution, in terms of the original
L² data. -/
theorem weakSolution_three_term_bound
    (C : BoundedMeasurableCoefficients n Ω (volume.restrict (Ioc a b)))
    (hΩopen : IsOpen Ω) (hab : a ≤ b) {alpha : ℝ} (halpha : 0 < alpha)
    {f : Lp (DerivLp n 2 Ω) 2 (volume.restrict (Ioc a b))} {uInit : DerivLp n 2 Ω}
    (U : GardingWeakSolutionOn (h10L2GelfandTriple hΩopen) C.form
      (fun t ↦ (h10L2GelfandTriple hΩopen).pivotToDual (f t)) uInit a b
      (alpha / 2) (coerciveShift (n := n) alpha C.bound C.bound)) :
    ∀ t ∈ Icc a b,
      ‖U.evolution.representative t‖ + ‖U.state‖ + ‖U.derivative‖ ≤
        gardingThreeTermConstant (alpha / 2) (coerciveShift (n := n) alpha C.bound C.bound)
          (b - a) C.formBound 1 * (‖uInit‖ + ‖f‖) := by
  let T := h10L2GelfandTriple hΩopen
  let ell := T.pivotToDual.compLpL 2 (volume.restrict (Ioc a b)) f
  have hell : (ell : ℝ → StrongDual ℝ (H¹₀(Ω))) =ᵐ[volume.restrict (Ioc a b)]
      fun t ↦ T.pivotToDual (f t) := T.pivotToDual.coeFn_compLpL f
  have hgamma : 0 ≤ coerciveShift (n := n) alpha C.bound C.bound := by
    unfold coerciveShift gardingMass
    positivity
  have hC : 0 ≤ gardingThreeTermConstant (alpha / 2)
      (coerciveShift (n := n) alpha C.bound C.bound) (b - a) C.formBound 1 := by
    unfold gardingThreeTermConstant
    positivity
  intro t ht
  have h := (U.congrForcing hell.symm).three_term_bound hab (half_pos halpha) hgamma
    C.aestronglyMeasurable_form_apply C.formBound (Eventually.of_forall C.norm_form_le) t ht
  exact h.trans (mul_le_mul_of_nonneg_left
    (add_le_add_right (norm_pivotLoadLp_le hΩopen f) _) hC)

end HeatEquation.Variational.BoundedMeasurableCoefficients
