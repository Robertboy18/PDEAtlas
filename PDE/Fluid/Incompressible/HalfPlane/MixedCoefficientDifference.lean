/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.Incompressible.HalfPlane.WeightedStreamBounds
import PDE.Analysis.Calculus.HalfSpaceGluing

/-!
# Differences of mixed coefficients and mixed derivatives at the wall

Facts used to compare the strain of a stream function with the mixed coefficient
`c_f = (4/π) ∫_{ℝ²₊₊} K₁ f` of a source `f` in the weighted class of Chen and Hou, Part I,
Lemma 6.5; `c_f = -c_ω(f)` for the functional `c_ω` of Part I (5.67). The derivatives at a
boundary point are determined by the values on the closed half-plane, which has unique
derivatives.

## Main results

* `integrableOn_hessianKernel_mul_of_weighted_le`: under the weighted bound
  `|f(y)| (|y|^{-α} + |y|^β) ≤ M` of Lemma 6.5 the integrand `K₁ f` is integrable on the quadrant.
* `mixedCoefficient_sub`: the mixed coefficient is additive on such sources,
  `c_{f - g} = c_f - c_g`.
* `mixedDeriv_eq_of_eqOn_closedUpperHalfPlane`: two functions that agree on the closed upper
  half-plane, are differentiable at its points, and whose `x₁`-derivatives are differentiable at
  the origin have the same mixed derivative `∂₀∂₁` at the origin.
* `abs_mul_add_le_of_le_min`: a bound `|f(y)| ≤ K min(|y|^a, |y|^{-b})` gives the weighted bound
  `|f(y)| (|y|^{-a} + |y|^b) ≤ 2 K` away from the origin.

## References

* J. Chen and T. Y. Hou, "Stable nearly self-similar blowup of the 2D Boussinesq and 3D Euler
  equations with smooth data I: Analysis", arXiv:2210.07191v4, Lemma 6.5, p. 98, and (5.67), p. 78.
  <https://arxiv.org/abs/2210.07191v4>
-/

@[expose] public section

noncomputable section

namespace IncompressibleFlow

open MeasureTheory Filter Topology Set Metric GreenFunction PotentialTheory.Planar

set_option linter.missingDocs true

variable {f g : ℝ^2 → ℝ}

/-- **Integrability of the mixed-coefficient integrand** under the weighted bound of Lemma 6.5:
for `f` continuous and `|f(y)| (|y|^{-α} + |y|^β) ≤ M` on the open upper half-plane with
`α, β > 0`, `K₁ f` is integrable on the quadrant. -/
theorem integrableOn_hessianKernel_mul_of_weighted_le (hf : Continuous f) {α β M : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hM : ∀ y : ℝ^2, 0 < y 1 → |f y| * (‖y‖ ^ (-α) + ‖y‖ ^ β) ≤ M) :
    IntegrableOn (fun y ↦ hessianKernel 0 1 y * f y) quadrant := by
  have hM0 := nonneg_of_weighted_le hM
  have hm : AEStronglyMeasurable (fun y ↦ hessianKernel 0 1 y * f y) :=
    (measurable_hessianKernel 0 1).aestronglyMeasurable.mul hf.aestronglyMeasurable
  have hB : MeasurableSet (ball (0 : ℝ^2) 1) := measurableSet_ball
  have h1le : ∀ y ∈ quadrant ∩ ball (0 : ℝ^2) 1,
      |hessianKernel 0 1 y * f y| ≤ M / 2 * ‖y‖ ^ (α - 2) := fun y hy ↦
    abs_hessianKernel_mul_le hM0 (abs_le_mul_rpow_of_weighted_le hM hy.1.2)
  have h2le : ∀ y ∈ quadrant \ ball (0 : ℝ^2) 1,
      |hessianKernel 0 1 y * f y| ≤ M / 2 * ‖y‖ ^ ((1 - β) - 3) := fun y hy ↦ by
    rw [show (1 - β) - 3 = -β - 2 by ring]
    exact abs_hessianKernel_mul_le hM0 (abs_le_mul_rpow_neg_of_weighted_le hM hy.1.2)
  have hT1 : ∫⁻ y in ball (0 : ℝ^2) 1, ENNReal.ofReal (M / 2 * ‖y‖ ^ (α - 2)) ≤
      ENNReal.ofReal (M / 2 * (2 * Real.pi / α)) := by
    rw [lintegral_ball_zero_rpow (by positivity) zero_le_one hα, Real.one_rpow, mul_one]
  have hT2 : ∫⁻ y in (ball (0 : ℝ^2) 1)ᶜ, ENNReal.ofReal (M / 2 * ‖y‖ ^ ((1 - β) - 3)) ≤
      ENNReal.ofReal (M / 2 * (2 * Real.pi / β)) := by
    rw [lintegral_compl_ball_zero_rpow (by positivity) one_pos (by linarith), Real.one_rpow]
    simp
  have hS := measurableSet_quadrant
  have hI1 := integrableOn_of_abs_le_of_lintegral_le (hS.inter hB) inter_subset_right
    hm.restrict h1le hT1
  have hI2 := integrableOn_of_abs_le_of_lintegral_le (hS.diff hB) (fun y hy ↦ hy.2)
    hm.restrict h2le hT2
  have := hI1.union hI2
  rwa [inter_union_sdiff] at this

/-- **The mixed coefficient is additive on weighted sources**: `c_{f - g} = c_f - c_g` for
continuous `f`, `g` with the weighted bounds of Lemma 6.5. -/
theorem mixedCoefficient_sub (hf : Continuous f) (hg : Continuous g) {α β M N : ℝ}
    (hα : 0 < α) (hβ : 0 < β)
    (hMf : ∀ y : ℝ^2, 0 < y 1 → |f y| * (‖y‖ ^ (-α) + ‖y‖ ^ β) ≤ M)
    (hMg : ∀ y : ℝ^2, 0 < y 1 → |g y| * (‖y‖ ^ (-α) + ‖y‖ ^ β) ≤ N) :
    mixedCoefficient (fun y ↦ f y - g y) = mixedCoefficient f - mixedCoefficient g := by
  have hIf := integrableOn_hessianKernel_mul_of_weighted_le hf hα hβ hMf
  have hIg := integrableOn_hessianKernel_mul_of_weighted_le hg hα hβ hMg
  unfold mixedCoefficient
  rw [← mul_sub, ← integral_sub hIf hIg]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only
  ring

/-- **A min-power bound gives the weighted bound of Lemma 6.5**: if
`|f(y)| ≤ K min(|y|^a, |y|^{-b})` at a point `y ≠ 0`, then `|f(y)| (|y|^{-a} + |y|^b) ≤ 2 K`. -/
theorem abs_mul_add_le_of_le_min {a b K : ℝ} {y : ℝ^2} (hy : y ≠ 0)
    (h : |f y| ≤ K * min (‖y‖ ^ a) (‖y‖ ^ (-b))) :
    |f y| * (‖y‖ ^ (-a) + ‖y‖ ^ b) ≤ 2 * K := by
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hK : 0 ≤ K := by
    by_contra hK
    push Not at hK
    have : K * min (‖y‖ ^ a) (‖y‖ ^ (-b)) < 0 :=
      mul_neg_of_neg_of_pos hK (lt_min (Real.rpow_pos_of_pos hn _) (Real.rpow_pos_of_pos hn _))
    linarith [abs_nonneg (f y)]
  have h1 : |f y| * ‖y‖ ^ (-a) ≤ K := by
    calc |f y| * ‖y‖ ^ (-a) ≤ K * ‖y‖ ^ a * ‖y‖ ^ (-a) :=
          mul_le_mul_of_nonneg_right (h.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hK))
            (Real.rpow_nonneg hn.le _)
      _ = K := by rw [mul_assoc, ← Real.rpow_add hn, add_neg_cancel, Real.rpow_zero, mul_one]
  have h2 : |f y| * ‖y‖ ^ b ≤ K := by
    calc |f y| * ‖y‖ ^ b ≤ K * ‖y‖ ^ (-b) * ‖y‖ ^ b :=
          mul_le_mul_of_nonneg_right (h.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hK))
            (Real.rpow_nonneg hn.le _)
      _ = K := by rw [mul_assoc, ← Real.rpow_add hn, neg_add_cancel, Real.rpow_zero, mul_one]
  rw [mul_add]
  linarith

/-- Two functions that agree on the closed upper half-plane and are differentiable at one of its
points have the same derivative there. -/
theorem fderiv_eq_of_eqOn_closedUpperHalfPlane {F G : ℝ^2 → ℝ}
    (heq : EqOn F G {y : ℝ^2 | 0 ≤ y 1}) {x : ℝ^2} (hx : 0 ≤ x 1) (hF : DifferentiableAt ℝ F x)
    (hG : DifferentiableAt ℝ G x) : fderiv ℝ F x = fderiv ℝ G x := by
  have hu : UniqueDiffWithinAt ℝ {y : ℝ^2 | 0 ≤ y 1} x :=
    PDE.Analysis.uniqueDiffOn_coordinateHalfSpace (1 : Fin 2) x hx
  rw [← hF.fderivWithin hu, ← hG.fderivWithin hu]
  exact fderivWithin_congr heq (heq hx)

/-- **The mixed derivative at the origin from the closed half-plane**: if `F` and `G` agree on
the closed upper half-plane, are differentiable at its points, and their `x₁`-derivatives are
differentiable at the origin, then `∂₀∂₁F(0) = ∂₀∂₁G(0)`. -/
theorem mixedDeriv_eq_of_eqOn_closedUpperHalfPlane {F G : ℝ^2 → ℝ}
    (heq : EqOn F G {y : ℝ^2 | 0 ≤ y 1})
    (hF : ∀ y : ℝ^2, 0 ≤ y 1 → DifferentiableAt ℝ F y)
    (hG : ∀ y : ℝ^2, 0 ≤ y 1 → DifferentiableAt ℝ G y)
    (hF1 : DifferentiableAt ℝ (∂[(1 : Fin 2)] F) 0)
    (hG1 : DifferentiableAt ℝ (∂[(1 : Fin 2)] G) 0) :
    (∂[(0 : Fin 2)] (∂[(1 : Fin 2)] F)) 0 = (∂[(0 : Fin 2)] (∂[(1 : Fin 2)] G)) 0 := by
  have h1 : EqOn (∂[(1 : Fin 2)] F) (∂[(1 : Fin 2)] G) {y : ℝ^2 | 0 ≤ y 1} := fun y hy ↦ by
    change fderiv ℝ F y _ = fderiv ℝ G y _
    rw [fderiv_eq_of_eqOn_closedUpperHalfPlane heq hy (hF y hy) (hG y hy)]
  change fderiv ℝ (∂[(1 : Fin 2)] F) 0 _ = fderiv ℝ (∂[(1 : Fin 2)] G) 0 _
  rw [fderiv_eq_of_eqOn_closedUpperHalfPlane h1 (by simp) hF1 hG1]

end IncompressibleFlow
