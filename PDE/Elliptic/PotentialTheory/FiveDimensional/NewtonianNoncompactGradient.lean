/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Elliptic.PotentialTheory.FiveDimensional.NewtonianGradient
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import PDE.Elliptic.PotentialTheory.FundamentalSolution.LocalIntegrability

/-!
# First derivatives of noncompact Newtonian potentials

Absolute convergence at one anchor defines the Newtonian potential everywhere
for a continuous source. For a C¹ source, a compact cutoff handles the pole,
and a fixed integrable majorant permits differentiation of the remaining tail.
The result identifies the full Fréchet derivative and each coordinate derivative
with the absolutely convergent integral of the first-gradient kernel.
-/

@[expose] public section

open PDE (partialDeriv)

noncomputable section

open MeasureTheory
open scoped Distributions


/-!
The tail argument uses explicit kernel comparisons and the original Newtonian
integrand as its majorant. Vanishing on a ball keeps every nearby evaluation
point away from the pole.
-/

namespace PotentialTheory

/-- A source vanishing near `X` has an ordinary, absolutely convergent
Newtonian gradient there. The sole tail assumption is absolute integrability
of the Newtonian integrand at `X`. -/
theorem hasFDerivAt_fundamentalSolution_five_integral_of_zero_on_ball
    (g : ℝ^5 → ℝ) (hg : Measurable g) (X : ℝ^5) (r : ℝ) (hr : 0 < r)
    (hzero : ∀ Y ∈ Metric.ball X r, g Y = 0)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * g Y)) :
    Integrable (fun Y : ℝ^5 ↦ g Y • fiveDimensionalGammaFDerivKernel (X - Y)) ∧
      HasFDerivAt
        (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * g Y)
        (∫ Y : ℝ^5, g Y • fiveDimensionalGammaFDerivKernel (X - Y)) X := by
  let F (Z Y : ℝ^5) : ℝ := fundamentalSolution 5 (Z - Y) * g Y
  let D (Z Y : ℝ^5) : ℝ^5 →L[ℝ] ℝ :=
    g Y • fiveDimensionalGammaFDerivKernel (Z - Y)
  let bound (Y : ℝ^5) : ℝ := (48 / r) * ‖F X Y‖
  have hmeas (Z : ℝ^5) : Measurable (F Z) := by
    dsimp [F]
    simp_rw [fundamentalSolution_five]
    fun_prop
  have hDmeas (Z : ℝ^5) : Measurable (D Z) :=
    hg.smul (measurable_fiveDimensionalGammaFDerivKernel.comp
      (measurable_const.sub measurable_id))
  have hbound : Integrable bound := hInt.norm.const_mul (48 / r)
  have haway (Y : ℝ^5) (hY : g Y ≠ 0) : r ≤ ‖X - Y‖ :=
    not_lt.1 fun h ↦ hY (hzero Y (by rwa [Metric.mem_ball, dist_eq_norm, norm_sub_rev]))
  have hnear (Z : ℝ^5) (hZ : Z ∈ Metric.ball X (r / 2)) : ‖Z - X‖ ≤ r / 2 :=
    (mem_ball_iff_norm.1 hZ).le
  have hD_bound (Y Z : ℝ^5) (hZ : Z ∈ Metric.ball X (r / 2)) :
      ‖D Z Y‖ ≤ bound Y := by
    by_cases hY : g Y = 0
    · simp [D, bound, F, hY]
    have hk := norm_fiveDimensionalGammaFDerivKernel_sub_le_of_near
      hr (hnear Z hZ) (haway Y hY)
    calc
      ‖D Z Y‖ = ‖g Y‖ * ‖fiveDimensionalGammaFDerivKernel (Z - Y)‖ := norm_smul _ _
      _ ≤ ‖g Y‖ * ((48 / r) * |fundamentalSolution 5 (X - Y)|) :=
        mul_le_mul_of_nonneg_left hk (norm_nonneg _)
      _ = bound Y := by
        simp only [bound, F, norm_mul, Real.norm_eq_abs]
        ring
  have hdiff (Y Z : ℝ^5) (hZ : Z ∈ Metric.ball X (r / 2)) :
      HasFDerivAt (fun W : ℝ^5 ↦ F W Y) (D Z Y) Z := by
    by_cases hY : g Y = 0
    · simpa only [F, D, hY, mul_zero, zero_smul] using
        (hasFDerivAt_const (c := (0 : ℝ)) Z)
    have hZY : Z - Y ≠ 0 := sub_ne_zero.2 fun h ↦ by
      subst h
      exact hY (hzero _ (Metric.ball_subset_ball (by linarith) hZ))
    have hchain : HasFDerivAt (fun W : ℝ^5 ↦ fundamentalSolution 5 (W - Y))
        (fiveDimensionalGammaFDerivKernel (Z - Y)) Z := by
      simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using!
        (hasFDerivAt_fiveDimensionalGamma (Z - Y) hZY).comp Z
          ((hasFDerivAt_id Z).sub_const Y)
    exact hchain.mul_const (g Y)
  exact ⟨hbound.mono' (hDmeas X).aestronglyMeasurable
      (.of_forall fun Y ↦ hD_bound Y X (Metric.mem_ball_self (half_pos hr))),
    hasFDerivAt_integral_of_dominated_of_fderiv_le (Metric.ball_mem_nhds X (half_pos hr))
      (.of_forall fun Z ↦ (hmeas Z).aestronglyMeasurable) hInt (hDmeas X).aestronglyMeasurable
      (.of_forall hD_bound) hbound (.of_forall hdiff)⟩

end PotentialTheory

/-!
A compact cutoff deals with the pole, while the tail retains the source's
original decay. Absolute convergence at one anchor is enough to define and
differentiate the potential at every point.
-/

namespace PotentialTheory

/-- The full derivative kernel is locally integrable. Its inverse-fourth-power
singularity is integrable in five dimensions. -/
theorem locallyIntegrable_fiveDimensionalGammaFDerivKernel :
    LocallyIntegrable fiveDimensionalGammaFDerivKernel volume := by
  exact locallyIntegrable_of_norm_le_rpow
    (by norm_num : 1 ≤ Module.finrank ℝ (ℝ^5))
    (by norm_num : (4 : ℝ) < Module.finrank ℝ (ℝ^5))
    (Filter.Eventually.of_forall (fun X ↦
      (norm_fiveDimensionalGammaFDerivKernel X).le))
    measurable_fiveDimensionalGammaFDerivKernel.aestronglyMeasurable

/-- A continuous compact factor can be paired with the Newtonian kernel
at any evaluation point, including points inside its support. -/
private theorem integrable_fundamentalSolution_five_mul_of_hasCompactSupport
    (f : ℝ^5 → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) (X : ℝ^5) :
    Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * f Y) := by
  exact (hfc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
    (locallyIntegrable_fundamentalSolution 5) hf X).integrable_swap

/-- The compact C¹ gradient formula determines the full Fréchet derivative.
No additional regularity is needed to pass from its five coordinates to the
continuous linear map. -/
private theorem hasFDerivAt_fundamentalSolution_five_integral_of_hasCompactSupport
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (X : ℝ^5) :
    Integrable (fun Y : ℝ^5 ↦ f Y • fiveDimensionalGammaFDerivKernel (X - Y)) ∧
      HasFDerivAt
        (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y)
        (∫ Y : ℝ^5, f Y • fiveDimensionalGammaFDerivKernel (X - Y)) X := by
  let fX : ℝ^5 → ℝ := fun Y ↦ f (X - Y)
  have hfX : Continuous fX := hf.continuous.comp (continuous_const.sub continuous_id)
  have hfXc : HasCompactSupport fX := hfc.comp_homeomorph (Homeomorph.subLeft X)
  have hD0 : Integrable (fun Y : ℝ^5 ↦ fX Y • fiveDimensionalGammaFDerivKernel Y) :=
    LocallyIntegrable.integrable_smul_left_of_hasCompactSupport
      locallyIntegrable_fiveDimensionalGammaFDerivKernel hfX hfXc
  have hD : Integrable (fun Y : ℝ^5 ↦ f Y • fiveDimensionalGammaFDerivKernel (X - Y)) := by
    simpa only [fX, sub_sub_cancel] using hD0.comp_sub_left X
  let P : ℝ^5 → ℝ :=
    convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume
  have hP : DifferentiableAt ℝ P X :=
    ((hfc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      (locallyIntegrable_fundamentalSolution 5) hf).differentiable one_ne_zero) X
  have hfd : fderiv ℝ P X =
      ∫ Y : ℝ^5, f Y • fiveDimensionalGammaFDerivKernel (X - Y) := by
    have hlin : (fderiv ℝ P X).toLinearMap =
        (∫ Y : ℝ^5, f Y • fiveDimensionalGammaFDerivKernel (X - Y)).toLinearMap := by
      apply (EuclideanSpace.basisFun (Fin 5) ℝ).toBasis.ext
      intro i
      simp only [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
      change (∂[i] P) X =
        (∫ Y : ℝ^5, f Y • fiveDimensionalGammaFDerivKernel (X - Y))
          (EuclideanSpace.single i (1 : ℝ))
      rw [ContinuousLinearMap.integral_apply hD]
      simp only [smul_apply, smul_eq_mul,
        fiveDimensionalGammaFDerivKernel_apply_single]
      simpa only [mul_comm] using
        (fundamentalSolution_five_convolution_partialDeriv_eq_integral f hf hfc i X).2
    apply ContinuousLinearMap.ext
    intro v
    exact LinearMap.congr_fun hlin v
  have hrepr :
      (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) = P := by
    funext Z
    exact convolution_mul_swap.symm
  refine ⟨hD, ?_⟩
  rw [hrepr, ← hfd]
  exact hP.hasFDerivAt

/-- Absolute convergence of the Newtonian potential at one anchor implies
absolute convergence at every point for a continuous source. A compact cutoff
handles the new pole; outside it the shifted kernel is at most eight times
the anchor kernel. -/
theorem integrable_fundamentalSolution_five_mul_of_integrable_at_anchor
    (f : ℝ^5 → ℝ) (hf : Continuous f) (A X : ℝ^5)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (A - Y) * f Y)) :
    Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * f Y) := by
  let R : ℝ := 2 * ‖X - A‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let χ : ContDiffBump A := ⟨R, R + 1, hR, lt_add_one R⟩
  let fnear : ℝ^5 → ℝ := fun Y ↦ χ Y * f Y
  let g : ℝ^5 → ℝ := fun Y ↦ (1 - χ Y) * f Y
  have hfnear : Continuous fnear := χ.continuous.mul hf
  have hfnearc : HasCompactSupport fnear := χ.hasCompactSupport.mul_right
  have hnear := integrable_fundamentalSolution_five_mul_of_hasCompactSupport
    fnear hfnear hfnearc X
  have hgt : Measurable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * g Y) := by
    have hg : Continuous g := (continuous_const.sub χ.continuous).mul hf
    have hΓ : Measurable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y)) := by
      simp_rw [fundamentalSolution_five]
      fun_prop
    exact hΓ.mul hg.measurable
  have htail : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * g Y) := by
    apply (hInt.norm.const_mul 8).mono' hgt.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro Y
    by_cases hχ : χ Y = 1
    · simp only [g, hχ, sub_self, zero_mul, mul_zero, norm_zero]
      positivity
    have hRY : R ≤ ‖A - Y‖ := by
      by_contra h
      apply hχ
      apply χ.one_of_mem_closedBall
      simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev Y A] using
        (lt_of_not_ge h).le
    have hXA : ‖X - A‖ ≤ R / 2 := by dsimp [R]; linarith
    have hk := abs_fundamentalSolution_five_sub_le_of_near hR hXA hRY
    have hχ0 : 0 ≤ 1 - χ Y := sub_nonneg.mpr χ.le_one
    have hχ1 : 1 - χ Y ≤ 1 := by linarith [χ.nonneg' Y]
    change |fundamentalSolution 5 (X - Y) * ((1 - χ Y) * f Y)| ≤
      8 * |fundamentalSolution 5 (A - Y) * f Y|
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hχ0]
    calc
      _ ≤ (8 * |fundamentalSolution 5 (A - Y)|) * (1 * |f Y|) := by gcongr
      _ = _ := by ring
  exact (hnear.fun_add htail).congr (.of_forall fun Y ↦ by simp only [fnear, g]; ring)

/-- A C¹ source whose Newtonian potential converges absolutely at one anchor
has the classical gradient of the integral at every point. The proof
uses a compact C¹ cutoff at the pole and differentiates the remaining tail
under an integrable majorant. -/
theorem hasFDerivAt_fundamentalSolution_five_integral_of_integrable_at_anchor
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f) (A X : ℝ^5)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (A - Y) * f Y)) :
    Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (X - Y) * f Y) ∧
      Integrable (fun Y : ℝ^5 ↦ f Y • fiveDimensionalGammaFDerivKernel (X - Y)) ∧
      HasFDerivAt
        (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y)
        (∫ Y : ℝ^5, f Y • fiveDimensionalGammaFDerivKernel (X - Y)) X := by
  have hAll (Z : ℝ^5) :=
    integrable_fundamentalSolution_five_mul_of_integrable_at_anchor f hf.continuous A Z hInt
  let χ : ContDiffBump X := default
  let fnear : ℝ^5 → ℝ := fun Y ↦ χ Y * f Y
  let g : ℝ^5 → ℝ := fun Y ↦ f Y - fnear Y
  have hfnear : ContDiff ℝ 1 fnear := χ.contDiff.mul hf
  have hfnearc : HasCompactSupport fnear := χ.hasCompactSupport.mul_right
  have hg : Continuous g := hf.continuous.sub hfnear.continuous
  have hnearInt (Z : ℝ^5) :=
    integrable_fundamentalSolution_five_mul_of_hasCompactSupport
      fnear hfnear.continuous hfnearc Z
  have hgInt (Z : ℝ^5) :
      Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (Z - Y) * g Y) := by
    simpa only [g, mul_sub] using! (hAll Z).sub' (hnearInt Z)
  have hzero : ∀ Y ∈ Metric.ball X χ.rIn, g Y = 0 := fun Y hY ↦ by
    simp only [g, fnear, χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hY), one_mul,
      sub_self]
  have hnear := hasFDerivAt_fundamentalSolution_five_integral_of_hasCompactSupport
    fnear hfnear hfnearc X
  have htail := hasFDerivAt_fundamentalSolution_five_integral_of_zero_on_ball
    g hg.measurable X χ.rIn χ.rIn_pos hzero (hgInt X)
  have hpotential : (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) =
      fun Z ↦ (∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * fnear Y) +
        ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * g Y := funext fun Z ↦ by
    rw [← integral_add (hnearInt Z) (hgInt Z)]
    simp only [g, ← mul_add, add_sub_cancel]
  have hgradient : (∫ Y : ℝ^5, f Y • fiveDimensionalGammaFDerivKernel (X - Y)) =
      (∫ Y : ℝ^5, fnear Y • fiveDimensionalGammaFDerivKernel (X - Y)) +
        ∫ Y : ℝ^5, g Y • fiveDimensionalGammaFDerivKernel (X - Y) := by
    rw [← integral_add hnear.1 htail.1]
    simp only [g, ← add_smul, add_sub_cancel]
  refine ⟨hAll X, (Integrable.fun_add (ε' := ℝ^5 →L[ℝ] ℝ) hnear.1 htail.1).congr
    (.of_forall fun Y ↦ by simp only [g, ← add_smul, add_sub_cancel]), ?_⟩
  rw [hpotential, hgradient]
  exact hnear.2.add htail.2

/-- Each first derivative of a noncompact C¹ Newtonian potential is the
absolutely convergent integral of its explicit coordinate kernel. The only
decay assumption is absolute convergence of the potential at one anchor. -/
theorem fundamentalSolution_five_convolution_partialDeriv_eq_integral_of_integrable_at_anchor
    (f : ℝ^5 → ℝ) (hf : ContDiff ℝ 1 f) (A X : ℝ^5) (i : Fin 5)
    (hInt : Integrable (fun Y : ℝ^5 ↦ fundamentalSolution 5 (A - Y) * f Y)) :
    Integrable (fun Y : ℝ^5 ↦ fiveDimensionalGammaGradientKernel i (X - Y) * f Y) ∧
      (∂[i]
        (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume)) X =
        ∫ Y : ℝ^5, fiveDimensionalGammaGradientKernel i (X - Y) * f Y := by
  have h := hasFDerivAt_fundamentalSolution_five_integral_of_integrable_at_anchor f hf A X hInt
  have hconv : HasFDerivAt
      (convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume)
      (∫ Y : ℝ^5, f Y • fiveDimensionalGammaFDerivKernel (X - Y)) X := by
    have hrepr :
        convolution (fundamentalSolution 5) f (ContinuousLinearMap.mul ℝ ℝ) volume =
          (fun Z : ℝ^5 ↦ ∫ Y : ℝ^5, fundamentalSolution 5 (Z - Y) * f Y) := by
      funext Z
      exact convolution_mul_swap
    rw [hrepr]
    exact h.2.2
  refine ⟨?_, ?_⟩
  · simpa only [ContinuousLinearMap.apply_apply, smul_apply, smul_eq_mul,
      fiveDimensionalGammaFDerivKernel_apply_single, mul_comm] using!
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).integrable_comp h.2.1
  · unfold partialDeriv
    rw [hconv.fderiv, ContinuousLinearMap.integral_apply h.2.1]
    simp only [smul_apply, smul_eq_mul,
      fiveDimensionalGammaFDerivKernel_apply_single, mul_comm]

end PotentialTheory
