/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.Lp.WeightedL2
public import PDE.Common.Euclidean.HalfSpace
public import PDE.FDeriv.PartialDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import PDE.FDeriv.Calculus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Covering.Besicovitch
import PDE.Analysis.InnerProductSpace.Euclidean.Coordinates

/-!
# Weighted Poincaré estimates along rays

The fundamental theorem along rays and dilation of the half-plane give
a weighted Poincaré inequality for functions vanishing at the origin.
The ray comparison and all Fubini integrability hypotheses are explicit.
Quartic decay bounds the ray kernel; a positive floor makes it divergent.

Throughout, `H₊ = {x : ℝ² | 0 ≤ x₀}` is the closed right half-plane.
-/

@[expose] public section

noncomputable section

open PDE.Common (coordinateClosedHalfSpace measurableSet_coordinateClosedHalfSpace
  smul_mem_coordinateClosedHalfSpace_iff)

local notation "H₊" => coordinateClosedHalfSpace (0 : Fin 2)

open PDE.FDeriv

open MeasureTheory Filter LineDeriv
open scoped ENNReal RealInnerProductSpace Topology

namespace SobolevSpace.Weighted

/--
Fundamental theorem of calculus along the segment from the origin to `x`.

Integrating the directional derivative along the segment recovers a function
that vanishes at the origin.
-/
theorem profile_eq_integral_fderiv_along_ray
    {f : (ℝ^2 → ℝ)} (hf : ContDiff ℝ 1 f) (hf0 : f (0 : (ℝ^2)) = 0) (x : (ℝ^2)) :
    f x = ∫ t in (0 : ℝ)..1, fderiv ℝ f (t • x) x := by
  let line : ℝ → (ℝ^2) := fun t ↦ t • x
  have hline : ContDiff ℝ 1 line := contDiff_id.smul contDiff_const
  have hcomp : ContDiff ℝ 1 (f ∘ line) := hf.comp hline
  have hderiv :
      deriv (f ∘ line) = fun t ↦ fderiv ℝ f (t • x) x := by
    funext t
    have hchain :=
      (hf.differentiable_one.differentiableAt.hasFDerivAt.comp_hasDerivAt t
        hline.differentiable_one.differentiableAt.hasDerivAt).deriv
    simpa [line, deriv_smul_const] using hchain
  have hFTC := intervalIntegral.integral_deriv_of_contDiffOn_Icc
    (f := f ∘ line) hcomp.contDiffOn (by norm_num : (0 : ℝ) ≤ 1)
  rw [hderiv] at hFTC
  have hfzero : f (0 : (ℝ^2)) = 0 := by simpa using hf0
  simpa [Function.comp_def, line, hfzero] using hFTC.symm

/--
Triangle-inequality consequence of `profile_eq_integral_fderiv_along_ray`.

The next weighted-Poincaré step is Cauchy-Schwarz in `t`; this lemma already
establishes the exact radial reconstruction and the corresponding integral
majorant for the Fréchet derivative.
-/
theorem norm_profile_le_integral_norm_fderiv_along_ray
    {f : (ℝ^2 → ℝ)} (hf : ContDiff ℝ 1 f) (hf0 : f (0 : (ℝ^2)) = 0) (x : (ℝ^2)) :
    |f x| ≤ ∫ t in (0 : ℝ)..1, |fderiv ℝ f (t • x) x| := by
  rw [profile_eq_integral_fderiv_along_ray hf hf0 x]
  simpa [Real.norm_eq_abs] using
    (intervalIntegral.norm_integral_le_integral_norm
      (f := fun t : ℝ ↦ fderiv ℝ f (t • x) x)
      (by norm_num : (0 : ℝ) ≤ 1))

/--
Cauchy-Schwarz along the unit ray used in the weighted Poincaré proof.

The derivative is evaluated on the ray direction `x`; the next estimate can
bound this directional derivative by `‖x‖` times the operator norm of `fderiv`.
-/
theorem sq_profile_le_integral_sq_fderiv_along_ray
    {f : (ℝ^2 → ℝ)} (hf : ContDiff ℝ 1 f) (hf0 : f (0 : (ℝ^2)) = 0) (x : (ℝ^2)) :
    f x ^ 2 ≤ ∫ t in (0 : ℝ)..1, (fderiv ℝ f (t • x) x) ^ 2 := by
  let h : ℝ → ℝ := fun t ↦ fderiv ℝ f (t • x) x
  have hh_cont : Continuous h := (hf.continuous_fderiv_apply (hn := by norm_num)).comp
    ((continuous_id.smul continuous_const).prodMk continuous_const)
  have hcs := MeasureTheory.integral_abs_mul_le_sqrt_integral_sq
    (μ := volume.restrict (Set.Ioc (0 : ℝ) 1)) (f := fun _ : ℝ ↦ (1 : ℝ)) (g := h) (memLp_const 1)
    ((memLp_two_iff_integrable_sq hh_cont.aestronglyMeasurable).2
      ((hh_cont.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self))
  have hray : |f x| ≤ ∫ t in (0 : ℝ)..1, |h t| := by
    simpa [h] using norm_profile_le_integral_norm_fderiv_along_ray hf hf0 x
  have hbound : |f x| ≤ √(∫ t in (0 : ℝ)..1, h t ^ 2) :=
    hray.trans (by simpa [intervalIntegral.integral_of_le zero_le_one] using hcs)
  simpa only [sq_abs] using (Real.le_sqrt (abs_nonneg _)
    (intervalIntegral.integral_nonneg zero_le_one fun t _ ↦ sq_nonneg (h t))).1 hbound

/-- Ray Cauchy-Schwarz for arbitrary coordinate derivative representatives.

This is the form needed by weighted Poincaré: differentiability enters only through the
one-dimensional FTC identity, which is a hypothesis. Given that identity and `L²` slice
control, the estimate is purely measure-theoretic.
-/
theorem sq_profile_le_norm_sq_integral_gradient_representatives_of_rayFTC
    (f gr gz : (ℝ^2 → ℝ)) (x : (ℝ^2))
    (hFTC : f x = ∫ t in (0 : ℝ)..1,
      x 0 * gr (t • x) + x 1 * gz (t • x))
    (hdir : MemLp (fun t : ℝ ↦
      x 0 * gr (t • x) + x 1 * gz (t • x)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)))
    (henergy : Integrable (fun t : ℝ ↦
      gr (t • x) ^ 2 + gz (t • x) ^ 2)
      (volume.restrict (Set.Ioc (0 : ℝ) 1))) :
    f x ^ 2 ≤ ‖x‖ ^ 2 * ∫ t in (0 : ℝ)..1,
      gr (t • x) ^ 2 + gz (t • x) ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  let d : ℝ → ℝ := fun t ↦ x 0 * gr (t • x) + x 1 * gz (t • x)
  let e : ℝ → ℝ := fun t ↦ gr (t • x) ^ 2 + gz (t • x) ^ 2
  have hdSq : Integrable (fun t ↦ d t ^ 2) μ := by
    exact (memLp_two_iff_integrable_sq hdir.aestronglyMeasurable).1 hdir
  have hone : MemLp (fun _ : ℝ ↦ (1 : ℝ)) 2 μ := memLp_const 1
  have hcs := MeasureTheory.integral_abs_mul_le_sqrt_integral_sq
    (μ := μ) (f := fun _ : ℝ ↦ (1 : ℝ)) (g := d) hone hdir
  have hcs' : (∫ t, |d t| ∂μ) ≤ √(∫ t, d t ^ 2 ∂μ) := by
    simpa [μ] using hcs
  have habsInt : |f x| ≤ ∫ t, |d t| ∂μ := by
    have hi := abs_integral_le_integral_abs (μ := μ) (f := d)
    rw [hFTC]
    simpa [μ, d, intervalIntegral.integral_of_le
      (by norm_num : (0 : ℝ) ≤ 1)] using hi
  have hsqDir : f x ^ 2 ≤ ∫ t, d t ^ 2 ∂μ := by
    simpa only [sq_abs] using (Real.le_sqrt (abs_nonneg _)
      (integral_nonneg fun _ ↦ sq_nonneg _)).1 (habsInt.trans hcs')
  have hpoint (t : ℝ) : d t ^ 2 ≤ ‖x‖ ^ 2 * e t := by
    have hnorm : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
      simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq x
    dsimp [d, e]
    rw [hnorm]
    nlinarith [sq_nonneg (x 0 * gz (t • x) - x 1 * gr (t • x))]
  have hright : Integrable (fun t ↦ ‖x‖ ^ 2 * e t) μ := by
    simpa [e, μ] using henergy.const_mul (‖x‖ ^ 2)
  have hmono : (∫ t, d t ^ 2 ∂μ) ≤ ∫ t, ‖x‖ ^ 2 * e t ∂μ :=
    integral_mono hdSq hright hpoint
  calc
    f x ^ 2 ≤ ∫ t, d t ^ 2 ∂μ := hsqDir
    _ ≤ ∫ t, ‖x‖ ^ 2 * e t ∂μ := hmono
    _ = ‖x‖ ^ 2 * ∫ t in (0 : ℝ)..1,
        gr (t • x) ^ 2 + gz (t • x) ^ 2 := by
      rw [integral_const_mul]
      simp [μ, e, intervalIntegral.integral_of_le
        (by norm_num : (0 : ℝ) ≤ 1)]

/--
The geometric ray estimate from the weighted Poincaré proof:
`|f(x)|² ≤ ‖x‖² ∫₀¹ ‖Df(tx)‖² dt`.
-/
theorem sq_profile_le_norm_sq_integral_norm_fderiv_along_ray
    {f : (ℝ^2 → ℝ)} (hf : ContDiff ℝ 1 f) (hf0 : f (0 : (ℝ^2)) = 0) (x : (ℝ^2)) :
    f x ^ 2 ≤ ‖x‖ ^ 2 *
      ∫ t in (0 : ℝ)..1, ‖fderiv ℝ f (t • x)‖ ^ 2 := by
  let L : ℝ → ((ℝ^2) →L[ℝ] ℝ) := fun t ↦ fderiv ℝ f (t • x)
  have hline : Continuous (fun t : ℝ ↦ t • x) := continuous_id.smul continuous_const
  have hL_cont : Continuous L :=
    (hf.continuous_fderiv (by norm_num)).comp hline
  have happ_cont : Continuous (fun t ↦ L t x) := by
    exact (hf.continuous_fderiv_apply (hn := by norm_num)).comp
      (hline.prodMk continuous_const)
  have hleft_int : IntervalIntegrable (fun t ↦ (L t x) ^ 2) volume 0 1 :=
    (happ_cont.pow 2).intervalIntegrable (μ := volume) 0 1
  have hright_cont : Continuous (fun t ↦ ‖x‖ ^ 2 * ‖L t‖ ^ 2) :=
    continuous_const.mul ((continuous_norm.comp hL_cont).pow 2)
  have hright_int : IntervalIntegrable (fun t ↦ ‖x‖ ^ 2 * ‖L t‖ ^ 2) volume 0 1 :=
    hright_cont.intervalIntegrable (μ := volume) 0 1
  have hpoint (t : ℝ) : (L t x) ^ 2 ≤ ‖x‖ ^ 2 * ‖L t‖ ^ 2 := by
    rw [← sq_abs, ← Real.norm_eq_abs, ← mul_pow, mul_comm]
    gcongr
    exact (L t).le_opNorm x
  have hintegral :
      (∫ t in (0 : ℝ)..1, (L t x) ^ 2) ≤
        ∫ t in (0 : ℝ)..1, ‖x‖ ^ 2 * ‖L t‖ ^ 2 :=
    intervalIntegral.integral_mono_on
      (by norm_num : (0 : ℝ) ≤ 1) hleft_int hright_int (fun t _ ↦ hpoint t)
  rw [intervalIntegral.integral_const_mul] at hintegral
  calc
    f x ^ 2 ≤ ∫ t in (0 : ℝ)..1, (L t x) ^ 2 := by
      simpa [L] using sq_profile_le_integral_sq_fderiv_along_ray hf hf0 x
    _ ≤ ‖x‖ ^ 2 * ∫ t in (0 : ℝ)..1, ‖L t‖ ^ 2 := hintegral
    _ = ‖x‖ ^ 2 * ∫ t in (0 : ℝ)..1, ‖fderiv ℝ f (t • x)‖ ^ 2 := by rfl

/-- Coordinate-gradient form of the geometric ray estimate on the profile plane. -/
theorem sq_profile_le_norm_sq_integral_partialDeriv_sq_along_ray
    {f : (ℝ^2 → ℝ)} (hf : ContDiff ℝ 1 f) (hf0 : f (0 : (ℝ^2)) = 0) (x : (ℝ^2)) :
    f x ^ 2 ≤ ‖x‖ ^ 2 * ∫ t in (0 : ℝ)..1,
      ((∂[0] f) (t • x)) ^ 2 +
        ((∂[1] f) (t • x)) ^ 2 := by
  have hnorm :
      (fun t : ℝ ↦ ‖fderiv ℝ f (t • x)‖ ^ 2) =
        fun t ↦ ((∂[0] f) (t • x)) ^ 2 +
          ((∂[1] f) (t • x)) ^ 2 := by
    funext t
    have ht := PDE.norm_fderiv_sq_eq_sum_partialDeriv_sq
      (n := 2) (f := f) (x := t • x) hf.differentiable_one.differentiableAt
    simpa [Fin.sum_univ_two] using ht
  simpa [hnorm] using sq_profile_le_norm_sq_integral_norm_fderiv_along_ray hf hf0 x

/--
Change of variables for positive dilations of the closed right half-plane.
The Jacobian factor is `t⁻²`.
-/
theorem integral_coordinateClosedHalfSpace_comp_smul
    (g : (ℝ^2) → ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ x in H₊, g (t • x)) =
      (t ^ 2)⁻¹ * ∫ x in H₊, g x := by
  have hindicator :
      (fun x : (ℝ^2) ↦ H₊.indicator g (t • x)) =
        H₊.indicator (fun x ↦ g (t • x)) := by
    funext x
    by_cases hx : x ∈ H₊
    · have htx : t • x ∈ H₊ :=
        (smul_mem_coordinateClosedHalfSpace_iff (0 : Fin 2) ht x).2 hx
      simp [hx, htx]
    · have htx : t • x ∉ H₊ := by
        simpa [smul_mem_coordinateClosedHalfSpace_iff (0 : Fin 2) ht x] using hx
      simp [hx, htx]
  have hscale := Measure.integral_comp_smul_of_nonneg
    (volume : Measure (ℝ^2)) (H₊.indicator g) t (hR := ht.le)
  calc
    (∫ x in H₊, g (t • x)) =
        ∫ x : (ℝ^2), H₊.indicator (fun y ↦ g (t • y)) x := by
          rw [integral_indicator (measurableSet_coordinateClosedHalfSpace (0 : Fin 2))]
    _ = ∫ x : (ℝ^2), H₊.indicator g (t • x) := by rw [hindicator]
    _ = (t ^ 2)⁻¹ • ∫ x : (ℝ^2), H₊.indicator g x := by
      simpa using hscale
    _ = (t ^ 2)⁻¹ * ∫ x in H₊, g x := by
      rw [integral_indicator (measurableSet_coordinateClosedHalfSpace (0 : Fin 2))]
      rfl

/--
The exact `t⁻⁴` scaling identity in the weighted Poincaré proof.  Two
powers come from the two-dimensional Jacobian and two from `‖x‖²`.
-/
theorem integral_coordinateClosedHalfSpace_norm_sq_comp_smul
    (G Φ : (ℝ^2) → ℝ) {t : ℝ} (ht : 0 < t) :
    (∫ x in H₊, ‖x‖ ^ 2 * G (t • x) * Φ x) =
      (t ^ 4)⁻¹ * ∫ y in H₊,
        ‖y‖ ^ 2 * G y * Φ (t⁻¹ • y) := by
  let g : (ℝ^2) → ℝ := fun y ↦ ‖t⁻¹ • y‖ ^ 2 * G y * Φ (t⁻¹ • y)
  have hscale := integral_coordinateClosedHalfSpace_comp_smul g ht
  have hleft :
      (∫ x in H₊, ‖x‖ ^ 2 * G (t • x) * Φ x) =
        ∫ x in H₊, g (t • x) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with x
    simp [g, smul_smul, ht.ne']
  have hg :
      g = fun y ↦ (t ^ 2)⁻¹ * (‖y‖ ^ 2 * G y * Φ (t⁻¹ • y)) := by
    funext y
    simp only [g, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, mul_pow]
    field_simp [ht.ne']
  rw [hleft, hscale, hg, integral_const_mul]
  field_simp [ht.ne']

/-- The total real-valued ray ratio used below.

Its finite analytic interpretation requires interval integrability of the
ray kernel and a positive denominator. In particular, a nonintegrable kernel
has total real integral zero; this definition does not certify finiteness.
-/
def weightedPoincareRayRatio
    (PhiU PhiR PhiZ : (ℝ^2 → ℝ)) (y : (ℝ^2)) : ℝ :=
  (‖y‖ ^ 2 * ∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * PhiU (t⁻¹ • y)) /
    min (PhiR y) (PhiZ y)

/--
A positive half-plane floor is incompatible with the ray kernel used by the
weighted Poincaré constant.  On `(0, 1]`, the kernel dominates
`C / t`, so it is not interval-integrable.
-/
theorem positive_floor_forces_weightedPoincare_ray_nonintegrable
    (PhiU : (ℝ^2 → ℝ)) (C : ℝ) (hC : 0 < C)
    (hFloor : ∀ x ∈ H₊, C ≤ PhiU x)
    (y : (ℝ^2)) (hy : y ∈ H₊) :
    ¬ IntervalIntegrable
      (fun t : ℝ ↦ (t ^ 4)⁻¹ * PhiU (t⁻¹ • y)) volume 0 1 := by
  intro hg
  -- on `(0, 1]`, `C t⁻¹ ≤ C t⁻⁴ ≤ t⁻⁴ Φ(t⁻¹ y)`, and `t⁻¹` is not integrable at `0`
  have hf : IntervalIntegrable (fun t : ℝ ↦ C * t⁻¹) volume 0 1 := by
    refine hg.mono_fun' (measurable_const.mul measurable_id.inv).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht0 : 0 < t := ht.1
    rw [Real.norm_of_nonneg (by positivity), mul_comm C]
    calc t⁻¹ * C ≤ (t ^ 4)⁻¹ * C := by
          gcongr
          exact pow_le_of_le_one ht0.le ht.2 (by norm_num)
      _ ≤ (t ^ 4)⁻¹ * PhiU (t⁻¹ • y) := by
          gcongr
          exact hFloor _ ((smul_mem_coordinateClosedHalfSpace_iff (0 : Fin 2)
            (inv_pos.mpr ht0) y).2 hy)
  have hinv : IntervalIntegrable (fun t : ℝ ↦ t⁻¹) volume 0 1 := by
    simpa only [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] using hf.const_mul C⁻¹
  rcases intervalIntegrable_inv_iff.mp hinv with hzero | hnotmem
  · norm_num at hzero
  · exact hnotmem (by simp)

/-- Quartic decay of the velocity weight along an outward ray makes the
singular ray kernel interval-integrable, whereas a uniform positive floor does
not (`positive_floor_forces_weightedPoincare_ray_nonintegrable`). For fixed nonzero
`y`, the argument `t⁻¹ • y` tends to spatial infinity as `t → 0⁺`, so the hypothesis
asks the weight to decay there like `t⁴`.

The exponent four is a convenient sufficient rate. Any power-law upper bound
with exponent strictly greater than three also gives integrability after the
substitution `s = t⁻¹`; this does not exclude integrable borderline logarithmic
corrections to cubic decay. -/
theorem weightedPoincare_ray_intervalIntegrable_of_quartic_decay
    (PhiU : (ℝ^2 → ℝ)) (hPhiU_meas : Measurable PhiU)
    (hPhiU_nonneg : ∀ x ∈ H₊, 0 ≤ PhiU x)
    (y : (ℝ^2)) (hy : y ∈ H₊) (A : ℝ) (hA : 0 ≤ A)
    (hdecay : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      PhiU (t⁻¹ • y) ≤ A * t ^ 4) :
    IntervalIntegrable
      (fun t : ℝ ↦ (t ^ 4)⁻¹ * PhiU (t⁻¹ • y)) volume 0 1 := by
  refine (intervalIntegrable_const (c := A)).mono_fun ((measurable_id.pow_const 4).inv.mul
    (hPhiU_meas.comp (measurable_id.inv.smul_const y))).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  rw [Set.uIoc_of_le zero_le_one] at ht
  have ht4 : 0 < t ^ 4 := pow_pos ht.1 4
  rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr ht4.le) (hPhiU_nonneg _
    ((smul_mem_coordinateClosedHalfSpace_iff (0 : Fin 2) (inv_pos.mpr ht.1) y).2 hy)))]
  calc _ ≤ (t ^ 4)⁻¹ * (A * t ^ 4) :=
        mul_le_mul_of_nonneg_left (hdecay t ht) (inv_nonneg.mpr ht4.le)
    _ = ‖A‖ := by rw [Real.norm_of_nonneg hA]; field_simp [ht.1.ne']

/-- Under the same outward quartic decay, the singular ray integral is bounded
by its explicit majorant. -/
theorem weightedPoincare_ray_integral_le_of_quartic_decay
    (PhiU : (ℝ^2 → ℝ)) (hPhiU_meas : Measurable PhiU)
    (hPhiU_nonneg : ∀ x ∈ H₊, 0 ≤ PhiU x)
    (y : (ℝ^2)) (hy : y ∈ H₊) (A : ℝ) (hA : 0 ≤ A)
    (hdecay : ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      PhiU (t⁻¹ • y) ≤ A * t ^ 4) :
    (∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * PhiU (t⁻¹ • y)) ≤ A := by
  have hkernel_int := weightedPoincare_ray_intervalIntegrable_of_quartic_decay
    PhiU hPhiU_meas hPhiU_nonneg y hy A hA hdecay
  have hconst_int : IntervalIntegrable (fun _ : ℝ ↦ A) volume 0 1 :=
    intervalIntegrable_const
  calc
    (∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * PhiU (t⁻¹ • y)) ≤
        ∫ _t in (0 : ℝ)..1, A := by
      apply intervalIntegral.integral_mono_on (by norm_num) hkernel_int hconst_int
      intro t ht
      rcases eq_or_lt_of_le ht.1 with rfl | ht0
      · simpa using hA
      · have ht4 : 0 < t ^ 4 := pow_pos ht0 4
        calc
          (t ^ 4)⁻¹ * PhiU (t⁻¹ • y) ≤
              (t ^ 4)⁻¹ * (A * t ^ 4) :=
            mul_le_mul_of_nonneg_left
              (hdecay t ⟨ht0, ht.2⟩) (inv_nonneg.mpr ht4.le)
          _ = A := by field_simp
    _ = A := by simp

/-- The ordinary pointwise supremum of the total real ray ratios.

A numerical certificate must prove that the displayed set is bounded above,
as well as the integrability and denominator conditions needed to interpret
each ratio analytically. Pointwise bounds give a sufficient certificate for
the corresponding essential supremum.
-/
noncomputable def weightedPoincareRayConstant
    (PhiU PhiR PhiZ : (ℝ^2 → ℝ)) : ℝ :=
  sSup {c : ℝ | ∃ y ∈ H₊, y ≠ (0 : (ℝ^2)) ∧
    c = weightedPoincareRayRatio PhiU PhiR PhiZ y}

/-- Every admissible non-origin ray ratio is at most the exact supremum once
the numerical/profile data prove boundedness.
-/
theorem weightedPoincareRayRatio_le_constant
    (PhiU PhiR PhiZ : (ℝ^2 → ℝ))
    (hbounded : BddAbove {c : ℝ | ∃ y ∈ H₊,
      y ≠ (0 : (ℝ^2)) ∧ c = weightedPoincareRayRatio PhiU PhiR PhiZ y})
    (y : (ℝ^2)) (hy : y ∈ H₊) (hy0 : y ≠ (0 : (ℝ^2))) :
    weightedPoincareRayRatio PhiU PhiR PhiZ y ≤
      weightedPoincareRayConstant PhiU PhiR PhiZ := by
  apply le_csSup hbounded
  exact ⟨y, hy, hy0, rfl⟩

/-- Gradient-energy specialization of the `t⁻⁴` half-plane scaling identity. -/
theorem weightedPoincare_scaled_gradient_slice
    (f : (ℝ^2 → ℝ)) (Φu : (ℝ^2 → ℝ)) {t : ℝ} (ht : 0 < t) :
    (∫ x in H₊, ‖x‖ ^ 2 *
        (((∂[0] f) (t • x)) ^ 2 +
          ((∂[1] f) (t • x)) ^ 2) * Φu x) =
      ∫ y in H₊, (t ^ 4)⁻¹ *
        (‖y‖ ^ 2 *
          (((∂[0] f) y) ^ 2 +
            ((∂[1] f) y) ^ 2) * Φu (t⁻¹ • y)) := by
  have hscale := integral_coordinateClosedHalfSpace_norm_sq_comp_smul
    (fun y ↦ ((∂[0] f) y) ^ 2 +
      ((∂[1] f) y) ^ 2) Φu ht
  rw [hscale, integral_const_mul]

/--
Squared weighted Poincaré estimate on the physical half-plane for `C¹`
profiles.  The two product-integrability hypotheses are the precise Fubini
conditions for the change of variables and exchange of integrals. They remain
explicit hypotheses of this theorem.
-/
theorem weightedPoincare_squared_halfPlane
    {f : (ℝ^2 → ℝ)} {Φu Φr Φz : (ℝ^2 → ℝ)} {CP : ℝ}
    (hf : ContDiff ℝ 1 f) (hf0 : f (0 : (ℝ^2)) = 0)
    (hΦu : ∀ x ∈ H₊, 0 ≤ Φu x)
    (hCP : 0 ≤ CP)
    (hweight : ∀ y ∈ H₊,
      ‖y‖ ^ 2 * (∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * Φu (t⁻¹ • y)) ≤
        CP * min (Φr y) (Φz y))
    (hf_int : Integrable (fun x ↦ f x ^ 2 * Φu x)
      (volume.restrict H₊))
    (hK : Integrable
      (fun p : ℝ × (ℝ^2) ↦ ‖p.2‖ ^ 2 *
        (((∂[0] f) (p.1 • p.2)) ^ 2 +
          ((∂[1] f) (p.1 • p.2)) ^ 2) * Φu p.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict H₊)))
    (hJ : Integrable
      (fun p : ℝ × (ℝ^2) ↦ (p.1 ^ 4)⁻¹ *
        (‖p.2‖ ^ 2 *
          (((∂[0] f) p.2) ^ 2 +
            ((∂[1] f) p.2) ^ 2) * Φu (p.1⁻¹ • p.2)))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (volume.restrict H₊)))
    (hr_int : Integrable
      (fun x ↦ ((∂[0] f) x) ^ 2 * Φr x)
      (volume.restrict H₊))
    (hz_int : Integrable
      (fun x ↦ ((∂[1] f) x) ^ 2 * Φz x)
      (volume.restrict H₊)) :
    (∫ x in H₊, f x ^ 2 * Φu x) ≤
      CP * ((∫ x in H₊,
          ((∂[0] f) x) ^ 2 * Φr x) +
        ∫ x in H₊,
          ((∂[1] f) x) ^ 2 * Φz x) := by
  calc (∫ x in H₊, f x ^ 2 * Φu x)
      ≤ ∫ x in H₊, ∫ t in Set.Ioc (0 : ℝ) 1,
          ‖x‖ ^ 2 * (((∂[0] f) (t • x)) ^ 2 + ((∂[1] f) (t • x)) ^ 2) * Φu x := by
        refine integral_mono_ae hf_int hK.integral_prod_right ?_
        filter_upwards [ae_restrict_mem (measurableSet_coordinateClosedHalfSpace (0 : Fin 2))]
          with x hx
        rw [integral_mul_const, integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one]
        exact mul_le_mul_of_nonneg_right
          (sq_profile_le_norm_sq_integral_partialDeriv_sq_along_ray hf hf0 x) (hΦu x hx)
    _ = ∫ t in Set.Ioc (0 : ℝ) 1, ∫ x in H₊,
          ‖x‖ ^ 2 * (((∂[0] f) (t • x)) ^ 2 + ((∂[1] f) (t • x)) ^ 2) * Φu x :=
        (integral_integral_swap hK).symm
    -- dilating each time slice by `t⁻¹`
    _ = ∫ t in Set.Ioc (0 : ℝ) 1, ∫ y in H₊, (t ^ 4)⁻¹ *
          (‖y‖ ^ 2 * (((∂[0] f) y) ^ 2 + ((∂[1] f) y) ^ 2) * Φu (t⁻¹ • y)) :=
        setIntegral_congr_fun measurableSet_Ioc fun t ht ↦
          weightedPoincare_scaled_gradient_slice f Φu ht.1
    _ = ∫ y in H₊, ∫ t in Set.Ioc (0 : ℝ) 1, (t ^ 4)⁻¹ *
          (‖y‖ ^ 2 * (((∂[0] f) y) ^ 2 + ((∂[1] f) y) ^ 2) * Φu (t⁻¹ • y)) :=
        integral_integral_swap hJ
    _ ≤ ∫ y in H₊, CP * (((∂[0] f) y) ^ 2 * Φr y + ((∂[1] f) y) ^ 2 * Φz y) := by
        refine integral_mono_ae hJ.integral_prod_right ((hr_int.add hz_int).const_mul CP) ?_
        filter_upwards [ae_restrict_mem (measurableSet_coordinateClosedHalfSpace (0 : Fin 2))]
          with y hy
        calc
          _ = (((∂[0] f) y) ^ 2 + ((∂[1] f) y) ^ 2) *
              (‖y‖ ^ 2 * ∫ t in (0 : ℝ)..1, (t ^ 4)⁻¹ * Φu (t⁻¹ • y)) := by
            rw [intervalIntegral.integral_of_le zero_le_one, ← integral_const_mul,
              ← integral_const_mul]
            congr 1 with t
            ring
          _ ≤ (((∂[0] f) y) ^ 2 + ((∂[1] f) y) ^ 2) * (CP * min (Φr y) (Φz y)) :=
            mul_le_mul_of_nonneg_left (hweight y hy) (by positivity)
          _ = CP * (((∂[0] f) y) ^ 2 * min (Φr y) (Φz y) +
              ((∂[1] f) y) ^ 2 * min (Φr y) (Φz y)) := by ring
          _ ≤ _ := by gcongr; exacts [min_le_left _ _, min_le_right _ _]
    _ = _ := by rw [integral_const_mul, integral_add hr_int hz_int]

end SobolevSpace.Weighted
