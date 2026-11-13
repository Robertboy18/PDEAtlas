/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.GeneralOrder.SchwartzAgreement
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.Real
import CAS.ExactTactic

/-!
# Compatibility with the order-one trace

At `s = 1`, the normal mass is `π` and the general kernel equals the
Cauchy square-root kernel. Consequently both the trace and the chosen right
inverse agree with the order-one operators of `Trace.Operator` and `Trace.Real`.
The displayed casts only identify the equal real orders `1 - 1/2` and `1/2`.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform BesselPotentialSpace
open scoped ENNReal NNReal BesselPotentialSpace

namespace SobolevSpace.Fractional.Trace.GeneralOrder

/-- The general kernel specializes to the Cauchy square-root kernel. -/
theorem normalKernel_one (a : ℝ≥0) (ha : a ≠ 0) (t : ℝ) :
    normalKernel 1 a t = Trace.normalKernel a t := by
  apply (sq_eq_sq₀ (normalKernel_nonneg 1 a t) (Trace.normalKernel_nonneg a t)).mp
  rw [normalKernel_sq one_half_lt_one, Trace.normalKernel_sq, normalMass_one]
  norm_num only [mul_one, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    Real.rpow_neg_one]
  unfold ProbabilityTheory.cauchyPDFReal
  simp only [sub_zero]
  have hbase : 0 < t ^ 2 + (a : ℝ) ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (NNReal.coe_ne_zero.2 ha))
  cas using Real.pi_ne_zero hbase.ne'

theorem frequencyKernel_one {n : ℕ} (ξ : ℝ^n) (t : ℝ) :
    frequencyKernel 1 ξ t = Trace.normalKernel (tangentialScale ξ) t :=
  normalKernel_one _ (tangentialScale_ne_zero ξ) t

theorem frequencyRestriction_one (n : ℕ) :
    frequencyRestriction n one_half_lt_one = normalRestriction n := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [frequencyRestriction_apply_ae one_half_lt_one u,
    normalRestriction_apply_ae u] with ξ h1 h2
  rw [h1, h2]
  simp only [frequencyRestrictionFun, normalRestrictionFun, frequencyKernel_one]

theorem frequencyLiftEuclideanLI_one (n : ℕ) (v : Lp ℂ 2 (volume : Measure ℝ^n)) :
    frequencyLiftEuclideanLI n one_half_lt_one v = normalLiftEuclideanLI n v := by
  apply Lp.ext
  filter_upwards [frequencyLiftEuclideanLI_apply_ae n one_half_lt_one v,
    normalLiftEuclideanLI_apply_ae n v] with x h1 h2
  rw [h1, h2]
  simp only [frequencyLiftFun, normalLiftFun, frequencyKernel_one]

private theorem toLp_cast_order {n : ℕ} {r t : ℝ} (h : r = t) (u : H^{r}(ℝ^n)) :
    toLp (cast (congrArg (fun q : ℝ ↦ H^{q}(ℝ^n)) h) u) = toLp u := by
  subst t
  rfl

/-- The complex trace at order one is the trace, after the order identity. -/
theorem wholeSpaceTraceCLM_one (n : ℕ) (u : H^{(1 : ℝ)}(ℝ^(n + 1))) :
    cast (congrArg (fun r : ℝ ↦ H^{r}(ℝ^n))
      (by norm_num : (1 : ℝ) - 1 / 2 = 1 / 2))
        (wholeSpaceTraceCLM n one_half_lt_one u) = Trace.wholeSpaceTraceCLM n u := by
  apply injective_toLp (ℝ^n) ℂ (1 / 2) 2
  rw [toLp_cast_order (by norm_num : (1 : ℝ) - 1 / 2 = 1 / 2)]
  apply (Lp.fourierTransformₗᵢ (ℝ^n) ℂ).injective
  change 𝓕 (toLp (wholeSpaceTraceCLM n one_half_lt_one u)) =
    𝓕 (toLp (Trace.wholeSpaceTraceCLM n u))
  rw [fourier_toLp_wholeSpaceTraceCLM, Trace.fourier_toLp_wholeSpaceTraceCLM,
    traceConstant_one, frequencyRestriction_one]

/-- The explicit general lifting specializes to the order-one lifting. -/
theorem wholeSpaceLiftingCLM_one (n : ℕ) (v : H^{(1 : ℝ) - 1 / 2}(ℝ^n)) :
    wholeSpaceLiftingCLM n one_half_lt_one v =
      Trace.wholeSpaceLiftingCLM n (cast (congrArg (fun r : ℝ ↦ H^{r}(ℝ^n))
        (by norm_num : (1 : ℝ) - 1 / 2 = 1 / 2)) v) := by
  apply injective_toLp (ℝ^(n + 1)) ℂ 1 2
  apply (Lp.fourierTransformₗᵢ (ℝ^(n + 1)) ℂ).injective
  change 𝓕 (toLp (wholeSpaceLiftingCLM n one_half_lt_one v)) =
    𝓕 (toLp (Trace.wholeSpaceLiftingCLM n _))
  rw [fourier_toLp_wholeSpaceLiftingCLM, traceConstant_one,
    frequencyLiftEuclideanLI_one]
  simp only [Trace.wholeSpaceLiftingCLM, smul_apply, toLp_smul, fourier_smul,
    LinearIsometry.coe_toContinuousLinearMap, fourier_toLp_besselNormalLiftLI]
  rw [toLp_cast_order (by norm_num : (1 : ℝ) - 1 / 2 = 1 / 2)]

private theorem cast_real_val {n : ℕ} {r t : ℝ} (h : r = t) (u : HsSpaceReal n r) :
    (cast (congrArg (HsSpaceReal n) h) u).val =
      cast (congrArg (fun q : ℝ ↦ H^{q}(ℝ^n)) h) u.val := by
  subst t
  rfl

/-- Compatibility on the real spaces uses the same canonical order transport. -/
theorem wholeSpaceTraceRealCLM_one (n : ℕ) (u : HsSpaceReal (n + 1) 1) :
    cast (congrArg (HsSpaceReal n) (by norm_num : (1 : ℝ) - 1 / 2 = 1 / 2))
      (wholeSpaceTraceRealCLM n one_half_lt_one u) = Trace.wholeSpaceTraceRealCLM n u := by
  apply Subtype.ext
  rw [cast_real_val (by norm_num : (1 : ℝ) - 1 / 2 = 1 / 2)]
  exact wholeSpaceTraceCLM_one n u.val

/-- The real right inverse agrees with the real order-one right inverse. -/
theorem wholeSpaceLiftingRealCLM_one (n : ℕ) (v : HsSpaceReal n ((1 : ℝ) - 1 / 2)) :
    wholeSpaceLiftingRealCLM n one_half_lt_one v =
      Trace.wholeSpaceLiftingRealCLM n (cast (congrArg (HsSpaceReal n)
        (by norm_num : (1 : ℝ) - 1 / 2 = 1 / 2)) v) := by
  apply Subtype.ext
  rw [Trace.wholeSpaceLiftingRealCLM_val,
    cast_real_val (by norm_num : (1 : ℝ) - 1 / 2 = 1 / 2)]
  exact wholeSpaceLiftingCLM_one n v.val

end SobolevSpace.Fractional.Trace.GeneralOrder
