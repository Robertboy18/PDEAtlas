/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.SignedPower.Deriv
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Nodal.Bound
public import PDE.Hyperbolic.NonlinearWave.SmallData.Classical.LocalPower.LowerPower.Superposition
import CAS.ExactTactic

/-!
# Nodal moments of signed-power averages

Differentiation and symmetric increments of signed-power averages force a nodal moment to vanish
under the required interior regularity.
-/

@[expose] public noncomputable section

section

open Set Filter MeasureTheory BoundedContinuousFunction
open scoped Topology
open WaveEquation.SmallData.Classical.LocalPower
open WaveEquation.SmallData.Classical.LocalPower.LowerPower

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
  [OpensMeasurableSpace K] (μ : Measure K) [IsFiniteMeasure μ]

/-- Differentiate a finite signed-power average in the uniform function space. -/
theorem hasDerivAt_integral_signedPower {p t : ℝ} (hp : 1 ≤ p) (w : K →ᵇ ℝ) {U : ℝ → K →ᵇ ℝ}
    {U' : K →ᵇ ℝ} (hU : HasDerivAt U U' t) :
    HasDerivAt (fun s : ℝ ↦ ∫ z, w z * Real.signedPower p (U s z) ∂μ)
      (p * ∫ z, |U t z| ^ (p - 1) * (w z * U' z) ∂μ) t := by
  let f : C(ℝ, ℝ) := ⟨Real.signedPower p, (Real.contDiff_one_signedPower hp).continuous⟩
  let N := composeCompact (α := K) f
  have hN : HasDerivAt (fun s ↦ N (U s)) (fderiv ℝ N (U t) U') t :=
    ((contDiff_composeCompact (Real.contDiff_one_signedPower hp)).differentiable
      one_ne_zero (U t)).hasFDerivAt.comp_hasDerivAt t hU
  have hI := (integralCLM μ).hasFDerivAt.comp_hasDerivAt t (hN.const_mul w)
  have he : integralCLM μ (w * fderiv ℝ N (U t) U') =
      p * ∫ z, |U t z| ^ (p - 1) * (w z * U' z) ∂μ := by
    rw [integralCLM_apply, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with z
    change w z * (fderiv ℝ N (U t) U') z = _
    rw [fderiv_composeCompact_apply (Real.contDiff_one_signedPower hp),
      (Real.hasDerivAt_signedPower hp (U t z)).deriv]
    cas
  rw [he] at hI
  exact hI

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

end

section

open Set Filter MeasureTheory BoundedContinuousFunction
open scoped Topology
open WaveEquation.SmallData.Classical.LocalPower

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

variable {K : Type} [TopologicalSpace K]

variable [CompactSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  (μ : Measure K) [IsFiniteMeasure μ]

/-- Nodal necessity needs differentiable velocity only away from the exact zero patch. -/
theorem integral_nodal_moment_eq_zero_of_regular_off_zeros {α : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1)
    {U V V₂ : ℝ → K →ᵇ ℝ} (hU : DifferentiableAt ℝ U 0) (hV : ContinuousAt V 0)
    (hV₂ : DifferentiableAt ℝ V₂ 0) (heq : ∀ᶠ t : ℝ in 𝓝 0, ∀ z : K, U 0 z ≠ 0 → V t z = V₂ t z)
    (hD : DifferentiableAt ℝ (fun t : ℝ ↦ ∫ z, |U t z| ^ α * V t z ∂μ) 0) :
    (∫ z, if U 0 z = 0 then |deriv U 0 z| ^ α * V 0 z else 0 ∂μ) = 0 := by
  let d (t : ℝ) : K →ᵇ ℝ := composeCompact ⟨fun x : ℝ ↦ |x| ^ α,
      (Real.continuous_rpow_const hα.le).comp continuous_abs⟩ (U t) * V t
  have hint (t : ℝ) : Integrable (fun z ↦ |U t z| ^ α * V t z) μ := (d t).integrable μ
  let F (t : ℝ) (z : K) := (|U t z| ^ α * V t z + |U (-t) z| ^ α * V (-t) z -
      2 * (|U 0 z| ^ α * V 0 z)) / (2 * t ^ α)
  obtain ⟨C₀, hC₀⟩ := exists_uniform_nodal_majorant_on_zeros hα hU hV
  obtain ⟨C₂, hC₂⟩ := exists_uniform_nodal_majorant hα.le hα₁ hU hV₂
  let C : ℝ := max C₀ C₂
  have heq₀ := heq.self_of_nhds
  have hnegT : Tendsto (fun t : ℝ ↦ -t) (𝓝 0) (𝓝 0) := by
    simpa only [neg_zero] using continuous_neg.tendsto (0 : ℝ)
  have hC : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z, ‖F t z‖ ≤ C := by
    filter_upwards [hC₀, hC₂, heq.filter_mono nhdsWithin_le_nhds,
      (hnegT.eventually heq).filter_mono nhdsWithin_le_nhds] with t hzero hreg hp hn
    intro z
    by_cases hz : U 0 z = 0
    · exact (hzero z hz).trans (le_max_left _ _)
    · dsimp only [F]
      rw [hp z hz, hn z hz, heq₀ z hz]
      exact (hreg z).trans (le_max_right _ _)
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ᵐ z ∂μ, ‖F t z‖ ≤ C := by
    filter_upwards [hC] with t ht
    exact Filter.Eventually.of_forall ht
  have hmeas : ∀ᶠ t in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (F t) μ := by
    apply Filter.Eventually.of_forall
    intro t
    exact ((((hint t).add (hint (-t))).sub ((hint 0).const_mul 2)).div_const
      (2 * t ^ α)).aestronglyMeasurable
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun t ↦ F t z) (𝓝[>] 0)
      (𝓝 (if U 0 z = 0 then |deriv U 0 z| ^ α * V 0 z else 0)) := by
    apply Filter.Eventually.of_forall
    intro z
    have hUz : HasDerivAt (fun t ↦ U t z) (deriv U 0 z) 0 := by
      simpa only [Function.comp_def, evalCLM_apply] using
        (evalCLM ℝ z : (K →ᵇ ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hU.hasDerivAt
    by_cases hz : U 0 z = 0
    · have hVz : ContinuousAt (fun t ↦ V t z) 0 :=
        (evalCLM ℝ z : (K →ᵇ ℝ) →L[ℝ] ℝ).continuous.continuousAt.comp hV
      simpa only [F, mul_assoc, ite_eq_left hz] using
        tendsto_symmetric_abs_rpow_mul_increment_of_zero hUz hVz hz hα
    · have hVz : DifferentiableAt ℝ (fun t ↦ V t z) 0 := by
        have hd : DifferentiableAt ℝ (fun t ↦ V₂ t z) 0 := by
          simpa only [Function.comp_def, evalCLM_apply] using
            ((evalCLM ℝ z : (K →ᵇ ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
              0 hV₂.hasDerivAt).differentiableAt
        apply hd.congr_of_eventuallyEq
        filter_upwards [heq] with t ht
        exact ht z hz
      simpa only [F, mul_assoc] using tendsto_symmetric_abs_rpow_mul_increment hUz hVz hα hα₁
  have hmoment := tendsto_integral_filter_of_norm_le_const hmeas ⟨C, hbound⟩ hlim
  have hzero : Tendsto (fun t : ℝ ↦ ∫ z, F t z ∂μ) (𝓝[>] 0) (𝓝 0) := by
    apply (tendsto_symmetric_increment_div_rpow hD.hasDerivAt hα₁).congr'
    apply Filter.Eventually.of_forall
    intro t
    dsimp only [F]
    have hiadd : Integrable (fun z ↦ |U t z| ^ α * V t z +
        |U (-t) z| ^ α * V (-t) z) μ := (hint t).add (hint (-t))
    rw [integral_div, integral_sub hiadd ((hint 0).const_mul 2),
      integral_add (hint t) (hint (-t)), integral_const_mul]
  exact tendsto_nhds_unique hmoment hzero

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

end

section

open Set Filter MeasureTheory BoundedContinuousFunction
open scoped Topology
open WaveEquation.SmallData.Classical.LocalPower
open WaveEquation.SmallData.Classical.LocalPower.LowerPower

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
  [OpensMeasurableSpace K] (μ : Measure K) [IsFiniteMeasure μ]

/-- A C² signed-power average forces its weighted nodal velocity moment to vanish. -/
theorem integral_signedPower_nodal_moment_eq_zero_of_regular_off_zeros {p : ℝ} (hp : 1 < p)
    (hp₂ : p ≤ 2) (w : K →ᵇ ℝ) {U U₂ : ℝ → K →ᵇ ℝ} (hU : ContDiffAt ℝ 1 U 0)
    (hU₂ : ContDiffAt ℝ 2 U₂ 0)
    (heq : ∀ᶠ t : ℝ in 𝓝 0, ∀ z : K, U 0 z ≠ 0 → deriv U t z = deriv U₂ t z)
    (hA : ContDiffAt ℝ 2 (fun t : ℝ ↦ ∫ z, w z * Real.signedPower p (U t z) ∂μ) 0) :
    (∫ z, if U 0 z = 0 then |deriv U 0 z| ^ (p - 1) * (w z * deriv U 0 z) else 0 ∂μ) = 0 := by
  let A (t : ℝ) := ∫ z, w z * Real.signedPower p (U t z) ∂μ
  let V (t : ℝ) : K →ᵇ ℝ := w * deriv U t
  let V₂ (t : ℝ) : K →ᵇ ℝ := w * deriv U₂ t
  have hV : ContinuousAt V 0 :=
    (hU.derivWithin (m := 0) (by norm_num)).continuousAt.const_mul w
  have hV₂ : DifferentiableAt ℝ V₂ 0 :=
    ((hU₂.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero).const_mul w
  have heqV : ∀ᶠ t : ℝ in 𝓝 0, ∀ z : K, U 0 z ≠ 0 → V t z = V₂ t z := by
    filter_upwards [heq] with t ht z hz
    change w z * deriv U t z = w z * deriv U₂ t z
    rw [ht z hz]
  have he : (fun t : ℝ ↦ ∫ z, |U t z| ^ (p - 1) * V t z ∂μ) =ᶠ[𝓝 0]
      (fun t ↦ deriv A t / p) := by
    filter_upwards [hU.eventually (by norm_num)] with t ht
    have hd := (hasDerivAt_integral_signedPower μ hp.le w
      (ht.differentiableAt (by norm_num)).hasDerivAt).deriv
    change _ = deriv A t / p
    rw [hd]
    exact (mul_div_cancel_left₀ _ (ne_of_gt (lt_trans zero_lt_one hp))).symm
  have hAd : DifferentiableAt ℝ (deriv A) 0 :=
    (hA.derivWithin (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact integral_nodal_moment_eq_zero_of_regular_off_zeros μ (by linarith) (by linarith)
    (hU.differentiableAt (by norm_num)) hV hV₂ heqV ((hAd.div_const p).congr_of_eventuallyEq he)

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

end
