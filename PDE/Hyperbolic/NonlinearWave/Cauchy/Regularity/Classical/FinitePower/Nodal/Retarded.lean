/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.LocalExtension.TimeBand
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Nodal.Average
public import PDE.Common.Euclidean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Interior regularity and retarded nodal moments

An exact early zero patch separates the initial face from the nodal increment argument. Only
interior second derivatives are required of the original field.
-/

@[expose] public noncomputable section

section

open Set Filter MeasureTheory BoundedContinuousFunction PDE.Analysis
open scoped Topology
open WaveEquation.SmallData.Classical.LocalPower

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
  [OpensMeasurableSpace K] (μ : Measure K) [IsFiniteMeasure μ]

/-- An early exact zero patch makes the unit-cone nodal condition an interior C² condition. -/
theorem nodal_moment_eq_zero_of_interior_retarded_identity {p δ : ℝ} (hp : 1 < p) (hp₂ : p ≤ 2)
    (hδ : 0 < δ) (b e : ℝ^4) (hb : b 0 = 0) (he : e 0 = 1) (Z : K →ᵇ ℝ^4)
    (hZ : ∀ z, Z z 0 ∈ Icc 0 1) (w : K →ᵇ ℝ) {u H : ℝ^4 → ℝ}
    (hu₁ : ContDiffOn ℝ 1 u {x | -3 < x 0 ∧ x 0 < 3})
    (hu₂ : ContDiffOn ℝ 2 u {x | 0 < x 0 ∧ x 0 < 2}) (hzero : ∀ z, Z z 0 ≤ δ → u (b + Z z) = 0)
    (hH : ContDiff ℝ 2 H)
    (hEq : ∀ᶠ t : ℝ in 𝓝 1, u (b + t • e) = H (b + t • e) - t ^ 2 * ∫ z,
      w z * Real.signedPower p (u (b + t • Z z)) ∂μ) :
    (∫ z, if u (b + Z z) = 0 then |deriv (fun t : ℝ ↦ u (b + (1 + t) • Z z)) 0| ^ (p - 1) *
      (w z * deriv (fun t : ℝ ↦ u (b + (1 + t) • Z z)) 0) else 0 ∂μ) = 0 := by
  obtain ⟨G, hG, hGu⟩ := hu₁.exists_contDiff_eventuallyEq_on_band
    (EuclideanSpace.proj 0 : ℝ^4 →L[ℝ] ℝ)
    (s := 0) (τ := 3 / 2) (by norm_num) (by norm_num)
  obtain ⟨G₂, hG₂, hGu₂⟩ := hu₂.exists_contDiff_eventuallyEq_on_band
    (EuclideanSpace.proj 0 : ℝ^4 →L[ℝ] ℝ)
    (s := δ / 2) (τ := 3 / 2) (by positivity) (by norm_num)
  let B : K →ᵇ ℝ^4 := BoundedContinuousFunction.const K b
  let U (t : ℝ) : K →ᵇ ℝ := composeCompact ⟨G, hG.continuous⟩ (B + (1 + t) • Z)
  let U₂ (t : ℝ) : K →ᵇ ℝ := composeCompact ⟨G₂, hG₂.continuous⟩ (B + (1 + t) • Z)
  have hU : ContDiff ℝ 1 U := (contDiff_composeCompact hG).comp
    (contDiff_const.add ((contDiff_const.add contDiff_id).smul contDiff_const))
  have hU₂ : ContDiff ℝ 2 U₂ := (contDiff_composeCompact hG₂).comp
    (contDiff_const.add ((contDiff_const.add contDiff_id).smul contDiff_const))
  have hcoord (t : ℝ) (z : ℝ^4) : (b + (1 + t) • z) 0 = (1 + t) * z 0 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hb, zero_add]
  have hband {t : ℝ} (ht : t ∈ Ioo (-(1 / 4 : ℝ)) (1 / 4)) (z : K) :
      (b + (1 + t) • Z z) 0 ∈ Icc (0 : ℝ) (3 / 2) := by
    rw [hcoord]
    have hpos : 0 ≤ 1 + t := by linarith [ht.1]
    exact ⟨mul_nonneg hpos (hZ z).1,
      (mul_le_of_le_one_right hpos (hZ z).2).trans (by linarith [ht.2])⟩
  have hUZ {t : ℝ} (ht : t ∈ Ioo (-(1 / 4 : ℝ)) (1 / 4)) (z : K) : U t z = u (b + (1 + t) • Z z) :=
    (hGu _ (hband ht z)).eq_of_nhds.symm
  have hvalue (z : K) : U 0 z = u (b + Z z) := by
    simpa only [add_zero, one_smul] using hUZ (t := 0) (by norm_num) z
  have hUd (t : ℝ) (z : K) : deriv (fun s ↦ U s z) t = deriv U t z :=
    ((evalCLM ℝ z : (K →ᵇ ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
      (hU.differentiable one_ne_zero t).hasDerivAt).deriv
  have hU₂d (t : ℝ) (z : K) : deriv (fun s ↦ U₂ s z) t = deriv U₂ t z :=
    ((evalCLM ℝ z : (K →ᵇ ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t
      (hU₂.differentiable (by norm_num) t).hasDerivAt).deriv
  have heq : ∀ᶠ t : ℝ in 𝓝 0, ∀ z : K, U 0 z ≠ 0 → deriv U t z = deriv U₂ t z := by
    filter_upwards [Ioo_mem_nhds (by norm_num : -(1 / 4 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1 / 4)] with t ht z hz
    have hzδ : δ < Z z 0 := by
      by_contra hn
      exact hz ((hvalue z).trans (hzero z (le_of_not_gt hn)))
    have hlate : (b + (1 + t) • Z z) 0 ∈ Icc (δ / 2) (3 / 2) := by
      refine ⟨?_, (hband ht z).2⟩
      rw [hcoord]
      nlinarith [ht.1, (hZ z).1]
    have hgerm : G =ᶠ[𝓝 (b + (1 + t) • Z z)] G₂ := (hGu _ (hband ht z)).symm.trans (hGu₂ _ hlate)
    have hpath : Continuous (fun s : ℝ ↦ b + (1 + s) • Z z) := by fun_prop
    have heval : (fun s ↦ U s z) =ᶠ[𝓝 t] (fun s ↦ U₂ s z) := hgerm.comp_tendsto (hpath.tendsto t)
    rw [← hUd t z, ← hU₂d t z]
    exact heval.deriv_eq
  let A (t : ℝ) := ∫ z, w z * Real.signedPower p (U t z) ∂μ
  let R (t : ℝ) := (H (b + (1 + t) • e) - u (b + (1 + t) • e)) / (1 + t) ^ 2
  have hpath : ContDiff ℝ 2 (fun t : ℝ ↦ b + (1 + t) • e) :=
    contDiff_const.add ((contDiff_const.add contDiff_id).smul contDiff_const)
  have huvertex : ContDiffAt ℝ 2 u (b + (1 + (0 : ℝ)) • e) := by
    apply hu₂.contDiffAt
    apply ((isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)).mem_nhds
    change 0 < (b + (1 + (0 : ℝ)) • e) 0 ∧ (b + (1 + (0 : ℝ)) • e) 0 < 2
    rw [hcoord, he]
    norm_num
  have hR : ContDiffAt ℝ 2 R 0 :=
    ((hH.comp hpath).contDiffAt.sub (huvertex.comp 0 hpath.contDiffAt)).div
      ((contDiff_const.add contDiff_id).pow 2).contDiffAt (by norm_num)
  have hshift : Tendsto (fun t : ℝ ↦ 1 + t) (𝓝 0) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ ↦ 1 + t) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto (0 : ℝ)
  have hnear : Ioo (-(1 / 4 : ℝ)) (1 / 4) ∈ 𝓝 (0 : ℝ) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have hAR : A =ᶠ[𝓝 0] R := by
    filter_upwards [hnear, hshift.eventually hEq] with t ht hE
    have hI : (∫ z, w z * Real.signedPower p (u (b + (1 + t) • Z z)) ∂μ) = A t :=
      integral_congr_ae (.of_forall fun z ↦ by dsimp only; rw [← hUZ ht z])
    rw [hI] at hE
    dsimp only [R]
    apply (eq_div_iff (pow_ne_zero 2 (by linarith [ht.1] : 1 + t ≠ 0))).mpr
    generalize H (b + (1 + t) • e) = a at *
    generalize u (b + (1 + t) • e) = c at *
    generalize A t = d at *
    linarith
  have hm := integral_signedPower_nodal_moment_eq_zero_of_regular_off_zeros μ hp hp₂
    w hU.contDiffAt hU₂.contDiffAt heq (hR.congr_of_eventuallyEq hAR)
  have hderiv (z : K) : deriv U 0 z =
      deriv (fun t : ℝ ↦ u (b + (1 + t) • Z z)) 0 := by
    rw [← hUd 0 z]
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hnear] with t ht
    exact hUZ ht z
  convert hm using 1
  exact integral_congr_ae (.of_forall fun z ↦ by dsimp only; rw [hvalue z, hderiv z])

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower

end
