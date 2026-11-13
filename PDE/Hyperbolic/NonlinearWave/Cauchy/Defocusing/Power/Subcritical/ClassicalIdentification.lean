/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.LocalExtension.ForwardBand
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.ClassicalRepresentation.InteriorPower
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralLifespan
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiniteForwardSupport

/-!
# Classical and integral signed-power waves

A field with a continuously differentiable initial face and continuous second derivatives at
positive time has a bounded integral representative on each proper time prefix and agrees with
the global integral trajectory.
-/

@[expose] public noncomputable section

section

open Set Filter MeasureTheory PDE PDE.Analysis PDE.Common WaveEquation
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A forward classical candidate has an ambient C¹ representative satisfying
the integral equation on each shorter interval. No initial C² jet is required. -/
theorem exists_integral_representative_of_interior_classical_power {p L S : ℝ} (hp : 1 ≤ p)
    (hS : 0 < S) (hSL : S < L) {u : ℝ^4 → ℝ} {g h : ℝ^3 → ℝ}
    (hu : ContDiffOn ℝ 2 u {z | z 0 ∈ Ioo 0 L}) (hu₀ : ContDiffOn ℝ 1 u {z | z 0 ∈ Ico 0 L})
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hposition : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x)
    (hwave : ∀ t ∈ Ioo 0 L, ∀ x,
      waveOperator u (timeSpaceCons t x) + Real.signedPower p (u (timeSpaceCons t x)) = 0) :
    ∃ v : ℝ^4 → ℝ, ContDiff ℝ 1 v ∧ EqOn v u {z | z 0 ∈ Icc 0 S} ∧ ∀ t ∈ Ico 0 S, ∀ x : ℝ^3,
      v (timeSpaceCons t x) = cauchyFreeField g h (t, x) +
      oddDuhamelSolution 0 (fun z ↦ -Real.signedPower p (v z)) (timeSpaceCons t x) := by
  obtain ⟨w, hw, hwU⟩ := exists_contDiffOn_extension_halfOpenBand (k := 1) 0 (hS.trans hSL) hu₀
  obtain ⟨v, hv, hvw⟩ := hw.exists_contDiff_eventuallyEq_on_halfSpace
    (EuclideanSpace.proj 0 : ℝ^4 →L[ℝ] ℝ) hSL
  have heq : EqOn v u {z | z 0 ∈ Icc 0 S} :=
    fun z hz ↦ (hvw z hz.2).eq_of_nhds.symm.trans (hwU hz.1)
  have hlocal {z : ℝ^4} (hz : z 0 ∈ Ioo 0 S) : v =ᶠ[𝓝 z] u := by
    filter_upwards [((EuclideanSpace.proj 0).continuous.isOpen_preimage _ isOpen_Ioo).mem_nhds hz]
      with q hq
    exact heq ⟨hq.1.le, hq.2.le⟩
  have hv₂ : ContDiffOn ℝ 2 v {z | z 0 ∈ Ioo 0 S} :=
    (hu.mono (fun _ hz ↦ ⟨hz.1, hz.2.trans hSL⟩)).congr (fun _ hz ↦ heq ⟨hz.1.le, hz.2.le⟩)
  have hvpos (x : ℝ^3) : v (timeSpaceCons 0 x) = g x := (heq ⟨le_rfl, hS.le⟩).trans (hposition x)
  have hvvel (x : ℝ^3) : (∂[0] v) (timeSpaceCons 0 x) = h x := by
    have hd := (hasDerivAt_timeSpaceCons v 0 x
      (hv.differentiable (by norm_num) _)).hasDerivWithinAt (s := Ici 0)
    have he : (fun t ↦ v (timeSpaceCons t x)) =ᶠ[𝓝[Ici 0] 0]
        (fun t ↦ u (timeSpaceCons t x)) := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hS)]
        with t ht htS
      exact heq ⟨ht, htS.le⟩
    rw [← hd.derivWithin (uniqueDiffWithinAt_Ici 0),
      he.derivWithin_eq_of_mem (self_mem_Ici), hinitial]
  refine ⟨v, hv, heq, fun t ht x ↦ ?_⟩
  exact eq_free_add_duhamel_of_interior_classical_power hp hv hv₂ hg hh hvpos hvvel
    (fun s hs y ↦ by
      rw [waveOperator_congr_nhds (hlocal hs), (hlocal hs).eq_of_nhds]
      exact hwave s ⟨hs.1, hs.2.trans hSL⟩ y) ht x

/-- Every interior C², initial C¹ solution with the same compact data agrees
with the global C¹ integral trajectory. Amplitude bounds are derived from
finite propagation; none are imposed on the classical candidate. -/
theorem eq_global_integral_of_interior_classical_power {p b L S : ℝ} (hp : 1 ≤ p) (hb : 0 < b)
    (hS : 0 < S) (hSL : S < L) {u : ℝ^4 → ℝ} {U : ℝ × ℝ^3 → ℝ} {g h : ℝ^3 → ℝ}
    (hU : IsGlobalIntegralTrajectory p b (cauchyFreeField g h) U)
    (hu : ContDiffOn ℝ 2 u {z | z 0 ∈ Ioo 0 L}) (hu₀ : ContDiffOn ℝ 1 u {z | z 0 ∈ Ico 0 L})
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgs : HasCompactSupport g)
    (hhs : HasCompactSupport h) (hposition : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hinitial : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x)
    (hwave : ∀ t ∈ Ioo 0 L, ∀ x,
      waveOperator u (timeSpaceCons t x) + Real.signedPower p (u (timeSpaceCons t x)) = 0) :
    ∀ t ∈ Ico 0 S, ∀ x : ℝ^3, u (timeSpaceCons t x) = U (t, x) := by
  obtain ⟨v, hv, heq, hve⟩ := exists_integral_representative_of_interior_classical_power
    hp hS hSL hu hu₀ hg hh hposition hinitial hwave
  obtain ⟨B, hB, huB⟩ := exists_amplitude_bound_on_proper_strip
    (Real.contDiff_one_signedPower hp).locallyLipschitz (Real.signedPower_zero p)
    hu hu₀ hwave hposition hinitial hgs hhs hSL
  obtain ⟨A, hA, hUA⟩ := hU.bounded_before S
  let V : ℝ × ℝ^3 → ℝ := v ∘ (timeSpaceContinuousLinearEquiv 3).symm
  have hV : ContDiff ℝ 1 V := hv.comp (timeSpaceContinuousLinearEquiv 3).symm.contDiff
  have hE := eq_on_forward_interval_of_bounded_signedPower_integral_eq
    (L := S) (M := max A B) hp hb (hA.trans (le_max_left _ _)) hV.contDiffOn
    (hU.regular.mono (fun _ hz ↦ hz.1))
    (contDiff_one_cauchyFreeField (hg.of_le (by norm_num)) (hh.of_le (by norm_num)))
    (fun z hz ↦ ?_) (fun z hz ↦ (hUA z hz).trans (le_max_left _ _))
    (fun z hz ↦ ?_) (fun z hz ↦ hU.equation z hz.1)
  · intro t ht x
    have hvu := heq (show (timeSpaceCons t x) 0 ∈ Icc 0 S from ⟨ht.1, ht.2.le⟩)
    exact hvu.symm.trans (hE (t, x) ht)
  · change |v (timeSpaceCons z.1 z.2)| ≤ max A B
    rw [heq ⟨hz.1, hz.2.le⟩]
    exact (huB z.1 ⟨hz.1, hz.2.le⟩ z.2).trans (le_max_right _ _)
  · simpa only [V, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply,
      timeSpaceContinuousLinearEquiv_symm_apply, Prod.eta] using hve z.1 hz z.2

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

end
