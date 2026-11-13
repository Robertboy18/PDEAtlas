/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.FreeWeakEquation
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralWeakEquation
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.LocalTrajectory
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.RetardedOverlap
import PDE.FDeriv.Laplacian.Congruence
import PDE.FDeriv.Laplacian.Continuity
import CAS.ExactTactic

/-!
# The tested PDE of the constructed signed-power trajectory

The C¹ physical integral trajectory satisfies the nonlinear wave equation after
every compact C² spatial test. Localization to a shorter initial time band removes any global
regularity hypothesis on the trajectory. Both Cauchy traces come from the construction with
arbitrary compact data.

The conclusion is a weak spatial equation with a second time derivative
of each tested displacement.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData.Classical.LocalPower
open scoped Topology unitInterval Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- The C¹ signed-power integral equation implies the spatially tested
wave equation at each positive interior time. -/
theorem hasDerivAt_deriv_integral_of_signedPower_integral_eq {r b L : ℝ} (hr : 1 ≤ r) (hb : 0 < b)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) {u : ℝ × ℝ^3 → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | -b < p.1 ∧ p.1 < L})
    (heq : ∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 L → u p = cauchyFreeField g h p +
      oddDuhamelSolution 0 (fun z : ℝ^4 ↦
      -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z))) (timeSpaceCons p.1 p.2))
    {φ : ℝ^3 → ℝ} (hφ : ContDiff ℝ 2 φ) (hφs : HasCompactSupport φ) {t : ℝ} (ht : t ∈ Ioo 0 L) :
    HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x)) ((∫ x : ℝ^3, u (t, x) * laplacian φ x) -
      ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) t := by
  obtain ⟨a, hta, haL⟩ := exists_between ht.2
  obtain ⟨U, hU, hUeq⟩ := exists_contDiff_representative_on_initial_band hb hu haL
  let H := cauchyFreeField g h
  let F : ℝ × ℝ^3 → ℝ := fun p ↦ -Real.signedPower r (U p)
  let D : ℝ × ℝ^3 → ℝ := fun p ↦ oddDuhamelSolution 0
    (fun z : ℝ^4 ↦ F (timeSpaceContinuousLinearEquiv 3 z)) (timeSpaceCons p.1 p.2)
  have hH : ContDiff ℝ 1 H := contDiff_one_cauchyFreeField
    (hg.of_le (by norm_num)) (hh.of_le (by norm_num))
  have hF : Continuous F := ((Real.contDiff_one_signedPower hr).comp hU).continuous.neg
  have hpoint (s : ℝ) (hs : s ∈ Icc 0 a) (x : ℝ^3) :
      D (s, x) = U (s, x) - H (s, x) := by
    have hc := oddDuhamelSolution_congr_forward (F := F)
      (G := fun p ↦ -Real.signedPower r (u p)) (s, x) hs.1
      (fun q hq y ↦ congrArg (fun z ↦ -Real.signedPower r z) (hUeq (q, y) ⟨hq.1, hq.2.trans hs.2⟩))
    change D (s, x) = _ at hc
    rw [hc, hUeq (s, x) hs, heq (s, x) ⟨hs.1, hs.2.trans_lt haL⟩]
    exact (add_sub_cancel_left _ _).symm
  let A : ℝ → ℝ := fun s ↦ ∫ x : ℝ^3, U (s, x) * φ x
  let B : ℝ → ℝ := fun s ↦ ∫ x : ℝ^3, H (s, x) * φ x
  let C : ℝ → ℝ := fun s ↦ ∫ x : ℝ^3, D (s, x) * φ x
  have hA : Differentiable ℝ A := fun s ↦
    (hasDerivAt_integral_mul_spatial_test hU hφ.continuous hφs s).differentiableAt
  have hB : Differentiable ℝ B := fun s ↦
    (hasDerivAt_integral_mul_spatial_test hH hφ.continuous hφs s).differentiableAt
  have hpair {ψ : ℝ^3 → ℝ} (hψ : Continuous ψ) (hψs : HasCompactSupport ψ)
      {s : ℝ} (hs : s ∈ Icc 0 a) : (∫ x : ℝ^3, D (s, x) * ψ x) =
        (∫ x : ℝ^3, U (s, x) * ψ x) - ∫ x : ℝ^3, H (s, x) * ψ x := by
    simp_rw [hpoint s hs, sub_mul]
    exact integral_sub (Continuous.integrable_of_hasCompactSupport
        ((hU.continuous.comp (continuous_const.prodMk continuous_id)).mul hψ) hψs.mul_left)
      (Continuous.integrable_of_hasCompactSupport
        ((hH.continuous.comp (continuous_const.prodMk continuous_id)).mul hψ) hψs.mul_left)
  have hCnear : C =ᶠ[𝓝 t] fun s ↦ A s - B s := by
    filter_upwards [Ioo_mem_nhds ht.1 hta] with s hs
    exact hpair hφ.continuous hφs ⟨hs.1.le, hs.2.le⟩
  have hderiv : (fun s ↦ deriv B s + deriv C s) =ᶠ[𝓝 t] deriv A := by
    filter_upwards [hCnear.deriv] with s hs
    rw [hs]
    change deriv B s + deriv (A - B) s = deriv A s
    rw [deriv_sub (hA s) (hB s)]
    cas
  have hsource := hasDerivAt_deriv_integral_oddDuhamelSolution_mul hF hφ hφs ht.1
  change HasDerivAt (deriv C) _ t at hsource
  have hfree := hasDerivAt_deriv_integral_cauchyFreeField hg hh hφ hφs ht.1
  change HasDerivAt (deriv B) _ t at hfree
  have htested := (hfree.add hsource).congr_of_eventuallyEq hderiv.symm
  have hUNE : (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x) =ᶠ[𝓝 t] A := by
    filter_upwards [Ioo_mem_nhds ht.1 hta] with s hs
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hUeq (s, x) ⟨hs.1.le, hs.2.le⟩]
  apply (htested.congr_of_eventuallyEq hUNE.deriv).congr_deriv
  change (∫ x : ℝ^3, H (t, x) * laplacian φ x) +
    ((∫ x : ℝ^3, F (t, x) * φ x) + (∫ x : ℝ^3, D (t, x) * laplacian φ x)) = _
  rw [hpair hφ.continuous_coordinate_laplacian hφs.coordinate_laplacian ⟨ht.1.le, hta.le⟩]
  simp only [F, hUeq (t, _) ⟨ht.1.le, hta.le⟩, neg_mul, integral_neg]
  cas

/-- Every real signed power of exponent at least one and arbitrary compact C³
and C² Cauchy data construct a C¹ trajectory with both ordinary initial traces
and the spatially tested nonlinear wave equation. -/
theorem exists_signedPower_weak_trajectory_of_compact_data {r : ℝ} (hr : 1 ≤ r)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    (hgs : HasCompactSupport g) (hhs : HasCompactSupport h) :
    ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ × ℝ^3 → ℝ,
      ContDiffOn ℝ 1 u {p | |p.1| < T} ∧
      (∀ x : ℝ^3, u (0, x) = g x) ∧
      (∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0) ∧
      (∀ p : ℝ × ℝ^3, p.1 ∈ Ico 0 T →
        u p = cauchyFreeField g h p + oddDuhamelSolution 0
          (fun z : ℝ^4 ↦ -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z)))
          (timeSpaceCons p.1 p.2)) ∧
      ∀ φ : ℝ^3 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
        ∀ t ∈ Ioo 0 T,
          HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x))
            ((∫ x : ℝ^3, u (t, x) * laplacian φ x) -
              ∫ x : ℝ^3, Real.signedPower r (u (t, x)) * φ x) t := by
  obtain ⟨T, hT, u, a, hu, _, hu0, hut, heq, hrem⟩ :=
    exists_signedPower_trajectory_of_compact_data hr
      (hg.of_le (by norm_num)) (hh.of_le (by norm_num)) hgs hhs
  have hphysical (p : ℝ × ℝ^3) (hp : p.1 ∈ Ico 0 T) :
      u p = cauchyFreeField g h p + oddDuhamelSolution 0
        (fun z : ℝ^4 ↦ -Real.signedPower r (u (timeSpaceContinuousLinearEquiv 3 z)))
        (timeSpaceCons p.1 p.2) := by
    rw [heq p (by simpa only [abs_of_nonneg hp.1] using hp.2), hrem p hp,
      oddDuhamelSolution_zero_eq_normalized _ _ hp.1]
    simp only [timeSpaceContinuousLinearEquiv_apply, PDE.time, timeSpaceCons_zero,
      spatialPart_timeSpaceCons]
  refine ⟨T, hT, u, hu, hu0, hut, hphysical, fun φ hφ hφs t ht ↦ ?_⟩
  apply hasDerivAt_deriv_integral_of_signedPower_integral_eq hr hT hg hh
    (hu.mono (fun p hp ↦ abs_lt.mpr hp)) hphysical hφ hφs ht

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
