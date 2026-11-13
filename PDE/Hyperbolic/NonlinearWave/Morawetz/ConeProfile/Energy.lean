/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Morawetz.ConeProfile.CurrentFlux
public import PDE.Hyperbolic.NonlinearWave.Morawetz.ConeEnergy
import CAS.ExactTactic

/-!
# Cone profiles supplied by the quintic equation

The finite lateral flux from local conservation pulls back by the C¹ area
formula. Its two nonnegative terms supply tangential L² and potential L⁶
integrability, hence H¹ membership and the exact completed-square identity.
Only an open time band below the tip is required.
-/

@[expose] public noncomputable section

open MeasureTheory Metric Set Filter PDE PDE.Common PDE.Analysis NormedSpace
open SobolevSpace SobolevSpace.GraphSpace
open scoped RealInnerProductSpace Sobolev

namespace WaveEquation.ConeProfile

/-- Finite lateral flux pulls back to the spatial ball, with the tip removed only as a null set. -/
theorem integrableOn_graph_of_integrableOn_cone {n : ℕ} [Fact (0 < n)] {c : ℝ^n} {s T : ℝ}
    {g : ℝ^(n + 1) → ℝ}
    (hg : IntegrableOn g {p | s ≤ p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0}
      (Measure.euclideanHausdorffMeasure n)) :
    IntegrableOn (fun x ↦ g (backwardConeGraph c T x)) (ball c (T - s)) := by
  let U := ball c (T - s) \ {c}
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have hne : ∀ x ∈ U, x ≠ c := fun _ hx ↦ hx.2
  have hsub : backwardConeGraph c T '' U ⊆
      {p | s ≤ p 0 ∧ p 0 < T ∧ ‖spatialPart p - c‖ = T - p 0} := by
    rintro _ ⟨x, hx, rfl⟩
    have hρ : ‖x - c‖ < T - s := by simpa only [mem_ball, dist_eq_norm] using hx.1
    have hpos : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx.2)
    change s ≤ T - ‖x - c‖ ∧ T - ‖x - c‖ < T ∧ ‖x - c‖ = T - (T - ‖x - c‖)
    exact ⟨by linarith, by linarith, (sub_sub_cancel T _).symm⟩
  have hi := hg.mono_set hsub
  have hf := (contDiffOn_backwardConeGraph c T).mono (fun x hx ↦ hne x hx)
  have hd : ∀ x ∈ U, Function.Injective (fderiv ℝ (backwardConeGraph c T) x) := by
    intro x hx
    rw [(hasFDerivAt_backwardConeGraph c T (hne x hx)).fderiv]
    exact coneGraphDifferential_injective _
  have hi' : IntegrableOn g (backwardConeGraph c T '' U)
      (Measure.euclideanHausdorffMeasure (Module.finrank ℝ (ℝ^n))) := by
    simpa only [finrank_euclideanSpace_fin] using hi
  have harea := (integrableOn_image_iff_integrableOn_normDet_smul_of_contDiffOn
    hU hf (backwardConeGraph_injective c T).injOn hd hi'.aestronglyMeasurable).mp hi'
  have hscaled : IntegrableOn (fun x ↦ Real.sqrt 2 * g (backwardConeGraph c T x)) U := by
    apply harea.congr
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    simp only [smul_eq_mul, normDet_fderiv_backwardConeGraph c T (hne x hx)]
  have hplain : IntegrableOn (fun x ↦ g (backwardConeGraph c T x)) U :=
    (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))) _).mp
      hscaled
  let : Nontrivial (ℝ^n) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa using (Fact.out : 0 < n))
  exact (integrableOn_congr_set_ae (sdiff_null_ae_eq_self (measure_singleton c))).mp hplain

/-- The cone gradient differs by a sign from the vector in the physical null flux. -/
theorem cone_dissipation_graph_eq {n : ℕ} (V : ℝ → ℝ) (T : ℝ) (c : ℝ^n) (u : ℝ^(n + 1) → ℝ)
    (x : ℝ^n) :
    semilinearWaveConeDissipation V u c (backwardConeGraph c T x) =
      (1 / 2 : ℝ) * ‖coneProfileGradient T c u x‖ ^ 2 + V (coneProfile T c u x) := by
  have hvec : (∂[0] u) (backwardConeGraph c T x) • normalize (x - c) -
      classicalWaveSpatialGradient u (backwardConeGraph c T x) =
        -coneProfileGradient T c u x := by
    ext i
    simp only [coneProfileGradient, classicalWaveSpatialGradient, backwardConeGraph,
      PiLp.sub_apply, PiLp.smul_apply, PiLp.neg_apply, smul_eq_mul]
    ring
  unfold semilinearWaveConeDissipation semilinearWaveNullFlux
  simp only [backwardConeGraph, spatialPart_timeSpaceCons] at hvec ⊢
  rw [hvec, norm_neg]
  rfl

/-- Ambient C² regularity below the tip gives the punctured closed-ball C¹ profile hypothesis. -/
theorem contDiffAt_cone_of_band {n : ℕ} {u : ℝ^(n + 1) → ℝ} {s₀ s T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T}) (hs : s₀ < s) (c : ℝ^n) {x : ℝ^n}
    (hx : x ∈ closedBall c (T - s)) (hne : x ≠ c) :
    ContDiffAt ℝ 1 u (timeSpaceCons (T - ‖x - c‖) x) := by
  have hopen : IsOpen {p : ℝ^(n + 1) | s₀ < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have hρ : ‖x - c‖ ≤ T - s := by simpa only [mem_closedBall, dist_eq_norm] using hx
  have hpos := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  apply (hu.contDiffAt (hopen.mem_nhds ?_)).of_le (by norm_num)
  change s₀ < T - ‖x - c‖ ∧ T - ‖x - c‖ < T
  constructor <;> linarith

/-- The quintic equation supplies both cone densities. -/
theorem integrable_densities_of_wave {u : ℝ^4 → ℝ} {s₀ s T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T}) (c : ℝ^3) (hs : s₀ < s)
    (hwave : ∀ t ∈ Ico s T, ∀ x ∈ ball c (T - t), waveOperator u (timeSpaceCons t x) +
      u (timeSpaceCons t x) ^ 5 = 0) :
    IntegrableOn (fun x ↦ ‖coneProfileGradient T c u x‖ ^ 2) (ball c (T - s)) ∧
      IntegrableOn (fun x ↦ coneProfile T c u x ^ 6) (ball c (T - s)) := by
  let : Fact (0 < 3) := ⟨by omega⟩
  have hV := Real.contDiff_one_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5)
  have hpos := fun z ↦ Real.signedPowerPotential_nonneg (by norm_num : (1 : ℝ) ≤ 5) z
  have hi := integrableOn_cone_dissipation hV hpos hu c hs (by
    intro t ht x hx
    unfold semilinearWaveOperator
    rw [(Real.hasDerivAt_signedPowerPotential (by norm_num : (1 : ℝ) ≤ 5) _).deriv]
    unfold Real.signedPower
    rw [show (5 : ℝ) - 1 = (4 : ℕ) by norm_num, Real.rpow_natCast,
      (show Even 4 by decide).pow_abs]
    have hw := hwave t ht x hx
    convert hw using 1; cas)
  have hg := integrableOn_graph_of_integrableOn_cone hi
  have hsum : IntegrableOn (fun x ↦ (1 / 2 : ℝ) * ‖coneProfileGradient T c u x‖ ^ 2 +
      (1 / 6 : ℝ) * coneProfile T c u x ^ 6) (ball c (T - s)) := by
    apply hg.congr
    apply Eventually.of_forall
    intro x
    change semilinearWaveConeDissipation (Real.signedPowerPotential 5) u c
      (backwardConeGraph c T x) = _
    rw [cone_dissipation_graph_eq]
    norm_num [Real.signedPowerPotential, Real.rpow_ofNat, (show Even 6 by decide).pow_abs,
      div_eq_mul_inv, mul_comm]
  let U := ball c (T - s) \ {c}
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_singleton
  have hregular : ∀ x ∈ U, ContDiffAt ℝ 1 u (timeSpaceCons (T - ‖x - c‖) x) :=
    fun x hx ↦ contDiffAt_cone_of_band hu hs c (ball_subset_closedBall hx.1) hx.2
  have hGc : ContinuousOn (coneProfileGradient T c u) U := by
    have hcoords : ContinuousOn (fun x ↦ fun i : Fin 3 ↦ (∂[i] (coneProfile T c u)) x) U :=
      continuousOn_pi.mpr fun i x hx ↦ ((contDiffAt_partialDeriv 0
          (contDiffAt_coneProfile hx.2 (hregular x hx)) i).continuousAt).continuousWithinAt
    apply ((PiLp.continuous_toLp 2 (fun _ : Fin 3 ↦ ℝ)).comp_continuousOn hcoords).congr
    intro x hx
    apply PiLp.ext
    intro i
    exact (partialDeriv_coneProfile hx.2 ((hregular x hx).differentiableAt one_ne_zero) i).symm
  have hm : AEStronglyMeasurable
      (fun x ↦ (1 / 2 : ℝ) * ‖coneProfileGradient T c u x‖ ^ 2) (volume.restrict U) :=
    (continuousOn_const.mul (hGc.norm.pow 2)).aestronglyMeasurable hU.measurableSet
  obtain ⟨hG, hW⟩ := (integrable_add_iff_of_nonneg hm
    (ae_of_all _ fun x ↦ by positivity) (ae_of_all _ fun x ↦ by positivity)).mp
      (hsum.mono_set (show U ⊆ ball c (T - s) from sdiff_subset))
  have hG' := (integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (by norm_num : (1 / 2 : ℝ) ≠ 0)) _).mp hG
  have hW' := (integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (by norm_num : (1 / 6 : ℝ) ≠ 0)) _).mp hW
  exact ⟨(integrableOn_congr_set_ae (sdiff_null_ae_eq_self (measure_singleton c))).mp hG',
    (integrableOn_congr_set_ae (sdiff_null_ae_eq_self (measure_singleton c))).mp hW'⟩

/-- Finite cone energy constructs an H¹ profile and identifies its weak gradient. -/
theorem exists_h1_of_wave {u : ℝ^4 → ℝ} {s₀ s T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T}) (c : ℝ^3) (hs : s₀ < s)
    (hwave : ∀ t ∈ Ico s T, ∀ x ∈ ball c (T - t), waveOperator u (timeSpaceCons t x) +
      u (timeSpaceCons t x) ^ 5 = 0) :
    ∃ U : H¹(ball c (T - s)), baseRepresentative U =ᵐ[domainMeasure 3 (ball c (T - s))] coneProfile
      T c u ∧ (∇ U : ℝ^3 → ℝ^3) =ᵐ[domainMeasure 3 (ball c (T - s))] coneProfileGradient T c u := by
  obtain ⟨hg, hp⟩ := integrable_densities_of_wave hu c hs hwave
  exact exists_h1_of_integrable_densities (by omega : 2 ≤ 3)
    (fun x hx hne ↦ contDiffAt_cone_of_band hu hs c (ball_subset_closedBall hx) hne) hg hp

/-- The quintic solution satisfies the exact cone-current square identity below its tip. -/
theorem integral_scalingFlux_eq_boundary_sub_square_of_wave {u : ℝ^4 → ℝ} {s₀ s T : ℝ}
    (hu : ContDiffOn ℝ 2 u {p | s₀ < p 0 ∧ p 0 < T}) (c : ℝ^3) (hs : s₀ < s) (hsT : s < T)
    (hwave : ∀ t ∈ Ico s T, ∀ x ∈ ball c (T - t), waveOperator u (timeSpaceCons t x) +
      u (timeSpaceCons t x) ^ 5 = 0) :
    (∫ x in ball c (T - s), coneProfileScalingFlux (Real.signedPowerPotential 5) 1 T c u x) =
      (1 / 2 : ℝ) * sphereIntegral 3 (fun x ↦ coneProfile T c u x ^ 2) c (T - s) -
        ∫ x in ball c (T - s), ‖x - c‖ *
          (⟪coneProfileGradient T c u x, normalize (x - c)⟫ +
            coneProfile T c u x / ‖x - c‖) ^ 2 := by
  obtain ⟨hg, hp⟩ := integrable_densities_of_wave hu c hs hwave
  exact integral_scalingFlux_eq_boundary_sub_square (Real.signedPowerPotential 5) (sub_pos.mpr hsT)
    (fun _ hx hne ↦ contDiffAt_cone_of_band hu hs c hx hne) hg hp

end WaveEquation.ConeProfile
