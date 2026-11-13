/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.CompactData.Domination
public import PDE.Hyperbolic.NonlinearWave.SmallData.Mass
public import PDE.Analysis.Calculus.SpaceTime.ForwardDerivative

/-!
# Energy at the initial boundary of a forward wave

The continuous differential within the closed forward half-space identifies the
initial energy with the displacement gradient and right velocity. Finite
propagation places all nearby energy densities in one compact ball, so the
spatial energy tends to this data energy from positive time.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common PDE.Analysis
open scoped Topology BigOperators

namespace WaveEquation.NegativeEnergy

variable {n : ℕ}

/-- Energy density expressed through the continuous forward differential.
Clipping time is used only to express continuity at the initial boundary. -/
def forwardEnergyDensity (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ) (t : ℝ) (x : ℝ^n) : ℝ :=
  (1 / 2 : ℝ) * ((forwardDifferential u t x (EuclideanSpace.single 0 1)) ^ 2 +
    ∑ i : Fin n, (forwardDifferential u t x (EuclideanSpace.single i.succ 1)) ^ 2) +
      V (u (timeSpaceCons (max 0 t) x))

/-- The forward energy density is jointly continuous through initial time. -/
theorem continuous_forwardEnergyDensity {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hV : Continuous V) (hu : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) :
    Continuous (Function.uncurry (forwardEnergyDensity V u)) := by
  have hD := continuous_forwardDifferential hu
  apply Continuous.add
  · apply continuous_const.mul
    apply Continuous.add
    · exact (hD.clm_apply continuous_const).pow 2
    · exact continuous_finsetSum _ (fun _ _ ↦ (hD.clm_apply continuous_const).pow 2)
  · apply hV.comp
    apply hu.continuousOn.comp_continuous
      ((contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
        ((continuous_const.max continuous_fst).prodMk continuous_snd))
    exact fun p ↦ le_max_left 0 p.1

/-- At positive times, the forward density is the PDE energy density. -/
theorem forwardEnergyDensity_eq {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {t : ℝ} (ht : 0 < t) (x : ℝ^n) :
    forwardEnergyDensity V u t x = semilinearWaveSpatialEnergyDensity V u t x := by
  simp only [forwardEnergyDensity, forwardDifferential_eq_fderiv u ht x,
    max_eq_right ht.le, semilinearWaveSpatialEnergyDensity, semilinearWaveEnergyDensity,
    classicalWaveEnergyDensity, classicalWaveSpatialGradient, EuclideanSpace.real_norm_sq_eq,
    PDE.partialDeriv]

/-- Initial displacement and right velocity determine the forward energy density.
No ordinary derivative across negative time is used. -/
theorem forwardEnergyDensity_initial {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {g h : ℝ^n → ℝ}
    (hu : ContDiffOn ℝ 1 u {p | 0 ≤ p 0}) (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x) (x : ℝ^n) :
    forwardEnergyDensity V u 0 x =
      (1 / 2 : ℝ) * ((h x) ^ 2 + ∑ i : Fin n, ((∂[i] g) x) ^ 2) + V (g x) := by
  let D := fderivWithin ℝ u {p | 0 ≤ p 0} (timeSpaceCons 0 x)
  have hD : HasFDerivWithinAt u D {p | 0 ≤ p 0} (timeSpaceCons 0 x) :=
    (hu.differentiableOn_one _ (by simp)).hasFDerivWithinAt
  have ht : D (EuclideanSpace.single 0 1) = h x := by
    have hd := hD.comp_hasDerivWithinAt 0 (hasDerivAt_timeSpaceCons_time n 0 x).hasDerivWithinAt
      (show MapsTo (fun t ↦ timeSpaceCons t x) (Ici 0) {p | 0 ≤ p 0} from
        fun t ht ↦ by simpa using ht)
    exact (hd.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans (hvel x)
  have hs : D.comp (embedWithTimeZeroCLM n) = fderiv ℝ g x := by
    have hd := hD.comp_hasFDerivAt x (hasFDerivAt_timeSpaceCons_spatial n 0 x)
      (Eventually.of_forall fun y ↦
        (show (0 : ℝ) ≤ (timeSpaceCons 0 y) 0 by simp))
    exact (hd.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ (hpos y).symm)).fderiv.symm
  have hsi (i : Fin n) : D (EuclideanSpace.single i.succ 1) = (∂[i] g) x := by
    have he := congrArg (fun L : ℝ^n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1)) hs
    simpa [PDE.partialDeriv] using he
  unfold forwardEnergyDensity forwardDifferential
  rw [max_self]
  change (1 / 2 : ℝ) * ((D (EuclideanSpace.single 0 1)) ^ 2 +
    ∑ i : Fin n, (D (EuclideanSpace.single i.succ 1)) ^ 2) + V (u (timeSpaceCons 0 x)) = _
  simp only [ht, hsi, hpos]

/-- The total energy tends to the Cauchy-data energy from the right.
Compact support is propagated by the field. -/
theorem tendsto_semilinearWaveSpatialEnergy_initial {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {g h : ℝ^n → ℝ}
    {R : ℝ} (hV : Continuous V) (hVzero : V 0 = 0) (hu : ContDiffOn ℝ 1 u {p | 0 ≤ p 0})
    (hs : SmallData.HasForwardSupport u R) (hpos : ∀ x, u (timeSpaceCons 0 x) = g x)
    (hvel : ∀ x, derivWithin (fun t ↦ u (timeSpaceCons t x)) (Ici 0) 0 = h x)
    (hh : ∀ x, R < ‖x‖ → h x = 0) :
    Tendsto (semilinearWaveSpatialEnergy V u) (𝓝[>] 0)
      (𝓝 (∫ x : ℝ^n, (1 / 2 : ℝ) * ((h x) ^ 2 + ∑ i : Fin n, ((∂[i] g) x) ^ 2) + V (g x))) := by
  let K := Metric.closedBall (0 : ℝ^n) (R + 1)
  let F : ℝ → ℝ := fun t ↦ ∫ x in K, forwardEnergyDensity V u t x
  have hF : Continuous F := continuous_parametric_integral_of_continuous
    (continuous_forwardEnergyDensity hV hu) (isCompact_closedBall _ _)
  have hinitial (x : ℝ^n) (hx : R < ‖x‖) : forwardEnergyDensity V u 0 x = 0 := by
    have hD := forwardDifferential_initial_eq_zero hu (isOpen_lt continuous_const continuous_norm)
      (fun y hy ↦ hs 0 le_rfl y (by simpa using hy)) (fun y hy ↦ (hvel y).trans (hh y hy)) hx
    simp [forwardEnergyDensity, hD, hs 0 le_rfl x (by simpa using hx), hVzero]
  have hFzero : F 0 = ∫ x : ℝ^n, (1 / 2 : ℝ) *
      ((h x) ^ 2 + ∑ i : Fin n, ((∂[i] g) x) ^ 2) + V (g x) := by
    have he := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (f := forwardEnergyDensity V u 0) (s := K) (fun x hx ↦ ?_)
    · change (∫ x in K, forwardEnergyDensity V u 0 x) = _
      rw [he]
      exact integral_congr_ae (Eventually.of_forall (forwardEnergyDensity_initial hu hpos hvel))
    · apply hinitial
      have hx' : R + 1 < ‖x‖ := by
        simpa only [K, Metric.mem_closedBall, dist_zero_right, not_le] using hx
      linarith
  have heq : semilinearWaveSpatialEnergy V u =ᶠ[𝓝[>] 0] F := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with t ht ht1
    change (∫ x : ℝ^n, semilinearWaveSpatialEnergyDensity V u t x) = _
    have he := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
      (f := semilinearWaveSpatialEnergyDensity V u t) (s := K) (fun x hx ↦ ?_)
    · rw [← he]
      apply setIntegral_congr_fun measurableSet_closedBall
      exact fun x _ ↦ (forwardEnergyDensity_eq ht x).symm
    · have hx' : R + 1 < ‖x‖ := by
        simpa only [K, Metric.mem_closedBall, dist_zero_right, not_le] using hx
      exact (semilinearWaveEnergyDensity_eventuallyEq_zero hVzero
        (eventuallyEq_zero_of_cone_support (fun r hr ↦ hs r hr.le) ht
          (show R + t < ‖x‖ by linarith [show t < 1 from ht1]))).eq_of_nhds
  rw [← hFzero]
  exact (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm

end WaveEquation.NegativeEnergy
