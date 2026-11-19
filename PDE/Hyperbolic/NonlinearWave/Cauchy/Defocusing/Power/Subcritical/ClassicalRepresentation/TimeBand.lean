/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Analysis.Calculus.LocalExtension.TimeBand
public import PDE.Hyperbolic.Models.Wave.Duhamel.OneDimension.ClassicalSolution
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.ClassicalRepresentation
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FiniteForwardUniqueness
public import PDE.Hyperbolic.NonlinearWave.SmallData.StraussCritical.SphericalReduction

/-!
# Spherical reduction on an open time band

Spherical means preserve interior second derivatives and the wave equation using local time-band
representatives.
-/

@[expose] public noncomputable section

section

open Set Filter MeasureTheory PDE PDE.Analysis PDE.Common WaveEquation
open WaveEquation.SmallData
open PDE.Hyperbolic.NonlinearWave.Cauchy
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

private theorem radiusMean_eventuallyEq_of_eqOn_band {u v : ℝ^4 → ℝ} {a b : ℝ}
    (he : ∀ t ∈ Ioo a b, ∀ x : ℝ^3, u (timeSpaceCons t x) = v (timeSpaceCons t x))
    {z : ℝ^2} (hz : z 0 ∈ Ioo a b) : radiusMean u =ᶠ[𝓝 z] radiusMean v := by
  filter_upwards [((EuclideanSpace.proj 0).continuous.isOpen_preimage _ isOpen_Ioo).mem_nhds hz]
    with q hq
  unfold radiusMean waveSphericalMean unitSphereAverage
  congr 2
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ω ↦ he (q 0) hq _

/-- Localizing in time gives both the spherical mean and a smooth
representative near each positive-time slice. -/
private theorem exists_radiusMean_germ {u : ℝ^4 → ℝ} {L t : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | z 0 ∈ Ioo 0 L}) (ht : t ∈ Ioo 0 L) :
    ∃ v : ℝ^4 → ℝ, ContDiff ℝ 2 v ∧ (∀ x : ℝ^3, u =ᶠ[𝓝 (timeSpaceCons t x)] v) ∧ ∀ x : ℝ^1,
      radiusMean u =ᶠ[𝓝 (timeSpaceCons t x)] radiusMean v := by
  let a := t / 2
  let b := (t + L) / 2
  have ha : 0 < a := half_pos ht.1
  have hat : a < t := half_lt_self ht.1
  have htb : t < b := by dsimp only [b]; linarith [ht.2]
  have hb : b < L := by dsimp only [b]; linarith [ht.2]
  obtain ⟨v, hv, he⟩ := ContDiffOn.exists_contDiff_eventuallyEq_on_band (k := (2 : ℕ∞)) (f := u)
    (EuclideanSpace.proj (0 : Fin 4))
    (show ContDiffOn ℝ (2 : ℕ∞) u {z | 0 < z 0 ∧ z 0 < L} from hu) ha hb
  refine ⟨v, hv, fun x ↦ he _ ⟨hat.le, htb.le⟩, fun x ↦ ?_⟩
  apply radiusMean_eventuallyEq_of_eqOn_band (a := a) (b := b)
  · exact fun s hs y ↦ (he (timeSpaceCons s y) ⟨hs.1.le, hs.2.le⟩).eq_of_nhds
  · exact ⟨hat, htb⟩

/-- Spherical reduction preserves second regularity on the positive open band. -/
theorem contDiffOn_two_radiusMean {u : ℝ^4 → ℝ} {L : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | z 0 ∈ Ioo 0 L}) :
    ContDiffOn ℝ 2 (radiusMean u) {z | z 0 ∈ Ioo 0 L} := by
  intro z hz
  obtain ⟨v, hv, _, he⟩ := exists_radiusMean_germ hu hz
  have hz' : timeSpaceCons (z 0) (spatialPartCLM 1 z) = z := timeSpaceCons_spatialPartCLM z
  have hlocal := he (spatialPartCLM 1 z)
  rw [hz'] at hlocal
  exact ((contDiff_radiusMean hv).contDiffAt.congr_of_eventuallyEq hlocal).contDiffWithinAt

/-- The reduced PDE needs second derivatives only near its positive-time slice. -/
theorem waveOperator_radiusMean_on_open_band {u f : ℝ^4 → ℝ} {L t : ℝ}
    (hu : ContDiffOn ℝ 2 u {z | z 0 ∈ Ioo 0 L}) (hf : Continuous f) (ht : t ∈ Ioo 0 L)
    (hw : ∀ x : ℝ^3, waveOperator u (timeSpaceCons t x) = f (timeSpaceCons t x)) (x : ℝ^1) :
    waveOperator (radiusMean u) (timeSpaceCons t x) = radiusMean f (timeSpaceCons t x) := by
  obtain ⟨v, hv, he, hr⟩ := exists_radiusMean_germ hu ht
  rw [waveOperator_congr_nhds (hr x)]
  have hx : EuclideanSpace.single (0 : Fin 1) (x 0) = x := by
    ext i
    fin_cases i
    simp
  have hp := waveOperator_radiusMean hv hf (fun y ↦ by
    rw [← waveOperator_congr_nhds (he y)]
    exact hw y) (x 0)
  simpa only [hx] using hp

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

end
