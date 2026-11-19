/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.FinitePropagation.TruncatedEnergy.FiniteBand
import PDE.Analysis.Integration.Cone.RadiusContinuity
import PDE.FDeriv.SpaceTime

/-!
# Enlarging a cone of vanishing semilinear energy

For a nonnegative C1 potential, vanishing local energy supplies a late enlarged
cone with uniformly small energy. The field is C2 only on the open time band;
the geometric tip lies beyond that band and requires no extension of the field.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter PDE PDE.Common PDE.Analysis
open scoped ENNReal Topology

namespace WaveEquation

/-- Vanishing local energy provides an enlarged cone with uniformly small
energy up to the regularity endpoint. The geometric tip may lie beyond that endpoint. -/
theorem exists_enlarged_cone_energy_lt {V : ℝ → ℝ} (hV : ContDiff ℝ 1 V) (hVnonneg : ∀ z, 0 ≤ V z)
    {u : ℝ^4 → ℝ} {T : ℝ} (hT : 0 < T) (hu : ContDiffOn ℝ 2 u {p | 0 < p 0 ∧ p 0 < T}) (c : ℝ^3)
    (hwave : ∀ t ∈ Ioo 0 T, ∀ x : ℝ^3, semilinearWaveOperator V u (timeSpaceCons t x) = 0)
    (henergy : Tendsto (fun t ↦ ballIntegral 3
      (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons t x)) c (T - t)) (𝓝[<] T) (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ Ioo 0 T, ∃ δ > 0, ∀ t ∈ Ico s T, ballIntegral 3
      (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons t x)) c (T + δ - t) < ε := by
  have htimes : ∀ᶠ s in 𝓝[<] T, s ∈ Ioo 0 T := Ioo_mem_nhdsLT hT
  obtain ⟨s, hs, hEs⟩ := (htimes.and (henergy.eventually (eventually_lt_nhds hε))).exists
  have hopen : IsOpen {p : ℝ^4 | 0 < p 0 ∧ p 0 < T} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (EuclideanSpace.proj 0).continuous continuous_const)
  have he : Continuous (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons s x)) :=
    continuous_iff_continuousAt.mpr fun x ↦
      (contDiffAt_semilinearWaveEnergyDensity (m := 1) hV.contDiffAt
        (hu.contDiffAt (hopen.mem_nhds (by simpa using hs)))).continuousAt.comp
        (contDiff_timeSpaceCons_spatial 3 s (m := 1)).continuous.continuousAt
  have hc := continuousAt_ballIntegral_radius he c (sub_pos.mpr hs.2)
  have hd : Tendsto (fun δ : ℝ ↦ ballIntegral 3
      (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons s x)) c (T + δ - s))
      (𝓝[>] 0) (𝓝 (ballIntegral 3
        (fun x ↦ semilinearWaveEnergyDensity V u (timeSpaceCons s x)) c (T - s))) := by
    apply hc.tendsto.comp
    simpa only [add_zero] using ((tendsto_const_nhds (x := T)).add
        (show Tendsto (fun δ : ℝ ↦ δ) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds)).sub_const s
  obtain ⟨δ, hδE, hδ⟩ := ((hd.eventually (eventually_lt_nhds hEs)).and self_mem_nhdsWithin).exists
  refine ⟨s, hs, δ, hδ, fun t ht ↦ ?_⟩
  apply lt_of_le_of_lt ?_ hδE
  exact ballIntegral_energy_le_of_le_of_contDiffOn_finite_band hV hVnonneg hu c
    hs.1 ht.1 ht.2 (ht.2.trans (lt_add_of_pos_right T hδ))
    (fun q hq x _ ↦ hwave q ⟨hs.1.trans_le hq.1, hq.2.trans_lt ht.2⟩ x)

end WaveEquation
