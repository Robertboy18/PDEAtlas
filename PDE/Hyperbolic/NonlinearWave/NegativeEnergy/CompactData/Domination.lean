/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import PDE.FDeriv.Calculus
public import PDE.Hyperbolic.NonlinearWave.DominatedData
import PDE.FDeriv.SpaceTime

/-!
# Integral domination from finite propagation

On every compact time interval, a continuous density supported in an expanding
ball is bounded by an integrable constant times the indicator of a fixed ball.
This constructs the virial and energy data from support and regularity.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set PDE.Common
open scoped Topology

namespace WaveEquation.NegativeEnergy

variable {n : ℕ}

/-- Vanishing outside a forward cone is a spacetime germ away from its boundary. -/
theorem eventuallyEq_zero_of_cone_support {u : ℝ^(n + 1) → ℝ} {a R t : ℝ}
    (hs : ∀ r, a < r → ∀ x, R + r < ‖x‖ → u (timeSpaceCons r x) = 0)
    (ht : a < t) {x : ℝ^n} (hx : R + t < ‖x‖) :
    u =ᶠ[𝓝 (timeSpaceCons t x)] fun _ ↦ 0 := by
  have hopen : IsOpen {p : ℝ^(n + 1) | a < p 0 ∧ R + p 0 < ‖spatialPart p‖} :=
    (isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous).inter
      (isOpen_lt (continuous_const.add (EuclideanSpace.proj 0).continuous)
        (spatialPartCLM n).continuous.norm)
  filter_upwards [hopen.mem_nhds (show a < (timeSpaceCons t x) 0 ∧
      R + (timeSpaceCons t x) 0 < ‖spatialPart (timeSpaceCons t x)‖ by
        simpa using And.intro ht hx)] with p hp
  simpa using hs (p 0) hp.1 (spatialPart p) hp.2

/-- A continuous cone-supported density has a spatial integrable majorant near
any time strictly above the initial slice. -/
theorem exists_integrable_majorant_of_cone_support {F : ℝ^(n + 1) → ℝ} {a R t : ℝ}
    (hF : Continuous F) (hs : ∀ r, a < r → ∀ x, R + r < ‖x‖ → F (timeSpaceCons r x) = 0)
    (ht : a < t) :
    ∃ s ∈ 𝓝 t, ∃ b : ℝ^n → ℝ, Integrable b ∧ ∀ r ∈ s, ∀ x, ‖F (timeSpaceCons r x)‖ ≤ b x := by
  let K := Metric.closedBall (0 : ℝ^n) (R + (t + 1))
  obtain ⟨M, _, hbound⟩ := exists_norm_le_on_timeSpaceCylinder F hF a (t + 1) 0 (R + (t + 1))
  refine ⟨Ioo a (t + 1), Ioo_mem_nhds ht (by linarith), K.indicator (fun _ ↦ M), ?_, ?_⟩
  · exact (integrable_indicator_iff measurableSet_closedBall).2
      (integrableOn_const (μ := (volume : Measure (ℝ^n))) (C := M)
        (isCompact_closedBall (0 : ℝ^n) (R + (t + 1))).measure_ne_top)
  · intro r hr x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
      exact hbound r ⟨hr.1.le, hr.2.le⟩ x hx
    · rw [indicator_of_notMem hx, hs r hr.1 x, norm_zero]
      have hx' : R + (t + 1) < ‖x‖ := by
        simpa only [K, Metric.mem_closedBall, dist_zero_right, not_le] using hx
      linarith [hr.2]

/-- Choose majorants at all times, imposing neighborhood conditions only above `a`. -/
theorem exists_integrable_majorants_of_cone_support {F : ℝ^(n + 1) → ℝ} {a R : ℝ}
    (hF : Continuous F) (hs : ∀ r, a < r → ∀ x, R + r < ‖x‖ → F (timeSpaceCons r x) = 0) :
    ∀ t, ∃ s : Set ℝ, ∃ b : ℝ^n → ℝ, (a < t → s ∈ 𝓝 t) ∧ Integrable b ∧
      (a < t → ∀ r ∈ s, ∀ x, ‖F (timeSpaceCons r x)‖ ≤ b x) := by
  intro t
  by_cases ht : a < t
  · obtain ⟨s, hs, b, hb, hbound⟩ := exists_integrable_majorant_of_cone_support hF hs ht
    exact ⟨s, b, fun _ ↦ hs, hb, fun _ ↦ hbound⟩
  · exact ⟨∅, 0, fun h ↦ (ht h).elim, integrable_zero _ _ _, fun h ↦ (ht h).elim⟩

/-- Compact support and the two virial majorants follow from a C² field's
forward support cone. The neighborhoods stay above `a`. -/
def dominatedVirialDataOfConeSupport
    {u : ℝ^(n + 1) → ℝ} {a R : ℝ} (hu : ContDiff ℝ 2 u)
    (hs : ∀ r, a < r → ∀ x, R + r < ‖x‖ → u (timeSpaceCons r x) = 0) :
    DominatedVirialData u (Ioi a) := by
  have hu₁ : ContDiff ℝ 1 (∂[0] u) := PDE.contDiff_partialDeriv_of_succ hu
  have hu₂ : Continuous (∂[0] (∂[0] u)) :=
    (PDE.contDiff_partialDeriv_of_succ (m := 0) hu₁).continuous
  have htime (r : ℝ) (hr : a < r) (x : ℝ^n) (hx : R + r < ‖x‖) :
      (∂[0] u) (timeSpaceCons r x) = 0 := by
    rw [PDE.partialDeriv_congr_nhds 0 (eventuallyEq_zero_of_cone_support hs hr hx)]
    exact PDE.partialDeriv_const 0
  choose sm bm hm him hbm using exists_integrable_majorants_of_cone_support (a := a) (R := R)
    (hu.continuous.mul hu₁.continuous)
    (fun r hr x hx ↦ by simp [hs r hr x hx])
  choose sp bp hp hip hbp using exists_integrable_majorants_of_cone_support (a := a) (R := R)
    ((hu₁.continuous.pow 2).add (hu.continuous.mul hu₂))
    (fun r hr x hx ↦ by simp [hs r hr x hx, htime r hr x hx])
  exact {
    massNeighborhood := sm
    massBound := bm
    momentumNeighborhood := sp
    momentumBound := bp
    compact_support := fun t ht ↦ HasCompactSupport.intro
      (isCompact_closedBall (0 : ℝ^n) (R + t)) (fun x hx ↦ hs t ht x
        (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx))
    mass_mem_nhds := fun t ht ↦ hm t ht
    mass_dominated := fun t ht ↦ Eventually.of_forall (fun x r hr ↦ hbm t ht r hr x)
    mass_bound_integrable := fun t _ ↦ him t
    momentum_mem_nhds := fun t ht ↦ hp t ht
    momentum_dominated := fun t ht ↦ Eventually.of_forall (fun x r hr ↦ hbp t ht r hr x)
    momentum_bound_integrable := fun t _ ↦ hip t }

/-- The energy density vanishes as a spacetime germ wherever the field does,
provided the potential vanishes at zero. -/
theorem semilinearWaveEnergyDensity_eventuallyEq_zero {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {p : ℝ^(n + 1)} (hV : V 0 = 0) (hu : u =ᶠ[𝓝 p] fun _ ↦ 0) :
    semilinearWaveEnergyDensity V u =ᶠ[𝓝 p] fun _ ↦ 0 := by
  have hd := hu.fderiv (𝕜 := ℝ)
  filter_upwards [hu, hd] with q hq hdq
  simp [semilinearWaveEnergyDensity, classicalWaveEnergyDensity,
    classicalWaveSpatialGradient, EuclideanSpace.real_norm_sq_eq, PDE.partialDeriv, hdq, hq, hV]

/-- All energy domination and flux-support data follow from C² regularity
and a forward support cone. -/
def dominatedEnergyDataOfConeSupport
    {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {a R : ℝ}
    (hV : ContDiff ℝ 1 V) (hVzero : V 0 = 0) (hu : ContDiff ℝ 2 u)
    (hs : ∀ r, a < r → ∀ x, R + r < ‖x‖ → u (timeSpaceCons r x) = 0) :
    DominatedEnergyData V u (Ioi a) := by
  have henergy := contDiff_semilinearWaveEnergyDensity hV hu
  have hezero (r : ℝ) (hr : a < r) (x : ℝ^n) (hx : R + r < ‖x‖) :=
    semilinearWaveEnergyDensity_eventuallyEq_zero hVzero
      (eventuallyEq_zero_of_cone_support hs hr hx)
  choose s b hm hi hb using exists_integrable_majorants_of_cone_support (a := a) (R := R)
    (PDE.contDiff_partialDeriv_of_succ (m := 0) (i := 0) henergy).continuous
    (fun r hr x hx ↦ by rw [PDE.partialDeriv_congr_nhds 0 (hezero r hr x hx)]; simp)
  exact {
    neighborhood := s
    bound := b
    energy_integrable := fun t ht ↦
      (contDiff_semilinearWaveSpatialEnergyDensity hV (fun _ ↦ hu.contDiffAt)).continuous
        |>.integrable_of_hasCompactSupport (HasCompactSupport.intro
          (isCompact_closedBall (0 : ℝ^n) (R + t)) (fun x hx ↦
            (hezero t ht x (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le]
              using hx)).eq_of_nhds))
    mem_nhds := fun t ht ↦ hm t ht
    dominated := fun t ht ↦ Eventually.of_forall (fun x r hr ↦ hb t ht r hr x)
    bound_integrable := fun t _ ↦ hi t
    flux_compact_support := fun t ht i ↦ HasCompactSupport.intro
      (isCompact_closedBall (0 : ℝ^n) (R + t)) (fun x hx ↦ by
        have he := eventuallyEq_zero_of_cone_support hs ht
          (show R + t < ‖x‖ by
            simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx)
        simp [semilinearWaveSpatialEnergyFlux, classicalWaveEnergyFlux,
          PDE.partialDeriv_congr_nhds 0 he]) }

end WaveEquation.NegativeEnergy
