/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.Differentiation
public import PDE.Hyperbolic.NonlinearWave.NegativeEnergy.QuadraticMass.Basic

/-!
# Dominated spatial integrals for semilinear waves

`DominatedVirialData` supplies compact support of the field and the local domination
needed to differentiate its quadratic mass and momentum. `DominatedEnergyData`
supplies integrability of the energy, domination of its time derivative, and compact
support of the flux. The two structures are independent: an argument that assumes energy
conservation need not also prove the hypotheses for differentiating that energy.

Both are indexed by a time set. At each included time, domination holds on
a time neighborhood, with one spatial exceptional null set for that whole
neighborhood. Restriction to a smaller time set retains the same neighborhoods and
integrable bounds. In particular, restriction adds no condition at an excluded endpoint.

Spacetime regularity and the wave equation are separate hypotheses. This lets the same data serve
local slab arguments and the global regularity assumptions used by stability and continuation
results.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- Compact support and local domination for the first two derivatives of
`I(t) = ½ ∫ u(t, x)² dx`. No energy-conservation assumption is part of this data. -/
structure DominatedVirialData (u : ℝ^(n + 1) → ℝ) (times : Set ℝ) where
  /-- A time neighborhood for differentiating the quadratic mass. -/
  massNeighborhood : ℝ → Set ℝ
  /-- A spatial majorant for the mass derivative near each included time. -/
  massBound : ℝ → ℝ^n → ℝ
  /-- A time neighborhood for differentiating the quadratic momentum. -/
  momentumNeighborhood : ℝ → Set ℝ
  /-- A spatial majorant for the momentum derivative near each included time. -/
  momentumBound : ℝ → ℝ^n → ℝ
  /-- The field has compact support on each included spatial slice. -/
  compact_support : ∀ t ∈ times,
    HasCompactSupport (fun x : ℝ^n ↦ u (PDE.Common.timeSpaceCons (n := n) t x))
  /-- Mass domination holds on a neighborhood of the differentiation time. -/
  mass_mem_nhds : ∀ t ∈ times, massNeighborhood t ∈ 𝓝 t
  /-- The exceptional spatial null set is independent of the nearby time. -/
  mass_dominated : ∀ t ∈ times, ∀ᵐ x ∂(volume : Measure (ℝ^n)),
    ∀ r ∈ massNeighborhood t,
      ‖waveSpatialQuadraticMomentumDensity (n := n) u r x‖ ≤ massBound t x
  /-- The mass derivative majorant is integrable on space. -/
  mass_bound_integrable : ∀ t ∈ times, Integrable (massBound t)
  /-- Momentum domination holds on a neighborhood of the differentiation time. -/
  momentum_mem_nhds : ∀ t ∈ times, momentumNeighborhood t ∈ 𝓝 t
  /-- Momentum differentiation uses a common spatial exceptional null set. -/
  momentum_dominated : ∀ t ∈ times, ∀ᵐ x ∂(volume : Measure (ℝ^n)),
    ∀ r ∈ momentumNeighborhood t,
      ‖waveSpatialQuadraticMomentumDerivativeDensity (n := n) u r x‖ ≤ momentumBound t x
  /-- The momentum derivative majorant is integrable on space. -/
  momentum_bound_integrable : ∀ t ∈ times, Integrable (momentumBound t)

/-- Restrict virial data without shrinking its time neighborhoods or changing its bounds. -/
def DominatedVirialData.mono {u : ℝ^(n + 1) → ℝ} {times smaller : Set ℝ}
    (D : DominatedVirialData u times) (h : smaller ⊆ times) :
    DominatedVirialData u smaller where
  massNeighborhood := D.massNeighborhood
  massBound := D.massBound
  momentumNeighborhood := D.momentumNeighborhood
  momentumBound := D.momentumBound
  compact_support t ht := D.compact_support t (h ht)
  mass_mem_nhds t ht := D.mass_mem_nhds t (h ht)
  mass_dominated t ht := D.mass_dominated t (h ht)
  mass_bound_integrable t ht := D.mass_bound_integrable t (h ht)
  momentum_mem_nhds t ht := D.momentum_mem_nhds t (h ht)
  momentum_dominated t ht := D.momentum_dominated t (h ht)
  momentum_bound_integrable t ht := D.momentum_bound_integrable t (h ht)

/-- Analytic data for differentiating spatial wave energy and integrating its flux.
The equation, regularity, and any sign or coercivity condition on `V` are separate hypotheses. -/
structure DominatedEnergyData (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ) (times : Set ℝ) where
  /-- A time neighborhood for differentiating the energy at each included time. -/
  neighborhood : ℝ → Set ℝ
  /-- A spatial majorant for the energy time derivative. -/
  bound : ℝ → ℝ^n → ℝ
  /-- The energy density is integrable at every included time. -/
  energy_integrable : ∀ t ∈ times,
    Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t)
  /-- Each domination set is a neighborhood of its differentiation time. -/
  mem_nhds : ∀ t ∈ times, neighborhood t ∈ 𝓝 t
  /-- One spatial exceptional null set suffices throughout the time neighborhood. -/
  dominated : ∀ t ∈ times, ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ neighborhood t,
    ‖semilinearWaveSpatialEnergyTimeDerivative (n := n) V u r x‖ ≤ bound t x
  /-- The energy derivative majorant is integrable on space. -/
  bound_integrable : ∀ t ∈ times, Integrable (bound t)
  /-- Compact support eliminates each spatial flux integral. -/
  flux_compact_support : ∀ t ∈ times, ∀ i,
    HasCompactSupport (semilinearWaveSpatialEnergyFlux (n := n) u i t)

/-- Restrict energy data while retaining its neighborhood and majorant witnesses. -/
def DominatedEnergyData.mono {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {times smaller : Set ℝ} (D : DominatedEnergyData V u times) (h : smaller ⊆ times) :
    DominatedEnergyData V u smaller where
  neighborhood := D.neighborhood
  bound := D.bound
  energy_integrable t ht := D.energy_integrable t (h ht)
  mem_nhds t ht := D.mem_nhds t (h ht)
  dominated t ht := D.dominated t (h ht)
  bound_integrable t ht := D.bound_integrable t (h ht)
  flux_compact_support t ht := D.flux_compact_support t (h ht)

end WaveEquation
