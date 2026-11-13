/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.GlobalEnergy.ForwardConservation

/-!
# Global energy conservation for semilinear wave equations

We prove constancy of semilinear wave energy from the zero-derivative
theorem in `GlobalEnergy.Differentiation`. Local conservation is first proved on
the unordered interval between two times and then on arbitrary order-connected
time sets, including closed and half-open lifespan intervals.

Every theorem keeps the analytic hypotheses needed to differentiate under
the spatial integral and to eliminate the integrated spatial flux.
The interval results only require regularity on a common spatially uniform
time neighborhood of each included time, not at an excluded lifespan endpoint.

The theorem `semilinearWaveSpatialEnergy_conserved` is the conservation of energy of Evans,
§12.1.1, Theorem 1. Evans assumes a smooth solution with compact support in space at each time;
we assume instead the integrability, domination and flux-support conditions that the
differentiation under the integral and the integration by parts use.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.1, Theorem 1 and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace WaveEquation

variable {n : ℕ}

/-- Semilinear wave energy agrees at two times when the equation and the
analytic hypotheses for differentiating the energy hold on the unordered
interval between them.

Unlike `semilinearWaveSpatialEnergy_conserved`, this local form does not
require the wave equation outside the time interval relevant to the two
endpoints. -/
theorem semilinearWaveSpatialEnergy_eq_of_wave_on_uIcc
    {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {t₀ t₁ : ℝ}
    {s : ℝ → Set ℝ} {bound : ℝ → ℝ^n → ℝ}
    (hV : ContDiff ℝ 1 V)
    (hu : ∀ t ∈ uIcc t₀ t₁, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n,
      ContDiffAt ℝ 2 u (PDE.Common.timeSpaceCons (n := n) r x))
    (hwave :
      ∀ t ∈ uIcc t₀ t₁, ∀ x : ℝ^n,
        semilinearWaveOperator (n := n) V u
          (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (henergyIntegrable :
      ∀ t ∈ uIcc t₀ t₁,
        Integrable
          (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (hs :
      ∀ t ∈ uIcc t₀ t₁, s t ∈ 𝓝 t)
    (hdominated :
      ∀ t ∈ uIcc t₀ t₁,
        ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s t,
          ‖semilinearWaveSpatialEnergyTimeDerivative
            (n := n) V u r x‖ ≤ bound t x)
    (hboundIntegrable :
      ∀ t ∈ uIcc t₀ t₁, Integrable (bound t))
    (hfluxCompact :
      ∀ t ∈ uIcc t₀ t₁, ∀ i,
        HasCompactSupport
          (semilinearWaveSpatialEnergyFlux (n := n) u i t)) :
    semilinearWaveSpatialEnergy (n := n) V u t₀ =
      semilinearWaveSpatialEnergy (n := n) V u t₁ := by
  let energy : ℝ → ℝ := semilinearWaveSpatialEnergy (n := n) V u
  have hderivative (t : ℝ) (ht : t ∈ uIcc t₀ t₁) :
      HasDerivAt energy 0 t := by
    exact hasDerivAt_semilinearWaveSpatialEnergy_eq_zero
      (n := n) hV (hu t ht) (hs t ht) (henergyIntegrable t ht)
      (hdominated t ht) (hboundIntegrable t ht) (hwave t ht) (hfluxCompact t ht)
  have hnorm :
      ‖energy t₁ - energy t₀‖ ≤ 0 := by
    have hmean := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := energy) (f' := fun _ ↦ 0) (C := 0) (fun t ht ↦ (hderivative t ht).hasDerivWithinAt)
        (fun _ _ ↦ by simp) (convex_uIcc t₀ t₁) left_mem_uIcc right_mem_uIcc
    simpa using hmean
  have hnormZero : ‖energy t₁ - energy t₀‖ = 0 := le_antisymm hnorm (norm_nonneg _)
  have henergyEq : energy t₁ = energy t₀ := sub_eq_zero.mp (norm_eq_zero.mp hnormZero)
  exact henergyEq.symm

/-- Semilinear wave energy agrees at any two times in an order-connected set
on which the equation and all analytic differentiation hypotheses hold.

Order-connectedness is the exact geometric condition needed here: it ensures
that the unordered interval joining the two selected times remains inside the
available lifespan. In particular, this one result covers closed and half-open
forward and backward time slabs. -/
theorem semilinearWaveSpatialEnergy_eq_of_wave_on_ordConnected {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    {times : Set ℝ} {t₀ t₁ : ℝ} {s : ℝ → Set ℝ} {bound : ℝ → ℝ^n → ℝ} (htimes : times.OrdConnected)
    (ht₀ : t₀ ∈ times) (ht₁ : t₁ ∈ times) (hV : ContDiff ℝ 1 V)
    (hu : ∀ t ∈ times, ∀ᶠ r in 𝓝 t, ∀ x : ℝ^n, ContDiffAt ℝ 2 u
      (PDE.Common.timeSpaceCons (n := n) r x))
    (hwave : ∀ t ∈ times, ∀ x : ℝ^n, semilinearWaveOperator (n := n) V u
      (PDE.Common.timeSpaceCons (n := n) t x) = 0)
    (henergyIntegrable : ∀ t ∈ times, Integrable (semilinearWaveSpatialEnergyDensity (n := n) V
      u t))
    (hs : ∀ t ∈ times, s t ∈ 𝓝 t)
    (hdominated : ∀ t ∈ times, ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s t,
      ‖semilinearWaveSpatialEnergyTimeDerivative (n := n) V u r x‖ ≤ bound t x)
    (hboundIntegrable : ∀ t ∈ times, Integrable (bound t))
    (hfluxCompact : ∀ t ∈ times, ∀ i, HasCompactSupport (semilinearWaveSpatialEnergyFlux (n := n) u
      i t)) :
    semilinearWaveSpatialEnergy (n := n) V u t₀ = semilinearWaveSpatialEnergy (n := n) V u t₁ := by
  have hsubset : uIcc t₀ t₁ ⊆ times := htimes.uIcc_subset ht₀ ht₁
  apply semilinearWaveSpatialEnergy_eq_of_wave_on_uIcc hV (fun t ht ↦ hu t (hsubset ht))
  · exact fun t ht ↦ hwave t (hsubset ht)
  · exact fun t ht ↦ henergyIntegrable t (hsubset ht)
  · exact fun t ht ↦ hs t (hsubset ht)
  · exact fun t ht ↦ hdominated t (hsubset ht)
  · exact fun t ht ↦ hboundIntegrable t (hsubset ht)
  · exact fun t ht ↦ hfluxCompact t (hsubset ht)

/-- Global semilinear wave energy is conserved between any two times.

The hypotheses expose every analytic input: classical regularity and the
pointwise equation, integrability of each energy slice, a local integrable
dominator for differentiation under the integral, and compact support of each
fixed-time spatial energy-flux component. -/
theorem semilinearWaveSpatialEnergy_conserved {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ} {s : ℝ → Set ℝ}
    {bound : ℝ → ℝ^n → ℝ} (hV : ContDiff ℝ 1 V) (hu : ContDiff ℝ 2 u)
    (hwave : ∀ p, semilinearWaveOperator (n := n) V u p = 0)
    (henergyIntegrable : ∀ t, Integrable (semilinearWaveSpatialEnergyDensity (n := n) V u t))
    (hs : ∀ t, s t ∈ 𝓝 t)
    (hdominated : ∀ t, ∀ᵐ x ∂(volume : Measure (ℝ^n)), ∀ r ∈ s t,
      ‖semilinearWaveSpatialEnergyTimeDerivative (n := n) V u r x‖ ≤ bound t x)
    (hboundIntegrable : ∀ t, Integrable (bound t))
    (hfluxCompact : ∀ t i, HasCompactSupport (semilinearWaveSpatialEnergyFlux (n := n) u i t))
    (t₀ t₁ : ℝ) :
    semilinearWaveSpatialEnergy (n := n) V u t₀ = semilinearWaveSpatialEnergy (n := n) V u t₁ := by
  have hderivative : ∀ t, HasDerivAt
          (semilinearWaveSpatialEnergy (n := n) V u) 0 t := by
    intro t
    exact hasDerivAt_semilinearWaveSpatialEnergy_eq_zero
      (n := n) hV (Filter.Eventually.of_forall fun _ _ ↦ hu.contDiffAt) (hs t) (henergyIntegrable t)
      (hdominated t) (hboundIntegrable t) (fun x ↦ hwave (PDE.Common.timeSpaceCons (n := n) t x))
      (hfluxCompact t)
  exact is_const_of_deriv_eq_zero (fun t ↦ (hderivative t).differentiableAt)
    (fun t ↦ (hderivative t).deriv) t₀ t₁

end WaveEquation
