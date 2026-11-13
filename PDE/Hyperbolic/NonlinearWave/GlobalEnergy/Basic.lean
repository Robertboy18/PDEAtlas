/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import PDE.Hyperbolic.NonlinearWave.EnergyIdentity
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import PDE.FDeriv.SpaceTime

/-!
# Fixed-time semilinear wave energy

We define the semilinear wave-energy density on a fixed-time spatial
slice, its kinetic, spatial-gradient, and potential components, and the total
spatial energy.

The decomposition of the total energy assumes integrability of every
component. This is essential because the Bochner integral is totalized outside
the integrable regime.

With `V` in place of Evans's primitive `F`, the total spatial energy is the energy `E(t)` of
Evans, §12.1.1.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.1.1, the energy `E(t)`.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory

namespace WaveEquation

variable {n : ℕ}

/-- The semilinear wave-energy density restricted to a fixed-time spatial
slice. -/
def semilinearWaveSpatialEnergyDensity
    (V : ℝ → ℝ)
    (u : ℝ^(n + 1) → ℝ)
    (t : ℝ) (x : ℝ^n) : ℝ :=
  semilinearWaveEnergyDensity (n := n) V u
    (PDE.Common.timeSpaceCons (n := n) t x)

/-- The normalized kinetic-energy density `uₜ² / 2` on a fixed-time
spatial slice. -/
def semilinearWaveSpatialKineticEnergyDensity
    (u : ℝ^(n + 1) → ℝ)
    (t : ℝ) (x : ℝ^n) : ℝ :=
  (1 / 2 : ℝ) *
    ((∂[0] u)
      (PDE.Common.timeSpaceCons (n := n) t x)) ^ 2

/-- The normalized spatial-gradient energy density `‖Dₓu‖² / 2` on a
fixed-time spatial slice. -/
def semilinearWaveSpatialGradientEnergyDensity
    (u : ℝ^(n + 1) → ℝ)
    (t : ℝ) (x : ℝ^n) : ℝ :=
  (1 / 2 : ℝ) *
    ‖classicalWaveSpatialGradient (n := n) u
      (PDE.Common.timeSpaceCons (n := n) t x)‖ ^ 2

/-- The potential-energy density `V(u)` on a fixed-time spatial slice. -/
def semilinearWaveSpatialPotentialEnergyDensity
    (V : ℝ → ℝ)
    (u : ℝ^(n + 1) → ℝ)
    (t : ℝ) (x : ℝ^n) : ℝ :=
  V (u (PDE.Common.timeSpaceCons (n := n) t x))

/-- The fixed-time semilinear energy density is the sum of its kinetic,
spatial-gradient, and potential components. -/
theorem semilinearWaveSpatialEnergyDensity_eq_components (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ) (t : ℝ)
    (x : ℝ^n) :
    semilinearWaveSpatialEnergyDensity (n := n) V u t x =
      semilinearWaveSpatialKineticEnergyDensity (n := n) u t x +
        (semilinearWaveSpatialGradientEnergyDensity (n := n) u t x +
          semilinearWaveSpatialPotentialEnergyDensity (n := n) V u t x) := by
  simp only [semilinearWaveSpatialEnergyDensity, semilinearWaveSpatialKineticEnergyDensity,
    semilinearWaveSpatialGradientEnergyDensity, semilinearWaveSpatialPotentialEnergyDensity,
    semilinearWaveEnergyDensity, classicalWaveEnergyDensity]
  ring

/-- The total semilinear wave energy on a fixed-time spatial slice. -/
def semilinearWaveSpatialEnergy
    (V : ℝ → ℝ)
    (u : ℝ^(n + 1) → ℝ)
    (t : ℝ) : ℝ :=
  ∫ x, semilinearWaveSpatialEnergyDensity (n := n) V u t x

/-- Decompose total semilinear wave energy into the integrals of its kinetic,
spatial-gradient, and potential components.

The componentwise integrability hypotheses are necessary because the Bochner
integral is totalized outside the integrable regime. -/
theorem semilinearWaveSpatialEnergy_eq_integral_components (V : ℝ → ℝ) (u : ℝ^(n + 1) → ℝ) (t : ℝ)
    (hkinetic : Integrable (semilinearWaveSpatialKineticEnergyDensity (n := n) u t))
    (hgradient : Integrable (semilinearWaveSpatialGradientEnergyDensity (n := n) u t))
    (hpotential : Integrable (semilinearWaveSpatialPotentialEnergyDensity (n := n) V u t)) :
    semilinearWaveSpatialEnergy (n := n) V u t =
      (∫ x : ℝ^n,
        semilinearWaveSpatialKineticEnergyDensity (n := n) u t x) +
        ((∫ x : ℝ^n,
          semilinearWaveSpatialGradientEnergyDensity (n := n) u t x) +
          ∫ x : ℝ^n,
            semilinearWaveSpatialPotentialEnergyDensity
              (n := n) V u t x) := by
  unfold semilinearWaveSpatialEnergy
  calc
    (∫ x : ℝ^n, semilinearWaveSpatialEnergyDensity (n := n) V u t x) = ∫ x : ℝ^n,
          semilinearWaveSpatialKineticEnergyDensity (n := n) u t x +
            (semilinearWaveSpatialGradientEnergyDensity (n := n) u t x +
              semilinearWaveSpatialPotentialEnergyDensity
                (n := n) V u t x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦
        semilinearWaveSpatialEnergyDensity_eq_components V u t x
    _ = (∫ x : ℝ^n, semilinearWaveSpatialKineticEnergyDensity (n := n) u t x) + ∫ x : ℝ^n,
            (semilinearWaveSpatialGradientEnergyDensity (n := n) u t x +
              semilinearWaveSpatialPotentialEnergyDensity (n := n) V u t x) :=
      integral_add hkinetic (hgradient.add hpotential)
    _ = (∫ x : ℝ^n, semilinearWaveSpatialKineticEnergyDensity (n := n) u t x) + ((∫ x : ℝ^n,
            semilinearWaveSpatialGradientEnergyDensity (n := n) u t x) + ∫ x : ℝ^n,
              semilinearWaveSpatialPotentialEnergyDensity
                (n := n) V u t x) := by
      rw [integral_add hgradient hpotential]

/-- An equation `□u + f(u) = 0` that holds at all positive times extends by continuity to time
zero when `u` is `C²` and `f` is continuous. -/
theorem waveOperator_add_eq_zero_of_nonneg {f : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hf : Continuous f) (hu : ContDiff ℝ 2 u)
    (hwave : ∀ t, 0 < t → ∀ x,
      waveOperator u (PDE.Common.timeSpaceCons t x) + f (u (PDE.Common.timeSpaceCons t x)) = 0)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ^n) :
    waveOperator u (PDE.Common.timeSpaceCons t x) + f (u (PDE.Common.timeSpaceCons t x)) = 0 := by
  have hc : Continuous (fun r : ℝ ↦
      waveOperator u (PDE.Common.timeSpaceCons r x) + f (u (PDE.Common.timeSpaceCons r x))) :=
    ((continuous_waveOperator_of_contDiff_two hu).add (hf.comp hu.continuous)).comp
      ((PDE.Common.contDiff_timeSpaceCons_uncurry n (m := 1)).continuous.comp
        (continuous_id.prodMk continuous_const))
  have he : Set.EqOn (fun r : ℝ ↦
      waveOperator u (PDE.Common.timeSpaceCons r x) + f (u (PDE.Common.timeSpaceCons r x)))
      (fun _ ↦ 0) (Set.Ioi 0) := fun r hr ↦ hwave r hr x
  have hcl := he.closure hc continuous_const
  rw [closure_Ioi] at hcl
  exact hcl ht

/-- A semilinear wave equation with continuous reaction `deriv V` that holds at all positive
times also holds at time zero. -/
theorem semilinearWaveOperator_eq_zero_of_nonneg {V : ℝ → ℝ} {u : ℝ^(n + 1) → ℝ}
    (hV : Continuous (deriv V)) (hu : ContDiff ℝ 2 u)
    (hwave : ∀ t, 0 < t → ∀ x, semilinearWaveOperator V u (PDE.Common.timeSpaceCons t x) = 0)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ^n) :
    semilinearWaveOperator V u (PDE.Common.timeSpaceCons t x) = 0 :=
  waveOperator_add_eq_zero_of_nonneg hV hu hwave ht x

end WaveEquation
