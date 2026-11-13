/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.LerayHopf.EnergySpace

/-!
# Leray-Hopf solutions of Navier-Stokes

`LerayHopfSolution` is the energy-class interface on the slab `[0, T]` without a pressure. It
extends `WeakSolution`, so the momentum equation against solenoidal tests and incompressibility
are inherited, and it adds the `L^∞ L²` and `L² L²` Bochner bounds, continuity of
`velocityWeakL2Slice` into Mathlib's weak topology on `L²(ℝ^n; ℝ^n)`, the initial trace as an
equality of `L²` classes, and the field `energy_inequality`.
`PressureRepresentativeLerayHopfSolution` keeps a pressure and the momentum equation against
general vector tests, and `toLerayHopfSolution` forgets it.

The velocity has `L²` slices on `[0,T]`; the weak gradient and its spatial derivative identity
are required only on `(0,T]`. Thus the initial trace does not impose an `H¹` condition on the
prescribed `L²` datum. The gradient's Bochner representative is set to zero at `t = 0`, which does
not change its time integrals. Gradient slices are required at every positive time, rather than
almost every time. The energy inequality is measured from the initial datum, for every
`t ∈ [0,T]`.

## Main declarations

* `LerayHopfSolution`: the pressure-free energy-class interface, extending `WeakSolution`.
* `PressureRepresentativeLerayHopfSolution`: the pressure-retaining refinement, and
  `PressureRepresentativeLerayHopfSolution.toLerayHopfSolution` forgetting the pressure.
* `forceWork`, `ForceWorkTimeIntegrableOn`: the work of the external force entering the energy
  inequality.
* `LerayHopfSolution.energy_inequality_L2`: the energy inequality written with the `L²` classes,
  `½ ‖u(t)‖² + ν ∫₀ᵗ (weak-gradient dissipation) ≤ ½ ‖u₀‖² + (force work up to t)`.

## References

* J. Leray, "Sur le mouvement d'un liquide visqueux emplissant l'espace", *Acta Math.* 63 (1934),
  193-248.
  <https://doi.org/10.1007/BF02547354>
* E. Hopf, "Über die Anfangswertaufgabe für die hydrodynamischen Grundgleichungen",
  *Math. Nachr.* 4 (1950), 213-231.
  <https://doi.org/10.1002/mana.3210040121>
* R. Temam, *Navier–Stokes Equations: Theory and Numerical Analysis*, AMS Chelsea Publishing, 2001,
  Chapter III (the evolution Navier–Stokes equation).
  <https://doi.org/10.1090/chel/343>
-/

@[expose] public section

namespace NavierStokes

open EuclideanSpace MeasureTheory Order

set_option linter.missingDocs true

/-- Work done by the external force against a velocity representative up to time `t`. -/
noncomputable def forceWork {n : ℕ} (nse : Problem n) (u : ℝ^(n + 1) → ℝ^n)
    (t : ℝ) : ℝ :=
  ∫ s in Set.Icc 0 t, ∫ x : ℝ^n, forcePowerDensity nse u s x

/-- Time integrability of the spatial force-power integral on `[0,T]`.

For a weak solution, spatial integrability of the pointwise force-power density is a
consequence of the stored `L²` force and velocity slices. -/
def ForceWorkTimeIntegrableOn {n : ℕ} (nse : Problem n)
    (u : ℝ^(n + 1) → ℝ^n) (T : ℝ) : Prop :=
  IntegrableOn
    (fun s ↦ ∫ x : ℝ^n, forcePowerDensity nse u s x)
    (Set.Icc 0 T)

/-- Force-work time integrability restricts to every physical initial subinterval. -/
theorem ForceWorkTimeIntegrableOn.integrableOn_Icc {n : ℕ}
    {nse : Problem n} {u : ℝ^(n + 1) → ℝ^n} {T t : ℝ}
    (h : ForceWorkTimeIntegrableOn nse u T) (ht : t ∈ Set.Icc 0 T) :
    IntegrableOn
      (fun s ↦ ∫ x : ℝ^n, forcePowerDensity nse u s x)
      (Set.Icc 0 t) :=
  h.mono_set fun _ hs ↦ ⟨hs.1, hs.2.trans ht.2⟩

/-- Any force does no work against the zero velocity field. -/
theorem forceWork_zeroVelocity {n : ℕ} (nse : Problem n) (t : ℝ) :
    forceWork nse (fun _ : ℝ^(n + 1) ↦ (0 : ℝ^n)) t = 0 := by
  simp [forceWork, forcePowerDensity,
    IncompressibleFlow.velocitySlice]

/-- Pressure-free Leray-Hopf solution on `[0,T]`.

The weak momentum equation and incompressibility come from `WeakSolution`. The additional fields
give velocity and gradient Bochner bounds, continuity into the weak topology of `L²`, the
initial trace as equality of `L²` classes, force-work integrability, and the all-time energy
inequality measured from the prescribed datum.

The initial datum is required only in `L²`. Spatial-gradient membership and its weak derivative
identity are imposed on `(0,T]`, while the velocity and its initial trace are defined on `[0,T]`.
These representative requirements at every positive time are stronger than an almost-everywhere
formulation. -/
structure LerayHopfSolution {n : ℕ} (nse : Problem n) extends WeakSolution nse where
  /-- The velocity belongs to `L∞(0,T; L²(ℝ^n))` in the Bochner sense. -/
  velocity_memLp_top : MemLp toWeakSolution.velocityL2Slice (⊤ : ENNReal)
    ((MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ)))

  /-- The weak spatial gradient belongs to `L²(0,T; L²(ℝ^n))`. -/
  gradient_memLp_two : MemLp toWeakSolution.gradientL2Slice 2
    ((MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ)))

  /-- The selected `L²` velocity representative is continuous in Mathlib's weak topology. -/
  velocityWeakL2Slice_continuousOn :
    ContinuousOn toWeakSolution.velocityWeakL2Slice (Set.Icc 0 (T : ℝ))

  /-- The weakly continuous representative takes the prescribed initial `L²` trace. -/
  velocityL2Slice_zero_eq_initial :
    toWeakSolution.velocityL2Slice 0 = toWeakSolution.initialVelocityL2

  /-- The spatial force-power integral is integrable in time on the full slab. -/
  forceWorkTimeIntegrableOn : ForceWorkTimeIntegrableOn nse u T

  /-- Leray-Hopf energy inequality, measured from the prescribed initial datum. -/
  energy_inequality : ∀ {t : ℝ}, t ∈ Set.Icc 0 (T : ℝ) →
    kineticEnergy u t + nse.kinematicViscosity * ∫ s in Set.Icc 0 t, weakGradientDissipation Du s ≤
      initialKineticEnergy nse + forceWork nse u t

/-- A pressure-retaining representative-level refinement of `LerayHopfSolution`.

This retains the stronger `PressureWeakSolution` data and uses the same weak topology,
initial `L²` trace, Bochner bounds, and energy inequality as the pressure-free core. -/
structure PressureRepresentativeLerayHopfSolution {n : ℕ} (nse : Problem n)
    extends PressureWeakSolution nse where
  /-- The velocity belongs to `L∞(0,T; L²(ℝ^n))` after pressure is forgotten. -/
  velocity_memLp_top : MemLp toPressureWeakSolution.toWeakSolution.velocityL2Slice
    (⊤ : ENNReal) ((MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ)))

  /-- The weak spatial gradient belongs to `L²(0,T; L²(ℝ^n))`. -/
  gradient_memLp_two : MemLp toPressureWeakSolution.toWeakSolution.gradientL2Slice 2
    ((MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ)))

  /-- The selected velocity representative is continuous in the weak `L²` topology. -/
  velocityWeakL2Slice_continuousOn :
    ContinuousOn toPressureWeakSolution.toWeakSolution.velocityWeakL2Slice
      (Set.Icc 0 (T : ℝ))

  /-- The weakly continuous representative takes the prescribed initial `L²` trace. -/
  velocityL2Slice_zero_eq_initial :
    toPressureWeakSolution.toWeakSolution.velocityL2Slice 0 =
      toPressureWeakSolution.toWeakSolution.initialVelocityL2

  /-- The spatial force-power integral is integrable in time on the full slab. -/
  forceWorkTimeIntegrableOn : ForceWorkTimeIntegrableOn nse u T

  /-- Leray-Hopf energy inequality for the pressure-retaining representative. -/
  energy_inequality : ∀ {t : ℝ}, t ∈ Set.Icc 0 (T : ℝ) →
    kineticEnergy u t + nse.kinematicViscosity * ∫ s in Set.Icc 0 t, weakGradientDissipation Du s ≤
      initialKineticEnergy nse + forceWork nse u t

/-- Forgetting pressure produces the pressure-free Leray-Hopf core. -/
def PressureRepresentativeLerayHopfSolution.toLerayHopfSolution
    {n : ℕ} {nse : Problem n} (sol : PressureRepresentativeLerayHopfSolution nse) :
    LerayHopfSolution nse where
  toWeakSolution := sol.toPressureWeakSolution.toWeakSolution
  velocity_memLp_top := sol.velocity_memLp_top
  gradient_memLp_two := sol.gradient_memLp_two
  velocityWeakL2Slice_continuousOn := sol.velocityWeakL2Slice_continuousOn
  velocityL2Slice_zero_eq_initial := sol.velocityL2Slice_zero_eq_initial
  forceWorkTimeIntegrableOn := sol.forceWorkTimeIntegrableOn
  energy_inequality := sol.energy_inequality

/-- The standard Leray-Hopf velocity and gradient energy-space bounds. -/
theorem LerayHopfSolution.velocity_gradient_memLp {n : ℕ} {nse : Problem n}
    (sol : LerayHopfSolution nse) :
    MemLp sol.toWeakSolution.velocityL2Slice (⊤ : ENNReal)
        ((MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 (sol.T : ℝ))) ∧
      MemLp sol.toWeakSolution.gradientL2Slice 2
        ((MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 (sol.T : ℝ))) :=
  ⟨sol.velocity_memLp_top, sol.gradient_memLp_two⟩

/-- The weak-gradient dissipation is integrable in time; this is derived, not stored. -/
theorem LerayHopfSolution.weakGradientDissipation_integrableOn {n : ℕ}
    {nse : Problem n} (sol : LerayHopfSolution nse) :
    IntegrableOn (weakGradientDissipation sol.Du) (Set.Icc 0 (sol.T : ℝ)) :=
  sol.toWeakSolution.weakGradientDissipation_integrableOn_of_gradient_memLp
    sol.gradient_memLp_two

/-- The Leray-Hopf energy inequality written directly in terms of the selected `L²` classes. -/
theorem LerayHopfSolution.energy_inequality_L2 {n : ℕ} {nse : Problem n}
    (sol : LerayHopfSolution nse) {t : ℝ} (ht : t ∈ Set.Icc 0 (sol.T : ℝ)) :
    (1 / 2 : ℝ) * ‖sol.toWeakSolution.velocityL2Slice t‖ ^ 2 +
        nse.kinematicViscosity * ∫ s in Set.Icc 0 t, weakGradientDissipation sol.Du s ≤
      (1 / 2 : ℝ) * ‖sol.toWeakSolution.initialVelocityL2‖ ^ 2 +
        forceWork nse sol.u t := by
  simpa only [sol.toWeakSolution.kineticEnergy_eq_velocityL2Slice_norm_sq ht,
    sol.toWeakSolution.initialKineticEnergy_eq_initialVelocityL2_norm_sq] using
    sol.energy_inequality ht

/-- The pressure-retaining refinement has time-integrable weak-gradient dissipation. -/
theorem PressureRepresentativeLerayHopfSolution.weakGradientDissipation_integrableOn
    {n : ℕ} {nse : Problem n} (sol : PressureRepresentativeLerayHopfSolution nse) :
    IntegrableOn (weakGradientDissipation sol.Du) (Set.Icc 0 (sol.T : ℝ)) :=
  sol.toLerayHopfSolution.weakGradientDissipation_integrableOn

end NavierStokes
