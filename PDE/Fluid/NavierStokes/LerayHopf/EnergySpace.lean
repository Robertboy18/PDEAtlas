/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.WeakSolutions

/-!
# Leray-Hopf energy-space facts

The representative-level weak solutions sit inside Mathlib's `L²` Hilbert space with its weak
topology (`WeakSolution.velocityWeakL2Slice`). The spatial weak-gradient integral is the
squared norm of the corresponding `L²` class, and kinetic energy is one half of the squared
`L²` norm of the velocity.
-/

@[expose] public section

namespace NavierStokes

open EuclideanSpace MeasureTheory Order

set_option linter.missingDocs true

/-- The velocity slice regarded as an element of `L²` with its weak topology. -/
noncomputable def WeakSolution.velocityWeakL2Slice {n : ℕ} {nse : Problem n}
    (sol : WeakSolution nse) (t : ℝ) :
    WeakSpace ℝ (MeasureTheory.Lp (ℝ^n) 2
      (MeasureTheory.volume : Measure (ℝ^n))) :=
  toWeakSpace ℝ _ (sol.velocityL2Slice t)

/-- Kinetic energy is one half of the squared norm of the corresponding `L²` velocity class. -/
theorem WeakSolution.kineticEnergy_eq_velocityL2Slice_norm_sq
    {n : ℕ} {nse : Problem n} (sol : WeakSolution nse)
    {t : ℝ} (ht : t ∈ Set.Icc 0 (sol.T : ℝ)) :
    kineticEnergy sol.u t = (1 / 2 : ℝ) * ‖sol.velocityL2Slice t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [sol.velocityL2Slice_apply_ae ht] with x hx
  rw [hx]
  simp only [kineticEnergyDensity,
    IncompressibleFlow.specificKineticEnergy,
    IncompressibleFlow.velocitySlice, real_inner_self_eq_norm_sq]

/-- Initial kinetic energy is one half of the squared norm of the prescribed initial `L²` class. -/
theorem WeakSolution.initialKineticEnergy_eq_initialVelocityL2_norm_sq
    {n : ℕ} {nse : Problem n} (sol : WeakSolution nse) :
    initialKineticEnergy nse = (1 / 2 : ℝ) * ‖sol.initialVelocityL2‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [sol.initialVelocityL2_apply_ae] with x hx
  rw [hx]
  simp only [initialKineticEnergyDensity,
    IncompressibleFlow.specificKineticEnergy, real_inner_self_eq_norm_sq]

/-- Spatial weak-gradient dissipation is the squared norm of the corresponding `L²` class. -/
theorem WeakSolution.weakGradientDissipation_eq_gradientL2Slice_norm_sq
    {n : ℕ} {nse : Problem n} (sol : WeakSolution nse)
    {t : ℝ} (ht : t ∈ Set.Ioc 0 (sol.T : ℝ)) :
    weakGradientDissipation sol.Du t = ‖sol.gradientL2Slice t‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sol.gradientL2Slice_apply_ae ht] with x hx
  rw [hx]
  simp only [weakGradientDissipationDensity, real_inner_self_eq_norm_sq]

/-- Bochner `L²_t(L²_x)` control of the weak gradient makes the physical dissipation
integrable in time on the closed slab. -/
theorem WeakSolution.weakGradientDissipation_integrableOn_of_gradient_memLp
    {n : ℕ} {nse : Problem n} (sol : WeakSolution nse)
    (hgradient : MemLp sol.gradientL2Slice 2
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 (sol.T : ℝ)))) :
    IntegrableOn (weakGradientDissipation sol.Du) (Set.Icc 0 (sol.T : ℝ)) := by
  have hnorm : Integrable (fun t ↦ ‖sol.gradientL2Slice t‖ ^ 2)
      ((MeasureTheory.volume : Measure ℝ).restrict (Set.Icc 0 (sol.T : ℝ))) :=
    hgradient.integrable_norm_pow (by norm_num)
  have hmem : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 (sol.T : ℝ))),
      t ∈ Set.Ioc 0 (sol.T : ℝ) := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioc
  exact hnorm.congr <| hmem.mono fun t ht ↦
    (sol.weakGradientDissipation_eq_gradientL2Slice_norm_sq ht).symm

end NavierStokes
