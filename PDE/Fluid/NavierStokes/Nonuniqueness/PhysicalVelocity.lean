/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.MeasureTheory.ContinuousRepresentative.Canonical
public import PDE.Fluid.Incompressible.SpatialFields
public import PDE.Fluid.NavierStokes.Nonuniqueness.AncientFamily

/-!
# The physical velocity of the ancient family

For an unstable profile `Ũ`, a cutoff radius `R` and a parameter `s`, the velocity of Hou, Wang
and Yang (Section 2.2, (2.7)) is `u = ũ + u_cut + u_cor`, in similarity variables
`t = e^τ`, `x = e^{τ/2} ξ`:

`u(t, x) = t^{-1/2} (Ũ + U_cut + U_cor)(log t, x / √t)`,

with `U_cut` the cutoff field and `U_cor` the decoded ancient correction
`ancientCorrection D R s`. `correctionField D R s τ` is the continuous representative of the
correction at `τ` (a continuous function almost everywhere equal to its components when one
exists, and the components otherwise), and `physicalVelocity D R s` is the velocity at positive
times, with the localized datum `u_loc` at nonpositive times. Its cutoff part is the heat flow
`-e^{tΔ} w` of the localization remainder, and at time one, where similarity variables are
physical, the velocities of distinct parameters differ on a set of positive measure.

## Main results

* `correctionField`, `correctionField_ae_eq`.
* `physicalVelocity`, `physicalVelocity_timeSpaceCons`,
  `physicalVelocity_timeSpaceCons_of_nonpos`, `velocitySlice_physicalVelocity_zero`.
* `inv_sqrt_smul_cutoffField`, `physicalVelocity_timeSpaceCons_eq`: the cutoff part is
  `-e^{tΔ} w`.
* `velocitySlice_physicalVelocity_one`, `eq_of_velocitySlice_physicalVelocity_one_ae_eq`.

## References

* T. Hou, Y. Wang, and C. Yang, "Nonuniqueness of Leray–Hopf solutions to the unforced
  incompressible 3D Navier–Stokes Equation", arXiv:2509.25116v2, Section 2.2, (2.7), p. 11, and the
  construction of the cutoff, p. 12.
  <https://arxiv.org/abs/2509.25116v2>
-/

@[expose] public noncomputable section

open MeasureTheory Set SobolevSpace SobolevSpace.GraphSpace HeatEquation.WholeSpace
open PDE.Analysis.Evolution PDE.Common

namespace NavierStokes.Nonuniqueness

set_option linter.missingDocs true

variable (D : UnstableProfile) (R s : ℝ)

/-- The correction field `U_cor(τ, ξ)` in similarity variables: the continuous representative of
the Euclidean field of base representatives of the decoded ancient correction at `τ`, that is, a
continuous function almost everywhere equal to these components when one exists, and the
components otherwise. -/
def correctionField (τ : ℝ) : ℝ^3 → ℝ^3 :=
  continuousRepresentative volume fun ξ ↦ WithLp.toLp 2 fun j ↦
    baseRepresentative (ancientLift D.dichotomy.η (ancientCorrection D R s) τ j) ξ

/-- The correction field is almost everywhere equal to the base representatives of the decoded
ancient correction. -/
theorem correctionField_ae_eq (τ : ℝ) :
    correctionField D R s τ =ᵐ[volume] fun ξ ↦ WithLp.toLp 2 fun j ↦
      baseRepresentative (ancientLift D.dichotomy.η (ancientCorrection D R s) τ j) ξ :=
  continuousRepresentative_ae_eq _ _

/-- The physical velocity `u(t, x) = t^{-1/2} (Ũ + U_cut + U_cor)(log t, x / √t)` of the
profile, the cutoff field and the ancient correction at positive times `t`, and the localized
datum `u_loc(x)` at nonpositive times. -/
def physicalVelocity (z : ℝ^(3 + 1)) : ℝ^3 :=
  if 0 < z 0 then
    (Real.sqrt (z 0))⁻¹ • (D.U ((Real.sqrt (z 0))⁻¹ • spatialPart z) +
      cutoffField D R (Real.log (z 0)) ((Real.sqrt (z 0))⁻¹ • spatialPart z) +
      correctionField D R s (Real.log (z 0)) ((Real.sqrt (z 0))⁻¹ • spatialPart z))
  else localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R (spatialPart z)

/-- At a positive time the physical velocity is `t^{-1/2} (Ũ + U_cut + U_cor)(log t, x / √t)`. -/
theorem physicalVelocity_timeSpaceCons {t : ℝ} (ht : 0 < t) (x : ℝ^3) :
    physicalVelocity D R s (timeSpaceCons t x) =
      (Real.sqrt t)⁻¹ • (D.U ((Real.sqrt t)⁻¹ • x) +
        cutoffField D R (Real.log t) ((Real.sqrt t)⁻¹ • x) +
        correctionField D R s (Real.log t) ((Real.sqrt t)⁻¹ • x)) := by
  rw [physicalVelocity, timeSpaceCons_zero, spatialPart_timeSpaceCons, ite_eq_left ht]

/-- At a nonpositive time the physical velocity is the localized datum. -/
theorem physicalVelocity_timeSpaceCons_of_nonpos {t : ℝ} (ht : t ≤ 0) (x : ℝ^3) :
    physicalVelocity D R s (timeSpaceCons t x) = localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R x := by
  rw [physicalVelocity, timeSpaceCons_zero, spatialPart_timeSpaceCons, ite_eq_right ht.not_gt]

/-- The physical velocity at time zero is the localized datum. -/
theorem velocitySlice_physicalVelocity_zero :
    IncompressibleFlow.velocitySlice (physicalVelocity D R s) 0 =
      localizedDatum (fun x ↦ ‖x‖⁻¹ • D.A x) R :=
  funext fun x ↦ physicalVelocity_timeSpaceCons_of_nonpos D R s le_rfl x

/-- In physical variables the cutoff field is the heat flow `-e^{tΔ} w` of the localization
remainder: `t^{-1/2} U_cut(log t, x / √t) = -(e^{tΔ} w)(x)`. -/
theorem inv_sqrt_smul_cutoffField {t : ℝ} (ht : 0 < t) (x : ℝ^3) :
    (Real.sqrt t)⁻¹ • cutoffField D R (Real.log t) ((Real.sqrt t)⁻¹ • x) =
      -gaussianFlow t (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) x := by
  have hs : Real.exp (Real.log t / 2) = Real.sqrt t := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
    ring_nf
  have hs0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  rw [cutoffField, hs, Real.exp_log ht, smul_inv_smul₀ hs0, smul_neg, inv_smul_smul₀ hs0]

/-- At a positive time the physical velocity is the self-similar profile velocity, minus the heat
flow of the localization remainder, plus the physical correction. -/
theorem physicalVelocity_timeSpaceCons_eq {t : ℝ} (ht : 0 < t) (x : ℝ^3) :
    physicalVelocity D R s (timeSpaceCons t x) =
      (Real.sqrt t)⁻¹ • D.U ((Real.sqrt t)⁻¹ • x) -
        gaussianFlow t (localizationRemainder (fun x ↦ ‖x‖⁻¹ • D.A x) R) x +
        (Real.sqrt t)⁻¹ • correctionField D R s (Real.log t) ((Real.sqrt t)⁻¹ • x) := by
  rw [physicalVelocity_timeSpaceCons D R s ht, smul_add, smul_add,
    inv_sqrt_smul_cutoffField D R ht, sub_eq_add_neg]

/-- At time one similarity variables are physical: the velocity is `Ũ + U_cut(0) + U_cor(0)`. -/
theorem velocitySlice_physicalVelocity_one :
    IncompressibleFlow.velocitySlice (physicalVelocity D R s) 1 =
      D.U + cutoffField D R 0 + correctionField D R s 0 := by
  funext x
  rw [IncompressibleFlow.velocitySlice, physicalVelocity_timeSpaceCons D R s one_pos,
    Real.sqrt_one, inv_one, one_smul, one_smul, Real.log_one]
  rfl

variable {D R s} in
/-- The physical velocities of the ancient family at time one are pairwise distinct almost
everywhere: if two of them agree almost everywhere, their parameters agree. -/
theorem eq_of_velocitySlice_physicalVelocity_one_ae_eq (hR : D.ancientThreshold ≤ R)
    {s' : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hs' : s' ∈ Icc (0 : ℝ) 1)
    (h : IncompressibleFlow.velocitySlice (physicalVelocity D R s) 1 =ᵐ[volume]
      IncompressibleFlow.velocitySlice (physicalVelocity D R s') 1) : s = s' := by
  rw [velocitySlice_physicalVelocity_one, velocitySlice_physicalVelocity_one] at h
  have hc : correctionField D R s 0 =ᵐ[volume] correctionField D R s' 0 := by
    filter_upwards [h] with ξ hξ
    simpa only [Pi.add_apply, add_right_inj] using hξ
  have hbase :=
    (correctionField_ae_eq D R s 0).symm.trans (hc.trans (correctionField_ae_eq D R s' 0))
  have hlift : ∀ σ : ℝ, ancientLift D.dichotomy.η (ancientCorrection D R σ) 0 =
      ancientCorrection D R σ ⟨0, self_mem_Iic⟩ := fun σ ↦ by
    simp [ancientLift]
  refine injOn_ancientCorrection_terminal hR hs hs' ?_
  simp only
  rw [← hlift s, ← hlift s']
  refine PiLp.ext fun j ↦ WkpSpaceOn.ext_of_base_ae isOpen_univ _ _ ?_
  simp only [domainMeasure, Measure.restrict_univ]
  filter_upwards [hbase] with ξ hξ
  exact congrArg (fun v : ℝ^3 ↦ v j) hξ

end NavierStokes.Nonuniqueness
