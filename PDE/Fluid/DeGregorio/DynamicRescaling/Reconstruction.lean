/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.DeGregorio.DynamicRescaling.ClockInverse
import CAS.ExactTactic

/-!
# Reconstructing physical fields

At physical time `t`, invert the clock to find `τ`, then undo the spatial and
amplitude scales. This defines the physical fields on the clock's image. Their
regularity follows from that of the rescaled fields and from the proved
derivative of the inverse clock.

The transport calculation reuses the forward residual identity: rescaling the
constructed fields gives back the original rescaled trajectory. The spectral
Hilbert transform's dilation law supplies the Biot–Savart equation.
-/

@[expose] public noncomputable section

open PDE.Analysis PDE.Representations.Similarity

namespace DeGregorio

open DynamicRescalingData

/-- Undo the rescaling at the inverse physical clock. Only times in the clock's
range are used to state the reconstructed equation. -/
def physicallyReconstructedFields (data : DynamicRescalingData) (fields : Fields) : Fields where
  vorticity x t :=
    (data.vorticityScale (data.rescaledTime t))⁻¹ *
      fields.vorticity (x / data.spatialScale (data.rescaledTime t)) (data.rescaledTime t)
  velocity x t :=
    data.spatialScale (data.rescaledTime t) / data.vorticityScale (data.rescaledTime t) *
      fields.velocity (x / data.spatialScale (data.rescaledTime t)) (data.rescaledTime t)

/-- The initial physical vorticity is the initial rescaled profile. -/
@[simp]
theorem physicallyReconstructedFields_vorticity_zero
    (cl : ℝ → ℝ) {cw : ℝ → ℝ} (hcw : Continuous cw) (fields : Fields) (x : ℝ) :
    (physicallyReconstructedFields (ofRates cl cw) fields).vorticity x 0 =
      fields.vorticity x 0 := by
  simp only [physicallyReconstructedFields, rescaledTime_ofRates_zero cl hcw,
    vorticityScale_ofRates_zero, spatialScale_ofRates_zero, inv_one, div_one, one_mul]

/-- The initial physical velocity is the initial rescaled velocity. -/
@[simp]
theorem physicallyReconstructedFields_velocity_zero
    (cl : ℝ → ℝ) {cw : ℝ → ℝ} (hcw : Continuous cw) (fields : Fields) (x : ℝ) :
    (physicallyReconstructedFields (ofRates cl cw) fields).velocity x 0 =
      fields.velocity x 0 := by
  simp only [physicallyReconstructedFields, rescaledTime_ofRates_zero cl hcw,
    vorticityScale_ofRates_zero, spatialScale_ofRates_zero, div_one, one_mul]

/-- Reconstructing and then rescaling recovers the original fields at every
rescaled time, because the constructed clock is injective. -/
theorem dynamicallyRescaledFields_physicallyReconstructedFields
    (cl : ℝ → ℝ) {cw : ℝ → ℝ} (hcw : Continuous cw) (fields : Fields) :
    dynamicallyRescaledFields (ofRates cl cw)
      (physicallyReconstructedFields (ofRates cl cw) fields) = fields := by
  cases fields with
  | mk ω u =>
    change Fields.mk _ _ = Fields.mk ω u
    congr 1 <;> funext x τ
    · simp only [physicallyReconstructedFields, dynamicPullback, smul_eq_mul,
        rescaledTime_ofRates_physicalTime cl hcw]
      have hA := (vorticityScale_ofRates_pos cl cw τ).ne'
      have hL := (spatialScale_ofRates_pos cl cw τ).ne'
      rw [← mul_assoc, mul_inv_cancel₀ hA, one_mul, mul_div_cancel_left₀ x hL]
    · simp only [physicallyReconstructedFields, rescaledTime_ofRates_physicalTime cl hcw]
      have hA := (vorticityScale_ofRates_pos cl cw τ).ne'
      have hL := (spatialScale_ofRates_pos cl cw τ).ne'
      rw [mul_div_cancel_left₀ x hL]
      cas

/-- The inverse clock and positive scales transfer classical regularity to the
constructed physical fields on the image of the rescaled time domain. -/
theorem HasClassicalRegularityOn.physicallyReconstructedFields
    {fields : Fields} {times : Set ℝ}
    (hregularity : HasClassicalRegularityOn fields times)
    {cl cw : ℝ → ℝ} (hcl : Continuous cl) (hcw : Continuous cw) :
    HasClassicalRegularityOn (physicallyReconstructedFields (ofRates cl cw) fields)
      ((ofRates cl cw).physicalTime '' times) := by
  constructor
  · rintro x t ⟨τ, hτ, rfl⟩
    have hinv := (rescaledTime_ofRates_hasStrictDerivAt cl hcw τ).hasDerivAt.differentiableAt
    have htime : DifferentiableAt ℝ
        (fun p : ℝ × ℝ ↦ (ofRates cl cw).rescaledTime p.2)
        (x, (ofRates cl cw).physicalTime τ) :=
      hinv.comp (x, (ofRates cl cw).physicalTime τ) differentiableAt_snd
    have hlaws := satisfiesDynamicScaleODEsAt_ofRates hcl hcw τ
    have hA := hlaws.vorticityScale_hasDerivAt.differentiableAt
    have hL := hlaws.spatialScale_hasDerivAt.differentiableAt
    have htimeEq := rescaledTime_ofRates_physicalTime cl hcw τ
    have hAc := (htimeEq ▸ hA).comp (x, (ofRates cl cw).physicalTime τ) htime
    have hLc := (htimeEq ▸ hL).comp (x, (ofRates cl cw).physicalTime τ) htime
    have hAnonzero : (ofRates cl cw).vorticityScale
        ((ofRates cl cw).rescaledTime ((ofRates cl cw).physicalTime τ)) ≠ 0 :=
      (vorticityScale_ofRates_pos cl cw _).ne'
    have hLnonzero : (ofRates cl cw).spatialScale
        ((ofRates cl cw).rescaledTime ((ofRates cl cw).physicalTime τ)) ≠ 0 :=
      (spatialScale_ofRates_pos cl cw _).ne'
    have hfst : DifferentiableAt ℝ (fun p : ℝ × ℝ ↦ p.1)
        (x, (ofRates cl cw).physicalTime τ) := differentiableAt_fst
    have hspace : DifferentiableAt ℝ
        (fun p : ℝ × ℝ ↦ p.1 / (ofRates cl cw).spatialScale
          ((ofRates cl cw).rescaledTime p.2)) (x, (ofRates cl cw).physicalTime τ) := by
      simpa only [div_eq_mul_inv, Function.comp_apply] using
        hfst.fun_mul (hLc.fun_inv hLnonzero)
    have hpath := hspace.prodMk htime
    have hω := hregularity.vorticity_differentiableAt
      (x := x / (ofRates cl cw).spatialScale τ) hτ
    have hωc := (show DifferentiableAt ℝ (Function.uncurry fields.vorticity)
        (x / (ofRates cl cw).spatialScale
          ((ofRates cl cw).rescaledTime ((ofRates cl cw).physicalTime τ)),
          (ofRates cl cw).rescaledTime ((ofRates cl cw).physicalTime τ)) by
      simpa only [htimeEq] using hω).comp (x, (ofRates cl cw).physicalTime τ) hpath
    exact (hAc.fun_inv hAnonzero).fun_mul hωc
  · rintro x t ⟨τ, hτ, rfl⟩
    change DifferentiableAt ℝ
      (fun y ↦ (ofRates cl cw).spatialScale
          ((ofRates cl cw).rescaledTime ((ofRates cl cw).physicalTime τ)) /
        (ofRates cl cw).vorticityScale
          ((ofRates cl cw).rescaledTime ((ofRates cl cw).physicalTime τ)) *
        fields.velocity (y / (ofRates cl cw).spatialScale
          ((ofRates cl cw).rescaledTime ((ofRates cl cw).physicalTime τ)))
          ((ofRates cl cw).rescaledTime ((ofRates cl cw).physicalTime τ))) x
    rw [rescaledTime_ofRates_physicalTime cl hcw]
    exact ((hregularity.velocity_differentiableAt hτ).comp x
      (differentiableAt_id.div_const _)).const_mul _

/-- Undoing the positive spatial dilation preserves the concrete Hilbert pair.
The velocity amplitude cancels the factor from its spatial derivative. -/
theorem SatisfiesBiotSavartOn.physicallyReconstructedFields
    {fields : Fields} {times : Set ℝ}
    (hbiotSavart : SatisfiesBiotSavartOn fields times)
    (hregularity : HasClassicalRegularityOn fields times)
    (cl : ℝ → ℝ) {cw : ℝ → ℝ} (hcw : Continuous cw) :
    SatisfiesBiotSavartOn (physicallyReconstructedFields (ofRates cl cw) fields)
      ((ofRates cl cw).physicalTime '' times) := by
  rintro t ⟨τ, hτ, rfl⟩
  dsimp only [DeGregorio.physicallyReconstructedFields]
  rw [rescaledTime_ofRates_physicalTime cl hcw]
  have hA := (vorticityScale_ofRates_pos cl cw τ).ne'
  have hL := spatialScale_ofRates_pos cl cw τ
  have hderiv :
      deriv (fun x ↦ (ofRates cl cw).spatialScale τ / (ofRates cl cw).vorticityScale τ *
        fields.velocity (x / (ofRates cl cw).spatialScale τ) τ) =
      fun x ↦ ((ofRates cl cw).vorticityScale τ)⁻¹ *
        deriv (fun y ↦ fields.velocity y τ) (x / (ofRates cl cw).spatialScale τ) := by
    funext x
    have h := ((hregularity.velocity_differentiableAt
      (x := x / (ofRates cl cw).spatialScale τ) hτ).hasDerivAt.comp x
        ((hasDerivAt_id x).div_const ((ofRates cl cw).spatialScale τ))).const_mul
          ((ofRates cl cw).spatialScale τ / (ofRates cl cw).vorticityScale τ)
    have hd := h.deriv
    simp only [Function.comp_apply, id_eq] at hd
    rw [hd]
    have hLne := hL.ne'
    cas
  rw [hderiv]
  simpa only [inv_mul_eq_div] using
    ((hbiotSavart hτ).dilate (inv_pos.mpr hL)).const_mul
      ((ofRates cl cw).vorticityScale τ)⁻¹

/-- A classical rescaled trajectory with continuous rates determines a classical physical
solution on the image of its time set under the clock. -/
theorem IsClassicalRescaledSolutionOn.physicallyReconstructedFields
    {a : ℝ} {fields : Fields} {cl cw : ℝ → ℝ} {times : Set ℝ}
    (hsol : IsClassicalRescaledSolutionOn a fields cl cw times)
    (hcl : Continuous cl) (hcw : Continuous cw) :
    IsClassicalSolutionOn a (physicallyReconstructedFields (ofRates cl cw) fields)
      ((ofRates cl cw).physicalTime '' times) := by
  have hregularity := hsol.regularity.physicallyReconstructedFields hcl hcw
  refine ⟨hregularity, ?_,
    hsol.biotSavart.physicallyReconstructedFields hsol.regularity cl hcw⟩
  apply (satisfiesRescaledTransportEquationOn_iff_transport a (ofRates cl cw)
    (DeGregorio.physicallyReconstructedFields (ofRates cl cw) fields) times hregularity
    (fun τ _ ↦ satisfiesDynamicScaleODEsAt_ofRates hcl hcw τ)
    (fun τ _ ↦ (spatialScale_ofRates_pos cl cw τ).ne')
    (fun τ _ ↦ (vorticityScale_ofRates_pos cl cw τ).ne')).mp
  rw [dynamicallyRescaledFields_physicallyReconstructedFields cl hcw]
  exact hsol.transport

end DeGregorio
