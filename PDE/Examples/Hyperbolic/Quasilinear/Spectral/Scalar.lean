/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.ConservationLaw.System.Characteristics.SmoothFrame
public import PDE.Hyperbolic.Quasilinear.Spectral.Frame
public import PDE.Examples.Hyperbolic.ConservationLaw.System.OneComponent
import CAS.ExactTactic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import PDE.Symbolic.PDEDerivatives

/-!
# A scalar flux with a smooth characteristic field

The scalar flux `z⁴/4 - z²/2 + 7z` has the nonconstant characteristic speed
`z³ - z + 7`, and `exists_smooth_unit_characteristicFields` gives a smooth unit
characteristic field with this speed (`exists_smooth_unit_field`).
-/

@[expose] public noncomputable section

namespace PDE.Examples.Hyperbolic.Quasilinear.Spectral.Scalar

open PDE.Common PDE.Hyperbolic.ConservationLaw.System
open PDE.Examples.Hyperbolic.ConservationLaw.System
open scoped ContDiff Matrix.Norms.Elementwise

/-- A scalar quartic flux with a nonconstant characteristic speed. -/
def flux (z : ℝ^1) : ℝ^1 := !₂[z 0 ^ 4 / 4 - z 0 ^ 2 / 2 + 7 * z 0]

/-- The flux is smooth. -/
theorem contDiff_flux : ContDiff ℝ ∞ flux := by
  rw [contDiff_piLp]
  intro i
  fin_cases i
  change ContDiff ℝ ∞ (fun z : ℝ^1 ↦ z 0 ^ 4 / 4 - z 0 ^ 2 / 2 + 7 * z 0)
  cas

/-- The Jacobian of the flux is multiplication by `z³ - z + 7`. -/
theorem fderiv_flux (z v : ℝ^1) :
    fderiv ℝ flux z v = (z 0 ^ 3 - z 0 + 7) • v := by
  rw [fderiv_apply_eq_sum_smul_partialDeriv]
  ext i
  fin_cases i
  simp only [Fin.sum_univ_one, PiLp.smul_apply, smul_eq_mul]
  change v 0 * (∂[0] flux) z 0 = (z 0 ^ 3 - z 0 + 7) * v 0
  have hd : (∂[0] flux) z 0 = z 0 ^ 3 - z 0 + 7 := by
    rw [partialDeriv_apply 0 0 (contDiff_flux.differentiable (by simp) z)]
    change (∂[0] ((fun z : ℝ^1 ↦ z 0 ^ 4 / 4 - z 0 ^ 2 / 2 + 7 * z 0) : ℝ^1 → ℝ)) z =
      z 0 ^ 3 - z 0 + 7
    cas
  rw [hd]
  exact mul_comm _ _

/-- The flux is strictly hyperbolic at every state. -/
theorem isStrictlyHyperbolicAt_flux (z : ℝ^1) : IsStrictlyHyperbolicAt flux z :=
  OneComponent.isStrictlyHyperbolicAt_of_fderiv_eq_smul
    (contDiff_flux.differentiable (by simp) z) (fderiv_flux z)

/-- The characteristic speed is `z³ - z + 7`. -/
theorem characteristicSpeed_flux (z : ℝ^1) :
    characteristicSpeed flux 0 z = z 0 ^ 3 - z 0 + 7 :=
  OneComponent.characteristicSpeed_eq_of_fderiv_eq_smul (fderiv_flux z) 0

/-- The flux has a smooth unit characteristic field with speed `z³ - z + 7`. -/
theorem exists_smooth_unit_field :
    ∃ C : CharacteristicField flux,
      (∀ z, C.speed z = z 0 ^ 3 - z 0 + 7) ∧
      ContDiff ℝ ∞ C.speed ∧ ContDiff ℝ ∞ C.rightEigenvector ∧
      ∀ z, ‖C.rightEigenvector z‖ = 1 := by
  obtain ⟨C, hC, _⟩ :=
    exists_smooth_unit_characteristicFields contDiff_flux isStrictlyHyperbolicAt_flux
  refine ⟨C 0, ?_, (hC 0).2⟩
  intro z
  rw [(hC 0).1]
  exact characteristicSpeed_flux z

end PDE.Examples.Hyperbolic.Quasilinear.Spectral.Scalar
