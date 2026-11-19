/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Integration in the compactified radial coordinate

For positive scale `κ`, the map `β ↦ κ tan β` sends `(0, π/2)` bijectively
onto the positive radial half-line. The three-dimensional radial measure
`r² dr` becomes `κ³ (sin β / cos² β)² dβ`. The squared-norm formula and
integrability equivalence apply to arbitrary normed-space-valued functions.
-/

@[expose] public noncomputable section

namespace PDE.CoordinateSystems

open MeasureTheory Set

/-- A compactified radius `β ∈ (0, π/2)` has positive physical radius `κ tan β`. -/
theorem mul_tan_pos {κ β : ℝ} (hκ : 0 < κ) (hβ : β ∈ Ioo 0 (Real.pi / 2)) :
    0 < κ * Real.tan β :=
  mul_pos hκ (Real.tan_pos_of_pos_of_lt_pi_div_two hβ.1 hβ.2)

/-- Positive physical radii correspond bijectively to the open compactified interval. -/
theorem bijOn_scaled_tan {κ : ℝ} (hκ : 0 < κ) :
    BijOn (fun β : ℝ ↦ κ * Real.tan β) (Ioo 0 (Real.pi / 2)) (Ioi 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro β hβ
    exact mul_tan_pos hκ hβ
  · intro β hβ γ hγ h
    apply Real.injOn_tan
    · exact ⟨by linarith [Real.pi_pos, hβ.1], hβ.2⟩
    · exact ⟨by linarith [Real.pi_pos, hγ.1], hγ.2⟩
    · exact mul_left_cancel₀ hκ.ne' h
  · intro r hr
    refine ⟨Real.arctan (r / κ),
      ⟨Real.arctan_pos.mpr (div_pos hr hκ), Real.arctan_lt_pi_div_two _⟩, ?_⟩
    change κ * Real.tan (Real.arctan (r / κ)) = r
    rw [Real.tan_arctan, mul_div_cancel₀ _ hκ.ne']

private theorem cos_pos_of_mem_radialInterval {β : ℝ} (hβ : β ∈ Ioo 0 (Real.pi / 2)) :
    0 < Real.cos β :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hβ.1], hβ.2⟩

private theorem scaled_tan_hasDerivWithinAt (κ : ℝ) {β : ℝ}
    (hβ : β ∈ Ioo 0 (Real.pi / 2)) :
    HasDerivWithinAt (fun t : ℝ ↦ κ * Real.tan t) (κ / Real.cos β ^ 2)
      (Ioo 0 (Real.pi / 2)) β := by
  simpa only [mul_one_div] using
    ((Real.hasDerivAt_tan (cos_pos_of_mem_radialInterval hβ).ne').const_mul κ).hasDerivWithinAt

/-- Change of variables for the full positive radial half-line, without integrability assumptions.
The Bochner integrals use their usual value zero when integrability fails. -/
theorem integral_comp_scaled_tan {κ : ℝ} (hκ : 0 < κ) (g : ℝ → ℝ) :
    (∫ r in Ioi (0 : ℝ), g r) =
      ∫ β in Ioo (0 : ℝ) (Real.pi / 2), (κ / Real.cos β ^ 2) * g (κ * Real.tan β) := by
  rw [← (bijOn_scaled_tan hκ).image_eq]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun β hβ ↦ scaled_tan_hasDerivWithinAt κ hβ) (bijOn_scaled_tan hκ).injOn]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro β hβ
  change |κ / Real.cos β ^ 2| * g (κ * Real.tan β) = _
  rw [abs_of_pos (div_pos hκ (sq_pos_of_pos (cos_pos_of_mem_radialInterval hβ)))]

private theorem radial_sq_norm_jacobian {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (κ : ℝ) (f : ℝ → E) {β : ℝ}
    (hβ : β ∈ Ioo 0 (Real.pi / 2)) :
    (κ / Real.cos β ^ 2) * ((κ * Real.tan β) ^ 2 * ‖f (κ * Real.tan β)‖ ^ 2) =
      κ ^ 3 * ‖(Real.sin β / Real.cos β ^ 2) • f (κ * Real.tan β)‖ ^ 2 := by
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Real.tan_eq_sin_div_cos]
  field_simp [(cos_pos_of_mem_radialInterval hβ).ne']

/-- The radial squared norm carries the cubic physical scale factor. -/
theorem integral_radial_sq_norm_comp_scaled_tan {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {κ : ℝ} (hκ : 0 < κ) (f : ℝ → E) :
    (∫ r in Ioi (0 : ℝ), r ^ 2 * ‖f r‖ ^ 2) =
      κ ^ 3 * ∫ β in Ioo (0 : ℝ) (Real.pi / 2),
        ‖(Real.sin β / Real.cos β ^ 2) • f (κ * Real.tan β)‖ ^ 2 := by
  rw [integral_comp_scaled_tan hκ, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioo fun β hβ ↦ radial_sq_norm_jacobian κ f hβ

/-- The nonnegative radial squared-norm integral has the same cubic scale factor,
including when either side is infinite. -/
theorem lintegral_radial_sq_norm_comp_scaled_tan {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {κ : ℝ} (hκ : 0 < κ) (f : ℝ → E) :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2 * ‖f r‖ ^ 2)) =
      ∫⁻ β in Ioo (0 : ℝ) (Real.pi / 2),
        ENNReal.ofReal (κ ^ 3 *
          ‖(Real.sin β / Real.cos β ^ 2) • f (κ * Real.tan β)‖ ^ 2) := by
  rw [← (bijOn_scaled_tan hκ).image_eq,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
      (fun β hβ ↦ scaled_tan_hasDerivWithinAt κ hβ) (bijOn_scaled_tan hκ).injOn]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro β hβ
  change ENNReal.ofReal |κ / Real.cos β ^ 2| * ENNReal.ofReal _ = _
  have hderiv : 0 < κ / Real.cos β ^ 2 :=
    div_pos hκ (sq_pos_of_pos (cos_pos_of_mem_radialInterval hβ))
  rw [abs_of_pos hderiv, ← ENNReal.ofReal_mul hderiv.le, radial_sq_norm_jacobian κ f hβ]

/-- Weighted radial square integrability is equivalent to square integrability after
compactification. A positive physical scale does not change finiteness. -/
theorem integrableOn_radial_sq_norm_comp_scaled_tan_iff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {κ : ℝ} (hκ : 0 < κ) (f : ℝ → E) :
    IntegrableOn (fun r : ℝ ↦ r ^ 2 * ‖f r‖ ^ 2) (Ioi 0) ↔
      IntegrableOn (fun β : ℝ ↦
        ‖(Real.sin β / Real.cos β ^ 2) • f (κ * Real.tan β)‖ ^ 2)
        (Ioo 0 (Real.pi / 2)) := by
  rw [← (bijOn_scaled_tan hκ).image_eq,
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
      (fun β hβ ↦ scaled_tan_hasDerivWithinAt κ hβ) (bijOn_scaled_tan hκ).injOn]
  have heq : EqOn (fun β : ℝ ↦
      |κ / Real.cos β ^ 2| • ((κ * Real.tan β) ^ 2 * ‖f (κ * Real.tan β)‖ ^ 2))
      (fun β : ℝ ↦ κ ^ 3 *
        ‖(Real.sin β / Real.cos β ^ 2) • f (κ * Real.tan β)‖ ^ 2)
      (Ioo 0 (Real.pi / 2)) := by
    intro β hβ
    change |κ / Real.cos β ^ 2| * _ = _
    rw [abs_of_pos (div_pos hκ (sq_pos_of_pos (cos_pos_of_mem_radialInterval hβ)))]
    exact radial_sq_norm_jacobian κ f hβ
  rw [integrableOn_congr_fun heq measurableSet_Ioo]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (pow_ne_zero _ hκ.ne')) _

end PDE.CoordinateSystems
