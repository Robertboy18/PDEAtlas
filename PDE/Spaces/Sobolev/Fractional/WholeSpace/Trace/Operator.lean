/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.BesselRestriction
public import PDE.Spaces.Sobolev.Fractional.WholeSpace.Trace.KernelWeight

/-!
# The Bessel hyperplane restriction and its bounded lifting

The physically normalized operators have norm bounds `sqrt π` and
`1 / sqrt π`. The right-inverse identity is a consequence of the explicitly
normalized Cauchy kernel. Their agreement with classical boundary restriction
is established in `SchwartzAgreement`.
-/

@[expose] public section

noncomputable section

open MeasureTheory FourierTransform BesselPotentialSpace
open scoped BesselPotentialSpace

namespace SobolevSpace.Fractional.Trace

/-- The hyperplane trace in Bessel coordinates, with physical Fourier normalization. -/
def wholeSpaceTraceCLM (n : ℕ) :
    H^{(1 : ℝ)}(ℝ^(n + 1)) →L[ℂ] H^{(1 / 2 : ℝ)}(ℝ^n) :=
  (Real.sqrt Real.pi : ℂ) • besselNormalRestrictionCLM n

/-- The bounded right inverse of the hyperplane trace. -/
def wholeSpaceLiftingCLM (n : ℕ) :
    H^{(1 / 2 : ℝ)}(ℝ^n) →L[ℂ] H^{(1 : ℝ)}(ℝ^(n + 1)) :=
  (Real.sqrt Real.pi : ℂ)⁻¹ • (besselNormalLiftLI n).toContinuousLinearMap

/-- Fourier coordinates of the physically normalized trace. -/
theorem fourier_toLp_wholeSpaceTraceCLM (n : ℕ) (u : H^{(1 : ℝ)}(ℝ^(n + 1))) :
    𝓕 (toLp (wholeSpaceTraceCLM n u)) =
      (Real.sqrt Real.pi : ℂ) • normalRestriction n (splitFrequencyLI n (𝓕 (toLp u))) := by
  rw [wholeSpaceTraceCLM, smul_apply, toLp_smul, fourier_smul,
    fourier_toLp_besselNormalRestrictionCLM]

/-- The whole-space trace estimate in the Bessel norms. -/
theorem norm_wholeSpaceTraceCLM_apply_le (n : ℕ) (u : H^{(1 : ℝ)}(ℝ^(n + 1))) :
    ‖wholeSpaceTraceCLM n u‖ ≤ Real.sqrt Real.pi * ‖u‖ := by
  rw [wholeSpaceTraceCLM, smul_apply, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (norm_besselNormalRestrictionCLM_apply_le n u)
    (Real.sqrt_nonneg _)

/-- The constructed lifting has an exact norm formula. -/
theorem norm_wholeSpaceLiftingCLM (n : ℕ) (v : H^{(1 / 2 : ℝ)}(ℝ^n)) :
    ‖wholeSpaceLiftingCLM n v‖ = (Real.sqrt Real.pi)⁻¹ * ‖v‖ := by
  simp only [wholeSpaceLiftingCLM, smul_apply, norm_smul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]

/-- Every boundary Bessel element has the explicitly constructed lift. -/
theorem wholeSpaceTraceCLM_wholeSpaceLiftingCLM (n : ℕ) (v : H^{(1 / 2 : ℝ)}(ℝ^n)) :
    wholeSpaceTraceCLM n (wholeSpaceLiftingCLM n v) = v := by
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  simp only [wholeSpaceTraceCLM, wholeSpaceLiftingCLM, smul_apply,
    map_smul, LinearIsometry.coe_toContinuousLinearMap,
    besselNormalRestrictionCLM_besselNormalLiftLI, smul_smul, inv_mul_cancel₀ hπ, one_smul]

end SobolevSpace.Fractional.Trace
