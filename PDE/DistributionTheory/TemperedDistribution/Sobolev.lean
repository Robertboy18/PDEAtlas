/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.Sobolev

/-!
# Whole-space regularity from the distributional Laplacian

If a tempered distribution and its Laplacian belong to the Bessel space
`H^{s,p}`, then the distribution belongs to `H^{s+2,p}`. The proof uses
`J²u = u - (2π)⁻² Δu`, with Mathlib's Fourier normalization. This implication
holds for `1 ≤ p ≤ ∞` with values in a complex Banach space.

For complex Hilbert targets and `p = 2`, Mathlib's derivative estimates give
both the converse and L² representatives of every second directional derivative
of an L² distributional Poisson solution. No first derivative is assumed.
All spaces use Lebesgue measure on the whole finite-dimensional real inner
product space; no boundary condition or positive dimension is needed.

Here `H^{s,p}` means Mathlib's `TemperedDistribution.MemSobolev`, defined by a
Bessel multiplier. For `p = 1` and `p = ∞`, membership in `H^{s+2,p}` is a
statement about the Bessel potential, not about second partial derivatives in Lp.
-/

@[expose] public section

open FourierTransform MeasureTheory
open scoped ENNReal SchwartzMap LineDeriv Laplacian

namespace TemperedDistribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section Normed

variable [NormedSpace ℂ F]

/-- The order-two Bessel operator is `I - (2π)⁻² Δ`. The factor follows from
Mathlib's Fourier phase `exp (-2π i ⟪x, ξ⟫)`; the Laplacian has negative symbol. -/
theorem besselPotential_two_eq (u : 𝓢'(E, F)) :
    besselPotential E F 2 u =
      u - (Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹)) • Δ u := by
  have hsymbol : (fun x : E ↦ Complex.ofReal ((1 + ‖x‖ ^ 2) ^ ((2 : ℝ) / 2))) =
      (fun _ ↦ (1 : ℂ)) + (fun x ↦ Complex.ofReal (‖x‖ ^ 2)) := by
    ext x
    simp
  have hsum : besselPotential E F 2 u =
      u + fourierMultiplierCLM F (fun x ↦ Complex.ofReal (‖x‖ ^ 2)) u := by
    rw [besselPotential, hsymbol, fourierMultiplierCLM_apply,
      smulLeftCLM_add (by fun_prop) (by fun_prop)]
    change 𝓕⁻ (smulLeftCLM F (fun _ ↦ (1 : ℂ)) (𝓕 u) +
      smulLeftCLM F (fun x ↦ Complex.ofReal (‖x‖ ^ 2)) (𝓕 u)) =
        u + 𝓕⁻ (smulLeftCLM F (fun x ↦ Complex.ofReal (‖x‖ ^ 2)) (𝓕 u))
    rw [fourierInv_add, smulLeftCLM_const, one_smul, fourierInv_fourier_eq]
  have hnonzero : (2 * Real.pi) ^ 2 ≠ (0 : ℝ) :=
    pow_ne_zero 2 (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hscalar : Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹) *
      Complex.ofReal (-(2 * Real.pi) ^ 2) = -1 := by
    norm_cast
    rw [mul_neg, inv_mul_cancel₀ hnonzero]
    norm_num
  rw [hsum, laplacian_eq_fourierMultiplierCLM,
    ← Complex.coe_smul (-(2 * Real.pi) ^ 2), smul_smul, hscalar,
    neg_one_smul, sub_neg_eq_add]

variable [CompleteSpace F]

/-- An order-`s` Bessel distribution whose Laplacian has the same regularity
gains two orders. Membership of `u` controls the low frequencies; this is a
whole-space statement, with no assumed first derivative. -/
theorem MemSobolev.add_two_of_laplacian {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {u : 𝓢'(E, F)} (hu : MemSobolev s p u) (hΔ : MemSobolev s p (Δ u)) :
    MemSobolev (s + 2) p u := by
  have hJ : MemSobolev s p (besselPotential E F 2 u) := by
    rw [besselPotential_two_eq]
    exact hu.sub (hΔ.smul _)
  simpa only [add_comm 2 s] using memSobolev_besselPotential_iff.mp hJ

/-- For `Δu = f`, the order-two Bessel representative is the Lp class
`u - (2π)⁻² f`. Its norm is controlled by the two data norms, also at `p = 1`
and `p = ∞`. -/
theorem exists_lp_besselPotential_two_of_laplacian {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u f : Lp F p (volume : Measure E)) (hΔ : Δ (u : 𝓢'(E, F)) = (f : 𝓢'(E, F))) :
    ∃ U : Lp F p (volume : Measure E),
      besselPotential E F 2 (u : 𝓢'(E, F)) = (U : 𝓢'(E, F)) ∧
        ‖U‖ ≤ ‖u‖ + ((2 * Real.pi) ^ 2)⁻¹ * ‖f‖ := by
  refine ⟨u - Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹) • f, ?_, ?_⟩
  · rw [besselPotential_two_eq, hΔ]
    change (u : 𝓢'(E, F)) - Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹) •
      (f : 𝓢'(E, F)) = Lp.toTemperedDistributionCLM F volume p
        (u - Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹) • f)
    simp only [map_sub, map_smul, Lp.toTemperedDistributionCLM_apply]
  · calc
      ‖u - Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹) • f‖ ≤
          ‖u‖ + ‖Complex.ofReal (((2 * Real.pi) ^ 2)⁻¹) • f‖ := norm_sub_le _ _
      _ = _ := by
        rw [norm_smul, Complex.norm_of_nonneg (by positivity)]

end Normed

section Hilbert

variable [InnerProductSpace ℂ F] [CompleteSpace F]

/-- In the whole-space Hilbert-valued L² scale, two additional Sobolev orders
are equivalent to order-`s` membership of both the distribution and its Laplacian.
The forward implication uses Mathlib's Fourier multiplier derivative estimates. -/
theorem memSobolev_add_two_iff {s : ℝ} {u : 𝓢'(E, F)} :
    MemSobolev (s + 2) 2 u ↔ MemSobolev s 2 u ∧ MemSobolev s 2 (Δ u) := by
  constructor
  · intro hu
    exact ⟨hu.mono (le_add_of_nonneg_right (by norm_num)), by simpa using hu.laplacian⟩
  · rintro ⟨hu, hΔ⟩
    exact hu.add_two_of_laplacian hΔ

/-- Every second directional distributional derivative of an L² Poisson
solution is represented by an L² function when the state and forcing are L².
No H¹ witness or derivative integrability is assumed. The equation here is
`Δu = f`, so the usual convention `-Δu = f` uses the forcing `-f`. -/
theorem exists_lp_second_derivative_of_laplacian
    (u f : Lp F 2 (volume : Measure E)) (hΔ : Δ (u : 𝓢'(E, F)) = (f : 𝓢'(E, F)))
    (v w : E) :
    ∃ D : Lp F 2 (volume : Measure E),
      ∂_{v} (∂_{w} (u : 𝓢'(E, F))) = (D : 𝓢'(E, F)) := by
  have hu : MemSobolev 0 2 (u : 𝓢'(E, F)) := memSobolev_zero_iff.mpr ⟨u, rfl⟩
  have hforcing : MemSobolev 0 2 (Δ (u : 𝓢'(E, F))) :=
    memSobolev_zero_iff.mpr ⟨f, hΔ⟩
  have htwo : MemSobolev 2 2 (u : 𝓢'(E, F)) := by
    simpa only [zero_add] using hu.add_two_of_laplacian hforcing
  apply memSobolev_zero_iff.mp
  simpa only [show (2 : ℝ) - 1 - 1 = 0 by norm_num] using
    (htwo.lineDerivOp (m := w)).lineDerivOp (m := v)

end Hilbert

end TemperedDistribution
