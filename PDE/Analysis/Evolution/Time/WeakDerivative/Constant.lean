/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Evolution.Time.WeakDerivative.LocalConstant
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Locally integrable functions with zero weak derivative

A smooth compactly supported function of integral zero is the derivative
of another smooth compactly supported function. Subtracting a fixed test
function of integral one then shows that a locally integrable function
with zero weak derivative is almost everywhere constant.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff Topology

namespace PDE.Analysis

/-- A smooth compactly supported test of integral zero has a smooth compactly
supported antiderivative. The zero integral makes the primitive vanish on
both sides of the support. -/
theorem exists_compactSupport_antiderivative_of_integral_eq_zero
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcs : HasCompactSupport φ)
    (hzero : ∫ x, φ x = 0) :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      ∀ x, HasDerivAt ψ (φ x) x := by
  obtain ⟨r, _hrpos, hr⟩ := hcs.isBounded.subset_ball_lt 0 (0 : ℝ)
  have hsupp : tsupport φ ⊆ Ioo (-r) r := by
    simpa only [Real.ball_zero_eq_Ioo] using hr
  obtain ⟨ψ, hψ, hψcs, _, hdψ⟩ :=
    exists_compactSupport_antiderivative_on_Ioo_of_integral_eq_zero hφ hcs hsupp hzero
  exact ⟨ψ, hψ, hψcs, hdψ⟩

namespace Evolution.HasWeakTimeDerivativeOn

/-- A real locally integrable function with zero distributional derivative
on the whole line is almost everywhere constant. No continuity of the
function is assumed. -/
theorem exists_ae_eq_const_of_zero {f : ℝ → ℝ}
    (hweak : HasWeakTimeDerivativeOn univ f 0) :
    ∃ c : ℝ, f =ᵐ[volume] fun _ ↦ c := by
  let b : ContDiffBump (0 : ℝ) :=
    ⟨1, 2, by norm_num, by norm_num⟩
  let ρ : ℝ → ℝ := b.normed volume
  have hρ : ContDiff ℝ ∞ ρ := b.contDiff_normed
  have hρcs : HasCompactSupport ρ := b.hasCompactSupport_normed
  have hρint : Integrable ρ volume := b.integrable_normed
  have hρone : ∫ x, ρ x = 1 := b.integral_normed
  let c : ℝ := ∫ x, f x * ρ x
  refine ⟨c, ?_⟩
  apply ae_eq_of_integral_contDiff_smul_eq
    (locallyIntegrableOn_univ.mp hweak.locallyIntegrable_f)
    (continuous_const.locallyIntegrable : LocallyIntegrable (fun _ : ℝ ↦ c) volume)
  intro φ hφ hcs
  have hφint : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hcs
  let ψ : ℝ → ℝ := fun x ↦ φ x - (∫ t, φ t) * ρ x
  have hψ : ContDiff ℝ ∞ ψ := hφ.sub (contDiff_const.mul hρ)
  have hψcs : HasCompactSupport ψ := hcs.sub hρcs.mul_left
  have hψzero : ∫ x, ψ x = 0 := by
    dsimp only [ψ]
    rw [integral_sub hφint (hρint.const_mul _), integral_const_mul, hρone,
      mul_one, sub_self]
  obtain ⟨χ, hχ, hχcs, hdχ⟩ :=
    exists_compactSupport_antiderivative_of_integral_eq_zero hψ hψcs hψzero
  have hz := hweak.integral_eq (ContinuousLinearMap.id ℝ ℝ) χ hχ hχcs (subset_univ _)
  have hderiv : deriv χ = ψ := funext fun x ↦ (hdχ x).deriv
  have hz' : (∫ x, f x * ψ x) = 0 := by
    simpa only [ContinuousLinearMap.id_apply, Pi.zero_apply, zero_mul, integral_zero,
      hderiv, neg_eq_zero] using hz.symm
  have hleft := integrable_mul_test hweak.locallyIntegrable_f hφ.continuous hcs
    (subset_univ _)
  have hright := integrable_mul_test hweak.locallyIntegrable_f hρ.continuous hρcs
    (subset_univ _)
  have halg (x : ℝ) :
      f x * ψ x = f x * φ x - (∫ t, φ t) * (f x * ρ x) := by
    dsimp only [ψ]
    ring
  simp_rw [halg] at hz'
  rw [integral_sub hleft (hright.const_mul _), integral_const_mul] at hz'
  have heq : (∫ x, f x * φ x) = (∫ x, φ x) * c := sub_eq_zero.mp hz'
  simpa only [smul_eq_mul, mul_comm, integral_const_mul, integral_mul_const] using heq

end Evolution.HasWeakTimeDerivativeOn

end PDE.Analysis
