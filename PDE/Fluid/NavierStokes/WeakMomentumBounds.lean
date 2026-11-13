/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Fluid.NavierStokes.WeakSolutions
import PDE.Analysis.MeasureTheory.Integral.CollarEstimate
import PDE.Analysis.MeasureTheory.Lp.PairingConvergence
import PDE.FDeriv.SpaceTime

/-!
# Slice bounds for the weak momentum pairing

Against a fixed weak momentum test, the unforced weak momentum integrand of a velocity,
pressure and gradient field with square-integrable slices is integrable on the slice, and
its integral is bounded by a constant depending on the test times
`‖u‖₂ + ‖u‖₂² + ‖p‖₂ + ‖Du‖₂`. The velocity enters linearly against the time derivative of the
test, quadratically against its spatial gradient, and the pressure and gradient pair with the
divergence and gradient of the test, all of which are continuous with compact support.
-/

@[expose] public section

namespace NavierStokes

open EuclideanSpace MeasureTheory IncompressibleFlow PDE PDE.Common PDE.Analysis

set_option linter.missingDocs true

variable {n : ℕ}

/-- Against a bounded continuous matrix field, the convection pairing of a velocity with a
square-integrable slice is integrable, and its integral is bounded by the bound of the field
times the squared `L²` norm of the slice. -/
theorem integrable_convectionPairing_and_abs_integral_le {u : ℝ^(n + 1) → ℝ^n} {t : ℝ}
    {G : ℝ^(n + 1) → SpatialMatrix n} (hu : MemLp (velocitySlice u t) 2 volume)
    (hG : Continuous G) {S : ℝ} (hS : ∀ z, ‖G z‖ ≤ S) :
    Integrable (fun x ↦ inner ℝ
        (spatialOuterProduct (velocitySlice u t x) (velocitySlice u t x))
        (G (timeSpaceCons t x))) ∧
      |∫ x, inner ℝ (spatialOuterProduct (velocitySlice u t x) (velocitySlice u t x))
        (G (timeSpaceCons t x))| ≤ S * (eLpNorm (velocitySlice u t) 2 volume).toReal ^ 2 := by
  have hsq : Integrable (fun x ↦ ‖velocitySlice u t x‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 hu
  have hpt : ∀ x, ‖inner ℝ (spatialOuterProduct (velocitySlice u t x) (velocitySlice u t x))
      (G (timeSpaceCons t x))‖ ≤ S * ‖velocitySlice u t x‖ ^ 2 := by
    intro x
    calc _ ≤ ‖spatialOuterProduct (velocitySlice u t x) (velocitySlice u t x)‖ *
          ‖G (timeSpaceCons t x)‖ := norm_inner_le_norm _ _
      _ = ‖velocitySlice u t x‖ ^ 2 * ‖G (timeSpaceCons t x)‖ := by
          rw [norm_spatialOuterProduct, sq]
      _ ≤ ‖velocitySlice u t x‖ ^ 2 * S := mul_le_mul_of_nonneg_left (hS _) (by positivity)
      _ = S * ‖velocitySlice u t x‖ ^ 2 := mul_comm _ _
  have hmeas : AEStronglyMeasurable (fun x ↦ inner ℝ
      (spatialOuterProduct (velocitySlice u t x) (velocitySlice u t x))
      (G (timeSpaceCons t x))) volume :=
    (continuous_spatialOuterProduct_self.comp_aestronglyMeasurable
      hu.aestronglyMeasurable).inner
      (hG.comp (contDiff_timeSpaceCons_spatial n t (m := 0)).continuous).aestronglyMeasurable
  refine ⟨(hsq.const_mul S).mono' hmeas (ae_of_all _ hpt), ?_⟩
  rw [← Real.norm_eq_abs]
  calc _ ≤ ∫ x, S * ‖velocitySlice u t x‖ ^ 2 :=
        norm_integral_le_of_norm_le (hsq.const_mul S) (ae_of_all _ hpt)
    _ = _ := by rw [integral_const_mul, integral_norm_sq_eq_eLpNorm_toReal_sq hu]

/-- With zero forcing, the weak momentum integrand is the sum of the transport, convection,
pressure and viscous pairings. -/
theorem weakMomentumIntegrand_eq_of_forcing_eq_zero {nse : Problem n}
    (hforce : nse.forcing = 0) (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ)
    (Du : SpatialGradientField n) (φ : ℝ^(n + 1) → ℝ^n) (t : ℝ) (x : ℝ^n) :
    weakMomentumIntegrand nse u p Du φ t x =
      -inner ℝ (velocitySlice u t x) (timeDerivative n φ (timeSpaceCons t x))
      - inner ℝ (spatialOuterProduct (velocitySlice u t x) (velocitySlice u t x))
          (spatialVelocityGradient n φ (timeSpaceCons t x))
      - inner ℝ (spatialDivergence n φ (timeSpaceCons t x)) (p (timeSpaceCons t x))
      + nse.kinematicViscosity * inner ℝ (spatialGradientSlice Du t x)
          (spatialVelocityGradient n φ (timeSpaceCons t x)) := by
  simp only [weakMomentumIntegrand, inviscidWeakMomentumIntegrand, hforce, Pi.zero_apply,
    inner_zero_left, sub_zero, velocitySlice, spatialGradientSlice, RCLike.inner_apply,
    conj_trivial]

/-- The unforced weak momentum integrand of fields with square-integrable slices is
integrable on the slice. -/
theorem integrable_weakMomentumIntegrand {nse : Problem n} (hforce : nse.forcing = 0)
    {u : ℝ^(n + 1) → ℝ^n} {p : ℝ^(n + 1) → ℝ} {Du : SpatialGradientField n} {T t : ℝ}
    (hu : MemLp (velocitySlice u t) 2 volume)
    (hp : MemLp (fun x ↦ p (timeSpaceCons t x)) 2 volume)
    (hD : MemLp (spatialGradientSlice Du t) 2 volume)
    {φ : ℝ^(n + 1) → ℝ^n} (hφ : IsWeakMomentumTest T φ) :
    Integrable (fun x ↦ weakMomentumIntegrand nse u p Du φ t x) := by
  obtain ⟨hTc, hTs⟩ := hφ.continuous_hasCompactSupport_timeDerivative
  obtain ⟨hGc, hGs⟩ := hφ.continuous_hasCompactSupport_spatialVelocityGradient
  obtain ⟨hdc, hds⟩ := hφ.continuous_hasCompactSupport_spatialDivergence
  obtain ⟨_, _, hT⟩ := exists_eLpNorm_slice_le hTc hTs
  obtain ⟨_, _, hG⟩ := exists_eLpNorm_slice_le hGc hGs
  obtain ⟨_, _, hd⟩ := exists_eLpNorm_slice_le hdc hds
  obtain ⟨S, hS⟩ := hGc.bounded_above_of_compact_support hGs
  simp_rw [weakMomentumIntegrand_eq_of_forcing_eq_zero hforce]
  exact (((integrable_inner_of_memLp_two hu (hT t).1).neg.sub
    (integrable_convectionPairing_and_abs_integral_le hu hGc hS).1).sub
    (integrable_inner_of_memLp_two (hd t).1 hp)).add
    ((integrable_inner_of_memLp_two hD (hG t).1).const_mul _)

/-- Against a fixed test, the unforced weak momentum slice is bounded by a constant times
`‖u‖₂ + ‖u‖₂² + ‖p‖₂ + ‖Du‖₂`. -/
theorem exists_abs_weakMomentumSlice_le {nse : Problem n} (hforce : nse.forcing = 0) {T : ℝ}
    {φ : ℝ^(n + 1) → ℝ^n} (hφ : IsWeakMomentumTest T φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (u : ℝ^(n + 1) → ℝ^n) (p : ℝ^(n + 1) → ℝ) (Du : SpatialGradientField n)
      (t : ℝ), MemLp (velocitySlice u t) 2 volume →
      MemLp (fun x ↦ p (timeSpaceCons t x)) 2 volume →
      MemLp (spatialGradientSlice Du t) 2 volume →
      |weakMomentumSlice nse u p Du φ t| ≤
        M * ((eLpNorm (velocitySlice u t) 2 volume).toReal +
          (eLpNorm (velocitySlice u t) 2 volume).toReal ^ 2 +
          (eLpNorm (fun x ↦ p (timeSpaceCons t x)) 2 volume).toReal +
          (eLpNorm (spatialGradientSlice Du t) 2 volume).toReal) := by
  obtain ⟨hTc, hTs⟩ := hφ.continuous_hasCompactSupport_timeDerivative
  obtain ⟨hGc, hGs⟩ := hφ.continuous_hasCompactSupport_spatialVelocityGradient
  obtain ⟨hdc, hds⟩ := hφ.continuous_hasCompactSupport_spatialDivergence
  obtain ⟨M₁, hM₁, hT⟩ := exists_eLpNorm_slice_le hTc hTs
  obtain ⟨M₄, hM₄, hG⟩ := exists_eLpNorm_slice_le hGc hGs
  obtain ⟨M₃, hM₃, hd⟩ := exists_eLpNorm_slice_le hdc hds
  obtain ⟨S, hS⟩ := hGc.bounded_above_of_compact_support hGs
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0)
  have hν : (0 : ℝ) ≤ nse.kinematicViscosity := nse.kinematicViscosity.2.le
  refine ⟨M₁ + S + M₃ + nse.kinematicViscosity * M₄, by positivity,
    fun u p Du t hu hp hD ↦ ?_⟩
  obtain ⟨hBi, hB⟩ := integrable_convectionPairing_and_abs_integral_le hu hGc hS
  have hAi := integrable_inner_of_memLp_two hu (hT t).1
  have hPi := integrable_inner_of_memLp_two (hd t).1 hp
  have hDi := integrable_inner_of_memLp_two hD (hG t).1
  have hA := (abs_integral_inner_le_eLpNorm_mul hu (hT t).1).trans
    (mul_le_mul_of_nonneg_left (hT t).2 ENNReal.toReal_nonneg)
  have hP := (abs_integral_inner_le_eLpNorm_mul (hd t).1 hp).trans
    (mul_le_mul_of_nonneg_right (hd t).2 ENNReal.toReal_nonneg)
  have hDb := (abs_integral_inner_le_eLpNorm_mul hD (hG t).1).trans
    (mul_le_mul_of_nonneg_left (hG t).2 ENNReal.toReal_nonneg)
  rw [weakMomentumSlice]
  simp_rw [weakMomentumIntegrand_eq_of_forcing_eq_zero hforce]
  rw [integral_add ((hAi.fun_neg.sub' hBi).sub' hPi) (hDi.const_mul _),
    integral_sub (hAi.fun_neg.sub' hBi) hPi, integral_sub hAi.fun_neg hBi, integral_neg,
    integral_const_mul]
  set ν : ℝ := (nse.kinematicViscosity : ℝ)
  set a := (eLpNorm (velocitySlice u t) 2 volume).toReal
  set c := (eLpNorm (fun x ↦ p (timeSpaceCons t x)) 2 volume).toReal
  set d := (eLpNorm (spatialGradientSlice Du t) 2 volume).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hc : 0 ≤ c := ENNReal.toReal_nonneg
  have hd0 : 0 ≤ d := ENNReal.toReal_nonneg
  have hνM : 0 ≤ ν * M₄ := mul_nonneg hν hM₄
  have h1 := mul_le_mul_of_nonneg_right (show M₁ ≤ M₁ + S + M₃ + ν * M₄ by linarith) ha
  have h2 := mul_le_mul_of_nonneg_right (show S ≤ M₁ + S + M₃ + ν * M₄ by linarith)
    (sq_nonneg a)
  have h3 := mul_le_mul_of_nonneg_right (show M₃ ≤ M₁ + S + M₃ + ν * M₄ by linarith) hc
  have h4 := mul_le_mul_of_nonneg_right (show ν * M₄ ≤ M₁ + S + M₃ + ν * M₄ by linarith) hd0
  have hνD : |ν * ∫ x, inner ℝ (spatialGradientSlice Du t x)
      (spatialVelocityGradient n φ (timeSpaceCons t x))| ≤ ν * (d * M₄) := by
    rw [abs_mul, abs_of_nonneg hν]
    exact mul_le_mul_of_nonneg_left hDb hν
  rw [abs_le] at hA hB hP hνD ⊢
  constructor <;> linarith

end NavierStokes
