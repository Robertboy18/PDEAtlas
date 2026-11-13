/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.GradientBounds
public import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.BiotSavart
public import PDE.Fluid.Incompressible.StreamFunction
public import Mathlib.MeasureTheory.Function.L2Space
import PDE.Elliptic.PotentialTheory.GreenFunction.HalfSpace.QuadrantSymmetrization
import PDE.Analysis.Normed.PiLp.CompareExp

/-!
# Dipole decay of the half-plane Green gradient and finite energy

For a source supported in the ball of radius `R`, the Dirichlet Green potential of the upper
half-plane is the potential of the odd extension, a charge and its mirror image. Their
gradient kernels cancel to first order: with `g(z) = -z / (2π |z|²)`, the inversion identity
`|a/|a|² - b/|b|²| = |a - b| / (|a| |b|)` gives

```text
|g(x - y) - g(x - y*)| = |y - y*| / (2π |x - y| |x - y*|) ≤ R / (π (|x| - R)²)
```

for `|y| ≤ R < |x|`. So every first derivative of the Green potential decays like `|x|⁻²`,
the gradient is bounded by `C (1 + |x|)⁻²` everywhere, and the velocity `∇^⊥φ` of a compactly
supported continuous source is square integrable. In two dimensions the single-charge bound
`|x|⁻¹` of `ExteriorGradient` is not square integrable at infinity.

## Main results

* `norm_inv_sq_smul_sub_inv_sq_smul`: `‖a/‖a‖² - b/‖b‖²‖ = ‖a - b‖ / (‖a‖ ‖b‖)` for nonzero
  vectors of a real inner product space.
* `abs_partialDeriv_halfSpaceGreenPotential_le_dipole`: for a continuous source vanishing outside
  the ball of radius `R`, each first derivative of the Green potential is at most
  `R ∫ |f| / (π (|x| - R)²)` at `|x| > R`.
* `exists_norm_gradient_halfSpaceGreenPotential_le`: the gradient of the Green potential of a
  compactly supported continuous source is at most `C (1 + |x|)⁻²` on the plane.
* `memLp_planarStreamVelocity_halfSpaceGreenPotential`: the velocity `∇^⊥φ` of such a source is
  square integrable on the plane.
-/

@[expose] public section

noncomputable section

namespace GreenFunction

open MeasureTheory Filter Set SobolevSpace
open scoped Gradient
open PDE (partialDeriv)

local notation "𝐑" => PDE.Common.coordinateReflection

/-- The inversion identity `‖a/‖a‖² - b/‖b‖²‖ = ‖a - b‖ / (‖a‖ ‖b‖)` for nonzero vectors of a
real inner product space. -/
theorem norm_inv_sq_smul_sub_inv_sq_smul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖(‖a‖ ^ 2)⁻¹ • a - (‖b‖ ^ 2)⁻¹ • b‖ = ‖a - b‖ / (‖a‖ * ‖b‖) := by
  have ha' : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have hb' : ‖b‖ ≠ 0 := norm_ne_zero_iff.2 hb
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity), div_pow, norm_sub_sq_real, norm_sub_sq_real,
    norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
  simp only [Real.norm_eq_abs, abs_inv, abs_pow, abs_norm]
  field_simp
  ring

/-- The difference of the planar gradient kernel at two nonzero points. -/
theorem norm_gradientKernelVector_sub {a b : ℝ^2} (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖PotentialTheory.Planar.gradientKernelVector a -
        PotentialTheory.Planar.gradientKernelVector b‖ =
      1 / (2 * Real.pi) * (‖a - b‖ / (‖a‖ * ‖b‖)) := by
  have hrewrite (z : ℝ^2) : PotentialTheory.Planar.gradientKernelVector z =
      -(1 / (2 * Real.pi)) • ((‖z‖ ^ 2)⁻¹ • z) := by
    rw [PotentialTheory.Planar.gradientKernelVector, smul_smul]
    congr 1
    field_simp
  rw [hrewrite, hrewrite, ← smul_sub, norm_smul, norm_inv_sq_smul_sub_inv_sq_smul ha hb,
    Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]

/-- **Dipole decay.** For a continuous source vanishing outside the ball of radius `R ≥ 0`, each
first derivative of the half-plane Green potential is at most
`R ∫_{ℝ²₊} |f| / (π (|x| - R)²)` at `|x| > R`. -/
theorem abs_partialDeriv_halfSpaceGreenPotential_le_dipole {f : ℝ^2 → ℝ} (hf : Continuous f)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ y, R < ‖y‖ → f y = 0) (j : Fin 2) {x : ℝ^2}
    (hx : R < ‖x‖) :
    ‖(∂[j] (halfSpaceGreenPotential f)) x‖ ≤
      R * (∫ y in {y : ℝ^2 | 0 < y 1}, ‖f y‖) / (Real.pi * (‖x‖ - R) ^ 2) := by
  have hc := hasCompactSupport_of_eq_zero_of_lt_norm hR
  have hd : 0 < ‖x‖ - R := sub_pos.2 hx
  set c : ℝ := R / (Real.pi * (‖x‖ - R) ^ 2) with hc_def
  have hc0 : 0 ≤ c := by positivity
  set F : ℝ^2 → ℝ := fun y ↦
    PotentialTheory.Planar.gradientKernel j (x - y) * oddHalfSpaceExtension f y with hF
  have hFi : Integrable F := integrable_gradientKernel_sub_mul_oddHalfSpaceExtension hf hc j x
  rw [partialDeriv_halfSpaceGreenPotential_eq_integral hf hc j x, ← setIntegral_univ]
  rw [setIntegral_eq_setIntegral_pos_add_reflect (1 : Fin 2) MeasurableSet.univ
    (fun _ ↦ by simp) hFi.integrableOn, univ_inter]
  have hpoint : ∀ y ∈ {y : ℝ^2 | 0 < y 1},
      ‖F y + F (𝐑 1 y)‖ ≤ ‖f y‖ * c := by
    intro y hy
    have hup : y ∈ HalfSpace.upper 2 := hy
    have hlow : 𝐑 1 y ∈ HalfSpace.lower 2 := by
      change (𝐑 1 y) 1 < 0
      simpa using hy
    have hFy : F y = PotentialTheory.Planar.gradientKernel j (x - y) * f y := by
      simp only [hF, oddHalfSpaceExtension_eqOn f hup]
    have hFr : F (𝐑 1 y) = -(PotentialTheory.Planar.gradientKernel j (x - 𝐑 1 y) * f y) := by
      have hnu : 𝐑 1 y ∉ HalfSpace.upper 2 := fun h ↦
        (show (0 : ℝ) < (𝐑 1 y) 1 from h).not_gt hlow
      have hrr : HalfSpace.reflect 2 (𝐑 1 y) = y := by
        rw [reflect_two_eq_coordinateReflection]
        exact PDE.Common.coordinateReflection_involutive 1 y
      simp only [hF, oddHalfSpaceExtension, Pi.sub_apply, indicator_of_notMem hnu,
        indicator_of_mem hlow, hrr, zero_sub, mul_neg]
    rw [hFy, hFr, ← sub_eq_add_neg, ← sub_mul, norm_mul, mul_comm]
    by_cases hyR : R < ‖y‖
    · rw [hR y hyR, norm_zero, zero_mul, zero_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hyR' : ‖y‖ ≤ R := le_of_not_gt hyR
    have hry : ‖𝐑 1 y‖ = ‖y‖ := by
      rw [← reflect_two_eq_coordinateReflection, HalfSpace.norm_reflect]
    have hxy : ‖x‖ - R ≤ ‖x - y‖ := by linarith [norm_sub_norm_le x y]
    have hxry : ‖x‖ - R ≤ ‖x - 𝐑 1 y‖ := by linarith [norm_sub_norm_le x (𝐑 1 y)]
    have ha : x - y ≠ 0 := norm_ne_zero_iff.1 (hd.trans_le hxy).ne'
    have hb : x - 𝐑 1 y ≠ 0 := norm_ne_zero_iff.1 (hd.trans_le hxry).ne'
    have hcomp : ‖PotentialTheory.Planar.gradientKernel j (x - y) -
          PotentialTheory.Planar.gradientKernel j (x - 𝐑 1 y)‖ ≤
        ‖PotentialTheory.Planar.gradientKernelVector (x - y) -
          PotentialTheory.Planar.gradientKernelVector (x - 𝐑 1 y)‖ := by
      rw [← PotentialTheory.Planar.gradientKernelVector_apply,
        ← PotentialTheory.Planar.gradientKernelVector_apply, ← PiLp.sub_apply]
      exact PiLp.norm_apply_le _ j
    refine hcomp.trans ?_
    rw [norm_gradientKernelVector_sub ha hb]
    have hdiff : ‖x - y - (x - 𝐑 1 y)‖ ≤ 2 * R := by
      rw [sub_sub_sub_cancel_left]
      linarith [norm_sub_le (𝐑 1 y) y]
    have hden : (‖x‖ - R) ^ 2 ≤ ‖x - y‖ * ‖x - 𝐑 1 y‖ := by
      rw [sq]
      exact mul_le_mul hxy hxry hd.le (hd.le.trans hxy)
    rw [hc_def]
    calc 1 / (2 * Real.pi) * (‖x - y - (x - 𝐑 1 y)‖ / (‖x - y‖ * ‖x - 𝐑 1 y‖))
        ≤ 1 / (2 * Real.pi) * (2 * R / (‖x‖ - R) ^ 2) := by
          gcongr
      _ = R / (Real.pi * (‖x‖ - R) ^ 2) := by field_simp
  have hfi : IntegrableOn (fun y ↦ ‖f y‖ * c) {y : ℝ^2 | 0 < y 1} :=
    ((hf.integrable_of_hasCompactSupport hc).norm.mul_const c).integrableOn
  calc ‖∫ y in {y : ℝ^2 | 0 < y 1}, (F y + F (𝐑 1 y))‖
      ≤ ∫ y in {y : ℝ^2 | 0 < y 1}, ‖F y + F (𝐑 1 y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y in {y : ℝ^2 | 0 < y 1}, ‖f y‖ * c := by
        refine setIntegral_mono_on ?_ hfi
          (measurableSet_lt measurable_const (EuclideanSpace.proj 1).continuous.measurable)
          hpoint
        exact ((hFi.add ((PDE.Common.measurePreserving_coordinateReflection
          1).integrable_comp_of_integrable hFi)).norm).integrableOn
    _ = R * (∫ y in {y : ℝ^2 | 0 < y 1}, ‖f y‖) / (Real.pi * (‖x‖ - R) ^ 2) := by
        rw [integral_mul_const, hc_def]
        ring

/-- The gradient of the Green potential of a compactly supported continuous source is bounded by
`C (1 + |x|)⁻²` on the whole plane. -/
theorem exists_norm_gradient_halfSpaceGreenPotential_le {f : ℝ^2 → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) :
    ∃ C, ∀ x : ℝ^2, ‖∇ (halfSpaceGreenPotential f) x‖ ≤ C * (1 + ‖x‖) ^ (-2 : ℝ) := by
  obtain ⟨R₁, hR₁⟩ : ∃ R, ∀ y : ℝ^2, R < ‖y‖ → f y = 0 := by
    obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
    exact ⟨R, fun y hy ↦ by_contra fun h ↦ hy.not_ge (by simpa using hR (subset_tsupport f h))⟩
  set R := max R₁ 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hR : ∀ y : ℝ^2, R < ‖y‖ → f y = 0 := fun y hy ↦ hR₁ y ((le_max_left _ _).trans_lt hy)
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hc
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  set mass := ∫ y in HalfSpace.upper 2, ‖f y‖
  have hmass : 0 ≤ mass := setIntegral_nonneg (HalfSpace.measurableSet_upper 2)
    fun _ _ ↦ norm_nonneg _
  set C₀ := M * 1 + mass / (Real.pi * 1)
  refine ⟨max (C₀ * (1 + 2 * R) ^ 2) (2 * 16 * R * mass / Real.pi), fun x ↦ ?_⟩
  have hpos : 0 < 1 + ‖x‖ := by positivity
  have hrp : (1 + ‖x‖) ^ (-2 : ℝ) = ((1 + ‖x‖) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hpos.le]
    norm_cast
  rw [hrp]
  by_cases hx : ‖x‖ < 2 * R
  · have hnear := norm_gradient_halfSpaceGreenPotential_le_mass hf hc hM0
      (fun y _ ↦ hM y) x (ρ := 1) one_pos
    have hsq : (1 + ‖x‖) ^ 2 ≤ (1 + 2 * R) ^ 2 := by gcongr
    calc ‖∇ (halfSpaceGreenPotential f) x‖ ≤ C₀ := hnear
      _ ≤ C₀ * (1 + 2 * R) ^ 2 * ((1 + ‖x‖) ^ 2)⁻¹ := by
          rw [mul_assoc]
          refine le_mul_of_one_le_right ((norm_nonneg _).trans hnear) ?_
          rw [← div_eq_mul_inv, one_le_div (by positivity)]
          exact hsq
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have hx' : 2 * R ≤ ‖x‖ := le_of_not_gt hx
    have hxR : R < ‖x‖ := by linarith
    have hd : (1 + ‖x‖) ^ 2 ≤ 16 * (‖x‖ - R) ^ 2 := by nlinarith
    have hpart (j : Fin 2) : ‖(∂[j] (halfSpaceGreenPotential f)) x‖ ≤
        16 * R * mass / Real.pi * ((1 + ‖x‖) ^ 2)⁻¹ := by
      have h := abs_partialDeriv_halfSpaceGreenPotential_le_dipole hf (by linarith) hR j hxR
      refine h.trans ?_
      change R * mass / _ ≤ _
      have hdpos : 0 < (‖x‖ - R) ^ 2 := by nlinarith
      rw [div_le_iff₀ (by positivity)]
      calc R * mass = 16 * R * mass / Real.pi * ((1 + ‖x‖) ^ 2)⁻¹ *
            (Real.pi * ((1 + ‖x‖) ^ 2 / 16)) := by field_simp
        _ ≤ 16 * R * mass / Real.pi * ((1 + ‖x‖) ^ 2)⁻¹ * (Real.pi * (‖x‖ - R) ^ 2) := by
          gcongr
          linarith
    have hsplit : ‖∇ (halfSpaceGreenPotential f) x‖ ≤
        ‖(∂[(0 : Fin 2)] (halfSpaceGreenPotential f)) x‖ +
          ‖(∂[(1 : Fin 2)] (halfSpaceGreenPotential f)) x‖ := by
      simpa only [Fin.sum_univ_two, PDE.gradient_apply_eq_partialDeriv] using
        PiLp.norm_le_sum_norm (∇ (halfSpaceGreenPotential f) x)
    calc ‖∇ (halfSpaceGreenPotential f) x‖
        ≤ 16 * R * mass / Real.pi * ((1 + ‖x‖) ^ 2)⁻¹ +
          16 * R * mass / Real.pi * ((1 + ‖x‖) ^ 2)⁻¹ :=
          hsplit.trans (add_le_add (hpart 0) (hpart 1))
      _ = 2 * 16 * R * mass / Real.pi * ((1 + ‖x‖) ^ 2)⁻¹ := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-- **Finite energy.** The velocity `∇^⊥φ` of the half-plane Green potential of a compactly
supported continuous source is square integrable on the plane. -/
theorem memLp_planarStreamVelocity_halfSpaceGreenPotential {f : ℝ^2 → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) :
    MemLp (IncompressibleFlow.planarStreamVelocity (halfSpaceGreenPotential f)) 2 := by
  obtain ⟨C, hC⟩ := exists_norm_gradient_halfSpaceGreenPotential_le hf hc
  have hcont : Continuous (IncompressibleFlow.planarStreamVelocity (halfSpaceGreenPotential f)) :=
    (IncompressibleFlow.contDiff_planarStreamVelocity (m := 0) _
      (by simpa using contDiff_one_halfSpaceGreenPotential hf hc)).continuous
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  have hint : Integrable (fun x : ℝ^2 ↦ (1 + ‖x‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by simp; norm_num)
  refine (hint.const_mul (C ^ 2)).mono' (by fun_prop) (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), IncompressibleFlow.norm_planarStreamVelocity]
  have hpos : 0 < 1 + ‖x‖ := by positivity
  have h4 : (1 + ‖x‖) ^ (-(4 : ℝ)) = ((1 + ‖x‖) ^ (-(2 : ℝ))) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    norm_num
  rw [h4, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2

end GreenFunction
