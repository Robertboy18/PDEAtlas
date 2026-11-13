/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Fourier.HilbertTransform.RealPair.PrincipalValue
public import PDE.Spaces.Sobolev.Inequalities.Morrey.FiniteExponent.OneDimensional.UniformBound

/-!
# Classical Sobolev bounds for real Hilbert pairs

For compact `C²` input, derivative commutation and spectral isometry bound a
continuous Hilbert representative by the input's `L²` and derivative `L²` norms.
The output need not have compact support. A normalized primitive also satisfies
a square-integral bound by the one-dimensional Morrey estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal NNReal

namespace PDE.Analysis

variable {omega v : ℝ → ℝ}

/-- Compact `C²` vorticity gives a pointwise global bound for its Hilbert
principal value solely in terms of input `L²` norms. -/
theorem norm_hilbertPV_le_eLpNorm_add_deriv
    (homega : ContDiff ℝ 2 omega) (hsupp : HasCompactSupport omega) (x : ℝ) :
    ‖hilbertPV omega x‖ ≤
      (eLpNorm omega 2 volume).toReal + (eLpNorm (deriv omega) 2 volume).toReal := by
  have hC1 : ContDiff ℝ 1 omega := homega.of_le (by norm_num)
  have hpair := IsHilbertPair.of_contDiff_one_compactSupport hC1 hsupp
  have hpair' :=
    IsHilbertPair.of_contDiff_one_compactSupport homega.deriv' hsupp.deriv
  have hcommute := deriv_hilbertPV_of_contDiff_two_compactSupport homega hsupp
  have hderiv : MemLp (deriv (hilbertPV omega)) 2 volume := by
    rw [hcommute]
    exact hpair'.memLp_right
  have hbound := SobolevSpace.norm_apply_le_eLpNorm_toReal_add_deriv
    (contDiff_hilbertPV_of_contDiff_succ_compactSupport 1 homega hsupp)
    (by norm_num : (1 : ℝ≥0∞) < 2) hpair.memLp_right hderiv x
  rwa [hcommute, hpair.eLpNorm_eq, hpair'.eLpNorm_eq] at hbound

/-- Any continuous representative in a spectral Hilbert pair inherits
the global bound from compact `C²` vorticity. -/
theorem IsHilbertPair.norm_le_eLpNorm_add_deriv (h : IsHilbertPair omega v)
    (hv : Continuous v) (homega : ContDiff ℝ 2 omega)
    (hsupp : HasCompactSupport omega) (x : ℝ) :
    ‖v x‖ ≤
      (eLpNorm omega 2 volume).toReal + (eLpNorm (deriv omega) 2 volume).toReal := by
  rw [h.eq_hilbertPV hv (homega.of_le (by norm_num)) hsupp]
  exact norm_hilbertPV_le_eLpNorm_add_deriv homega hsupp x

/-- A `C¹` velocity satisfying the concrete Biot–Savart relation has bounded
spatial derivative, with the bound computed from the vorticity. -/
theorem IsHilbertPair.nnnorm_deriv_le_eLpNorm_add_deriv {u : ℝ → ℝ}
    (h : IsHilbertPair omega (deriv u)) (hu : ContDiff ℝ 1 u)
    (homega : ContDiff ℝ 2 omega) (hsupp : HasCompactSupport omega) (x : ℝ) :
    ‖deriv u x‖₊ ≤
      (eLpNorm omega 2 volume).toNNReal + (eLpNorm (deriv omega) 2 volume).toNNReal := by
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_add, ENNReal.coe_toNNReal_eq_toReal, coe_nnnorm] using
    h.norm_le_eLpNorm_add_deriv (hu.continuous_deriv le_rfl) homega hsupp x

/-- Input `H¹` norms give a global Lipschitz constant for every `C¹` velocity
satisfying the concrete Hilbert relation. -/
theorem IsHilbertPair.lipschitzWith_of_contDiff_two_compactSupport {u : ℝ → ℝ}
    (h : IsHilbertPair omega (deriv u)) (hu : ContDiff ℝ 1 u)
    (homega : ContDiff ℝ 2 omega) (hsupp : HasCompactSupport omega) :
    LipschitzWith
      ((eLpNorm omega 2 volume).toNNReal + (eLpNorm (deriv omega) 2 volume).toNNReal) u :=
  lipschitzWith_of_nnnorm_deriv_le (hu.differentiable (by norm_num))
    (h.nnnorm_deriv_le_eLpNorm_add_deriv hu homega hsupp)

/-- The normalized velocity constructed by the integral primitive has
the global Lipschitz bound dictated by the input `H¹` norms. -/
theorem lipschitzWith_hilbertPVVelocity_of_contDiff_two_compactSupport
    (homega : ContDiff ℝ 2 omega) (hsupp : HasCompactSupport omega) :
    LipschitzWith
      ((eLpNorm omega 2 volume).toNNReal + (eLpNorm (deriv omega) 2 volume).toNNReal)
      (hilbertPVVelocity omega) := by
  have hC1 : ContDiff ℝ 1 omega := homega.of_le (by norm_num)
  have hu : ContDiff ℝ 1 (hilbertPVVelocity omega) := by
    obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsupp hC1 (by norm_num)
    exact contDiff_one_hilbertPVVelocity_of_lipschitzWith_compactSupport hK hsupp
  exact IsHilbertPair.lipschitzWith_of_contDiff_two_compactSupport
    (isHilbertPair_deriv_hilbertPVVelocity hC1 hsupp) hu homega hsupp

/-- Normalization at zero, the one-dimensional Morrey estimate, and Hilbert
isometry control a velocity by the vorticity's square integral. -/
theorem IsHilbertPair.sq_le_abs_mul_integral_sq {f u : ℝ → ℝ}
    (h : IsHilbertPair f (deriv u)) (hu : ContDiff ℝ 1 u) (hzero : u 0 = 0) (x : ℝ) :
    u x ^ 2 ≤ |x| * ∫ y, f y ^ 2 := by
  have hbound := SobolevSpace.norm_sub_le_eLpNorm_deriv_toReal_mul_rpow
    u hu (by norm_num : (1 : ℝ≥0∞) < 2) h.memLp_right.eLpNorm_ne_top 0 x
  simp only [hzero, sub_zero] at hbound
  norm_num [SobolevSpace.morreyExponent] at hbound
  rw [← Real.sqrt_eq_rpow] at hbound
  have hsq := (sq_le_sq₀ (abs_nonneg (u x))
    (mul_nonneg ENNReal.toReal_nonneg (Real.sqrt_nonneg |x|))).mpr hbound
  rw [sq_abs, mul_pow, Real.sq_sqrt (abs_nonneg x),
    ← integral_sq_eq_eLpNorm_toReal_sq h.memLp_right, h.integral_sq_eq] at hsq
  simpa only [mul_comm] using hsq

/-- The normalized velocity of a concrete Hilbert pair controls the boundary
rate by the L² norm of its vorticity. -/
theorem IsHilbertPair.abs_boundary_normalization_le_L2
    {q v : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hpair : IsHilbertPair q (deriv v)) (hv : ContDiff ℝ 1 v) (hzero : v 0 = 0) :
    |-v L / L| ≤ (√L / L) * ‖hpair.memLp_left.toLp q‖ := by
  have hsq := hpair.sq_le_abs_mul_integral_sq hv hzero L
  rw [abs_of_pos hL, integral_sq_eq_eLpNorm_toReal_sq hpair.memLp_left,
    ← Lp.norm_toLp q hpair.memLp_left] at hsq
  have habs : |v L| ≤ √L * ‖hpair.memLp_left.toLp q‖ := by
    apply (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [sq_abs, mul_pow, Real.sq_sqrt hL.le] using hsq
  calc
    |-v L / L| = |v L| / L := by rw [abs_div, abs_neg, abs_of_pos hL]
    _ ≤ (√L * ‖hpair.memLp_left.toLp q‖) / L :=
      div_le_div_of_nonneg_right habs hL.le
    _ = (√L / L) * ‖hpair.memLp_left.toLp q‖ := by
      rw [div_mul_eq_mul_div]

/-- Differentiating a Hilbert pair with `C²` compactly supported vorticity and continuous
velocity gives the Hilbert pair of the derivatives. -/
theorem IsHilbertPair.deriv_of_contDiff_two {f h : ℝ → ℝ}
    (hpair : IsHilbertPair f h) (hh : Continuous h)
    (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f) :
    IsHilbertPair (deriv f) (deriv h) := by
  rw [hpair.eq_hilbertPV hh (hf.of_le (by norm_num)) hsupp,
    deriv_hilbertPV_of_contDiff_two_compactSupport hf hsupp]
  exact IsHilbertPair.of_contDiff_one_compactSupport hf.deriv' hsupp.deriv

end PDE.Analysis
