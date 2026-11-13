/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import CAS.ExactTactic

/-!
# The angularly reduced Newtonian denominator

The squared distance between radial-axial coordinates is
`q = r² + s² - 2rs cos θ + (z - ζ)²`. For nonnegative radii it dominates
the squared planar distance. Thus distinct planar points give a positive
denominator uniformly in the angle.

Differentiating `P q⁻ᵃ` produces `q P' - a P q'` over `qᵃ⁺¹`.
The exponent is arbitrary, so the calculus applies to Newtonian kernels
in any dimension. No angular integration formula is assumed here.
-/

@[expose] public noncomputable section

namespace PotentialTheory.Axisymmetric

/-- Squared distance in radial-axial coordinates with relative angle `θ`. -/
def reducedKernelQ (r z s ζ θ : ℝ) : ℝ :=
  r ^ 2 + s ^ 2 - 2 * r * s * Real.cos θ + (z - ζ) ^ 2

/-- The radial derivative of the squared distance. -/
theorem reducedKernelQ_deriv_r (r z s ζ θ : ℝ) :
    deriv (fun ρ : ℝ ↦ reducedKernelQ ρ z s ζ θ) r =
      2 * (r - s * Real.cos θ) := by
  cas

/-- The axial derivative of the squared distance. -/
theorem reducedKernelQ_deriv_z (r z s ζ θ : ℝ) :
    deriv (fun ξ : ℝ ↦ reducedKernelQ r ξ s ζ θ) z = 2 * (z - ζ) := by
  cas

/-- The second radial derivative of the squared distance is constant. -/
theorem reducedKernelQ_secondDeriv_rr (r z s ζ θ : ℝ) :
    deriv (deriv (fun ρ : ℝ ↦ reducedKernelQ ρ z s ζ θ)) r = 2 := by
  cas

/-- The second axial derivative of the squared distance is constant. -/
theorem reducedKernelQ_secondDeriv_zz (r z s ζ θ : ℝ) :
    deriv (deriv (fun ξ : ℝ ↦ reducedKernelQ r ξ s ζ θ)) z = 2 := by
  cas

/-- Radial and axial variables do not interact in the squared distance. -/
theorem reducedKernelQ_secondDeriv_rz (r z s ζ θ : ℝ) :
    deriv (fun ξ : ℝ ↦ deriv (fun ρ : ℝ ↦ reducedKernelQ ρ ξ s ζ θ) r) z = 0 := by
  cas

/-- Decomposition into planar distance and angular correction. -/
theorem reducedKernelQ_eq_planar_add_angular (r z s ζ θ : ℝ) :
    reducedKernelQ r z s ζ θ =
      (r - s) ^ 2 + (z - ζ) ^ 2 + 2 * r * s * (1 - Real.cos θ) := by
  cas

/-- For nonnegative radii the angular correction can only increase the distance. -/
theorem planarDistanceSq_le_reducedKernelQ
    (r z s ζ θ : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (r - s) ^ 2 + (z - ζ) ^ 2 ≤ reducedKernelQ r z s ζ θ := by
  rw [reducedKernelQ_eq_planar_add_angular]
  exact le_add_of_nonneg_right
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hr) hs)
      (sub_nonneg.mpr (Real.cos_le_one θ)))

/-- Distinct points in the closed radial half-plane give a positive denominator
at every angle, including when one point lies on the axis. -/
theorem reducedKernelQ_pos_of_ne
    (r z s ζ θ : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hne : (r, z) ≠ (s, ζ)) :
    0 < reducedKernelQ r z s ζ θ := by
  have hd : 0 < (r - s) ^ 2 + (z - ζ) ^ 2 := by
    by_contra! h
    have hrs : r = s := by nlinarith [sq_nonneg (z - ζ), sq_nonneg (r - s)]
    have hzζ : z = ζ := by nlinarith [sq_nonneg (z - ζ), sq_nonneg (r - s)]
    exact hne (Prod.ext hrs hzζ)
  exact hd.trans_le (planarDistanceSq_le_reducedKernelQ r z s ζ θ hr hs)

/-- Any positive lower bound on the planar squared distance gives a uniform
upper bound for every nonpositive power of the reduced denominator. -/
theorem reducedKernelQ_neg_rpow_le
    (r z s ζ θ a d : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hd : 0 < d) (hsep : d ≤ (r - s) ^ 2 + (z - ζ) ^ 2) :
    reducedKernelQ r z s ζ θ ^ (-a) ≤ d ^ (-a) :=
  Real.rpow_le_rpow_of_nonpos hd
    (hsep.trans (planarDistanceSq_le_reducedKernelQ r z s ζ θ hr hs)) (neg_nonpos.mpr ha)

/-- Differentiating a numerator times a negative real power preserves the
factorized kernel form. Only local differentiability and positivity are needed. -/
theorem reducedKernelPower_deriv
    (P q : ℝ → ℝ) (a x : ℝ)
    (hP : DifferentiableAt ℝ P x) (hq : DifferentiableAt ℝ q x)
    (hqx : 0 < q x) :
    deriv (fun y : ℝ ↦ P y * q y ^ (-a)) x =
      (q x * deriv P x - a * P x * deriv q x) * q x ^ (-a - 1) := by
  have hpow := hq.hasDerivAt.rpow_const (p := -a) (Or.inl hqx.ne')
  have hproduct := hP.hasDerivAt.mul hpow
  have hfactor : q x ^ (-a) = q x * q x ^ (-a - 1) := by
    calc
      q x ^ (-a) = q x ^ ((1 : ℝ) + (-a - 1)) := by congr 1; ring
      _ = q x ^ (1 : ℝ) * q x ^ (-a - 1) := Real.rpow_add hqx 1 (-a - 1)
      _ = q x * q x ^ (-a - 1) := by rw [Real.rpow_one]
  have hderiv :
      deriv (fun y : ℝ ↦ P y * q y ^ (-a)) x =
        deriv P x * q x ^ (-a) +
          P x * (deriv q x * -a * q x ^ (-a - 1)) := by
    change deriv (P * fun y ↦ q y ^ (-a)) x = _
    exact hproduct.deriv
  rw [hderiv, hfactor]
  ring

/-- Each differentiation raises the denominator exponent by one, starting
from an arbitrary base exponent. -/
theorem reducedKernelRecursion_step
    (P q : ℝ → ℝ) (a : ℝ) (m : ℕ) (x : ℝ)
    (hP : DifferentiableAt ℝ P x) (hq : DifferentiableAt ℝ q x)
    (hqx : 0 < q x) :
    deriv (fun y : ℝ ↦ P y * q y ^ (-(a + (m : ℝ)))) x =
      (q x * deriv P x - (a + (m : ℝ)) * P x * deriv q x) *
        q x ^ (-(a + ((m + 1 : ℕ) : ℝ))) := by
  convert reducedKernelPower_deriv P q (a + (m : ℝ)) x hP hq hqx using 1
  congr 2
  push_cast
  ring

end PotentialTheory.Axisymmetric
