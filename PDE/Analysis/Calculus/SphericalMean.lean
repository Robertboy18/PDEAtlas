/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.EuclideanBall
public import PDE.FDeriv.Operators
import PDE.Analysis.Calculus.CompactParametricIntegral
import PDE.Analysis.MeasureTheory.SphereSymmetry
import CAS.ExactTactic

/-!
# Calculus of spherical means

The radial calculus of the spherical mean `unitSphereAverage`.  For

`M(r) = |S^{n-1}|⁻¹ ∫_{S^{n-1}} u(x + rω) dω`,

we prove evenness in `r`, differentiation under the angular integral, and
the radial Laplacian identity

`M''(r) + (n - 1) M'(r) / r = average_{S^{n-1}} Δu(x + rω)`

for `r > 0`.  The proof of the last formula uses Gauss's theorem on a ball:
`r^(n-1) |S^{n-1}| M'(r)` is the integral of `Δu` over `B(x,r)`.

The fixed-sphere average is defined for every signed radius.  It is even, and
at `r = 0` it equals `u x` in positive dimension.  The displayed differential
equation is stated only for `r > 0`; its coefficient is singular at zero.

These are the computations in Evans's proofs of the mean-value formulas (§2.2.2, Theorem 2,
step 1) and of the Euler–Poisson–Darboux equation (§2.4.1(b), Lemma 1):
`unitSphereAverage_radial_flux` is his (15), and `radialLaplacian_unitSphereAverage'`, with
his coefficient `(n - 1)/r`, is the radial identity of step 2 with `Δu` in place of `u_tt`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.2.2, step 1 of the proof of Theorem 2, pp. 25-26,
  and §2.4.1(b), Lemma 1 (the Euler–Poisson–Darboux equation) and its proof, (14)-(16),
  pp. 70-71. <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace PDE.Analysis

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

variable {n : ℕ}

/-- The fixed-sphere average is unchanged when the signed radius is negated.

This is the change of variables `ω ↦ -ω`, using invariance of Mathlib's
angular measure under linear isometries. -/
theorem unitSphereAverage_neg_radius
    (u : ℝ^n → ℝ) (x : ℝ^n) (r : ℝ) :
    unitSphereAverage n u x (-r) = unitSphereAverage n u x r := by
  classical
  let e : ℝ^n ≃ₗᵢ[ℝ] ℝ^n :=
    LinearIsometryEquiv.neg ℝ
  have hpres := e.measurePreserving_toSphere
  have hchange :=
    hpres.integral_comp'
      (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
        u (x + r • (ω : ℝ^n)))
  unfold unitSphereAverage
  congr 1
  simpa [e, sphereLinearIsometryEquiv] using hchange

/-- In positive dimension, the fixed-sphere average at radius zero is the
value at the center. -/
@[simp]
theorem unitSphereAverage_zero
    [Fact (0 < n)] (u : ℝ^n → ℝ) (x : ℝ^n) :
    unitSphereAverage n u x 0 = u x := by
  have harea : unitSphereArea n ≠ 0 :=
    ne_of_gt unitSphereArea_pos
  unfold unitSphereAverage
  simp only [zero_smul, add_zero, integral_const, smul_eq_mul]
  change unitSphereArea n * u x / unitSphereArea n = u x
  field_simp

/-- Along an affine ray, the radial derivative is the differential applied to its direction. -/
private theorem hasDerivAt_radial_integrand
    {u : ℝ^n → ℝ} (x v : ℝ^n) (r : ℝ)
    (hu : DifferentiableAt ℝ u (x + r • v)) :
    HasDerivAt (fun s : ℝ ↦ u (x + s • v)) (fderiv ℝ u (x + r • v) v) r := by
  have hpath : HasDerivAt (fun s : ℝ ↦ x + s • v) v r := by
    simpa using ((hasDerivAt_id r).smul_const v).const_add x
  exact hu.hasFDerivAt.comp_hasDerivAt r hpath

/-- The radial derivatives vary continuously in both the signed radius and the direction.
This gives compact domination on each bounded radius interval. -/
private theorem continuous_radial_integrand_deriv
    {u : ℝ^n → ℝ} (x : ℝ^n) (hu : ContDiff ℝ 1 u) :
    Continuous (fun p : ℝ × Metric.sphere (0 : ℝ^n) 1 ↦
      fderiv ℝ u (x + p.1 • (p.2 : ℝ^n)) (p.2 : ℝ^n)) := by
  have hp : Continuous (fun p : ℝ × Metric.sphere (0 : ℝ^n) 1 ↦
      (x + p.1 • (p.2 : ℝ^n), (p.2 : ℝ^n))) := by fun_prop
  exact (hu.continuous_fderiv_apply one_ne_zero).comp hp

/-- Radial differentiation formula for the normalized fixed-sphere average
of a globally `C¹` function.

A compact radius interval and the unit sphere give a uniform bound on the
derivative, so no global bound on the gradient is required. -/
theorem hasDerivAt_unitSphereAverage
    (u : ℝ^n → ℝ) (x : ℝ^n) (r : ℝ)
    (hu : ContDiff ℝ 1 u) :
    HasDerivAt (unitSphereAverage n u x)
      ((∫ ω,
          fderiv ℝ u (x + r • (ω : ℝ^n)) (ω : ℝ^n)
          ∂((volume : Measure (ℝ^n)).toSphere)) /
        unitSphereArea n) r := by
  let μ : Measure (Metric.sphere (0 : ℝ^n) 1) := (volume : Measure (ℝ^n)).toSphere
  let D : ℝ → Metric.sphere (0 : ℝ^n) 1 → ℝ →L[ℝ] ℝ := fun s ω ↦
    (1 : ℝ →L[ℝ] ℝ).smulRight (fderiv ℝ u (x + s • (ω : ℝ^n)) (ω : ℝ^n))
  have hF : Continuous (fun p : ℝ × Metric.sphere (0 : ℝ^n) 1 ↦ u (x + p.1 • (p.2 : ℝ^n))) :=
    hu.continuous.comp (by fun_prop)
  have hD : Continuous D.uncurry :=
    (ContinuousLinearMap.smulRightL ℝ ℝ ℝ 1).continuous.comp
      (continuous_radial_integrand_deriv x hu)
  have hd (s : ℝ) (ω : Metric.sphere (0 : ℝ^n) 1) :
      HasFDerivAt (fun t ↦ u (x + t • (ω : ℝ^n))) (D s ω) s :=
    (hasDerivAt_radial_integrand x (ω : ℝ^n) s
      (hu.differentiable one_ne_zero).differentiableAt).hasFDerivAt
  -- Compactness gives the integrable bound for differentiation under the angular integral.
  have hi := hasFDerivAt_integral_of_compact (μ := μ) hF hD hd r
  have hDi : Integrable (D r) μ := by
    have hc : Continuous (D r) := hD.comp (continuous_const.prodMk continuous_id)
    simpa only [integrableOn_univ] using
      hc.continuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ
  have hderiv := hi.hasDerivAt.div_const (unitSphereArea n)
  rw [ContinuousLinearMap.integral_apply hDi] at hderiv
  rw [show unitSphereAverage n u x = fun s ↦ (∫ ω : Metric.sphere (0 : ℝ^n) 1,
      u (x + s • (ω : ℝ^n)) ∂((volume : Measure (ℝ^n)).toSphere)) / unitSphereArea n by rfl]
  simpa [D, μ] using hderiv

/-- The first radial derivative of a `C¹` spherical mean vanishes at the
center.  This is the differential consequence of the signed-radius
evenness convention. -/
theorem deriv_unitSphereAverage_zero
    (u : ℝ^n → ℝ) (x : ℝ^n) (hu : ContDiff ℝ 1 u) :
    deriv (unitSphereAverage n u x) 0 = 0 := by
  have hM := (hasDerivAt_unitSphereAverage u x 0 hu).differentiableAt.hasDerivAt
  have hcomp := HasDerivAt.comp (0 : ℝ) (h₂ := unitSphereAverage n u x)
    (by simpa only [neg_zero] using hM) (hasDerivAt_neg 0)
  simp only [Function.comp_def, unitSphereAverage_neg_radius] at hcomp
  linarith [hcomp.unique hM]

/-- The derivative of a spherical mean is the normalized outward flux.  Gauss's
formula therefore identifies `r^(n-1) |S^{n-1}| M'(r)` with the ball integral
of the Laplacian. -/
theorem unitSphereAverage_radial_flux
    [Fact (0 < n)] (u : ℝ^n → ℝ) (x : ℝ^n)
    {r : ℝ} (hr : 0 < r) (hu : ContDiff ℝ 2 u) :
    r ^ (n - 1) * unitSphereArea n *
        deriv (unitSphereAverage n u x) r =
      ballIntegral n (laplacian u) x r := by
  have hGauss : ballIntegral n (laplacian u) x r =
      sphereIntegral n (fun y ↦ ∑ i : Fin n, (∂[i] u) y * (NormedSpace.normalize (y - x)) i) x r :=
    ballIntegral_divergence_eq_sphereIntegral_normal_flux (fun i y ↦ (∂[i] u) y)
      (fun i ↦ contDiff_partialDeriv_of_succ (m := 1) (i := i) hu) x hr
  have hboundary :
      sphereIntegral n (fun y ↦ ∑ i : Fin n, (∂[i] u) y * (NormedSpace.normalize (y - x)) i) x r =
        r ^ (n - 1) * ∫ ω, fderiv ℝ u (x + r • (ω : ℝ^n)) (ω : ℝ^n)
          ∂((volume : Measure (ℝ^n)).toSphere) := by
    unfold sphereIntegral
    rw [abs_of_pos hr]
    refine congrArg _ (integral_congr_ae (.of_forall fun ω ↦ ?_))
    have hω : ‖(ω : ℝ^n)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
    have hnormal : NormedSpace.normalize ((x + r • (ω : ℝ^n)) - x) = (ω : ℝ^n) := by
      ext i
      simp [NormedSpace.normalize, norm_smul, hω, abs_of_pos hr, hr.ne']
    simp only [hnormal]
    exact (fderiv_apply_eq_sum_partialDeriv_mul u (x + r • (ω : ℝ^n)) (ω : ℝ^n)).symm
  rw [(hasDerivAt_unitSphereAverage u x r (hu.of_le (by norm_num))).deriv, hGauss, hboundary]
  field_simp [unitSphereArea_pos.ne']

/-- Radial Laplacian formula for fixed-sphere averages.

The coefficient uses the natural number `n - 1`, cast to `ℝ`; in positive
dimension this is equal to `(n : ℝ) - 1`.  The formula is intentionally
restricted to `r > 0`, since the quotient by `r` has no pointwise meaning at
the origin. -/
theorem radialLaplacian_unitSphereAverage
    [Fact (0 < n)] (u : ℝ^n → ℝ) (x : ℝ^n)
    {r : ℝ} (hr : 0 < r) (hu : ContDiff ℝ 2 u) :
    deriv (deriv (unitSphereAverage n u x)) r +
        (((n - 1 : ℕ) : ℝ) / r) *
          deriv (unitSphereAverage n u x) r =
      unitSphereAverage n (laplacian u) x r := by
  have hsphere : sphereIntegral n (laplacian u) x r =
      r ^ (n - 1) * unitSphereArea n * unitSphereAverage n (laplacian u) x r := by
    unfold sphereIntegral unitSphereAverage
    rw [abs_of_pos hr]
    field_simp [unitSphereArea_pos.ne']
  set M : ℝ → ℝ := unitSphereAverage n u x
  set B : ℝ → ℝ := ballIntegral n (laplacian u) x
  set A : ℝ := unitSphereArea n
  have hrA : r ^ (n - 1) * A ≠ 0 := mul_ne_zero (pow_ne_zero _ hr.ne') unitSphereArea_pos.ne'
  have hlap : Continuous (laplacian u) := continuous_finsetSum _ fun i _ ↦
    (contDiff_partialDeriv_of_succ (m := 0) (i := i)
      (contDiff_partialDeriv_of_succ (m := 1) (i := i) hu)).continuous
  have hB : HasDerivAt B (sphereIntegral n (laplacian u) x r) r :=
    hasDerivAt_ballIntegral_radius (laplacian u) hlap x hr
  -- the flux identity `s^(n-1) |S^{n-1}| M'(s) = B(s)` holds near `r`
  have hflux : ∀ᶠ s in nhds r, B s = s ^ (n - 1) * A * deriv M s := by
    filter_upwards [Ioi_mem_nhds hr] with s hs using (unitSphereAverage_radial_flux u x hs hu).symm
  have hp : HasDerivAt (fun s : ℝ ↦ s ^ (n - 1) * A)
      (((n - 1 : ℕ) : ℝ) * r ^ (n - 1 - 1) * A) r := by
    cas
  -- `M' = B / (s^(n-1) |S^{n-1}|)` near `r`, so `M'` is differentiable at `r`
  have hM' : HasDerivAt (deriv M) (deriv (deriv M) r) r := by
    refine ((hB.div hp hrA).congr_of_eventuallyEq ?_).differentiableAt.hasDerivAt
    filter_upwards [hflux, Ioi_mem_nhds hr] with s hs hs0
    rw [Pi.div_apply, hs,
      mul_div_cancel_left₀ _ (mul_ne_zero (pow_ne_zero _ hs0.ne') unitSphereArea_pos.ne')]
  have hderiv := ((hp.mul hM').congr_of_eventuallyEq hflux).unique hB
  have hpower : r ^ (n - 1) * (((n - 1 : ℕ) : ℝ) / r) = ((n - 1 : ℕ) : ℝ) * r ^ (n - 1 - 1) := by
    cases n - 1 with
    | zero => simp
    | succ k => rw [Nat.add_sub_cancel, pow_succ]; field_simp
  refine mul_left_cancel₀ hrA ?_
  rw [← hsphere, ← hderiv]
  linear_combination (A * deriv M r) * hpower

/-- The same radial Laplacian identity with Evans's coefficient `(n - 1)/r`. -/
theorem radialLaplacian_unitSphereAverage'
    [Fact (0 < n)] (u : ℝ^n → ℝ) (x : ℝ^n)
    {r : ℝ} (hr : 0 < r) (hu : ContDiff ℝ 2 u) :
    deriv (deriv (unitSphereAverage n u x)) r +
        (((n : ℝ) - 1) / r) *
          deriv (unitSphereAverage n u x) r =
      unitSphereAverage n (laplacian u) x r := by
  have hn : 1 ≤ n :=
    Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt Fact.out)
  simpa [Nat.cast_sub hn] using
    radialLaplacian_unitSphereAverage
      (n := n) u x hr hu

end PDE.Analysis
