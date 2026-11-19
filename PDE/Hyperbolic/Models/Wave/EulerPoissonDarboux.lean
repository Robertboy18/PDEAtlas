/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SphericalMean
public import PDE.Hyperbolic.Models.Wave.Calculus.SpaceTime
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The Euler-Poisson-Darboux equation for wave-equation spherical means

For a spacetime field `u(t, x)`, `waveSphericalMean u x t r` is the normalized
average of `u(t, ·)` on the sphere with center `x` and signed radius `r`. If
`u` is a classical solution of the wave equation, its mean satisfies

`Mₜₜ = Mᵣᵣ + (n - 1) Mᵣ / r`

for `r > 0`. This is the Euler–Poisson–Darboux equation (14) of Evans, §2.4.1(b), Lemma 1. At
the center, the signed-radius convention gives `M(t, 0) = u(t, x)` and `Mᵣ(t, 0) = 0`.

The proof uses the spherical-mean calculus of
`PDE.Analysis.Calculus.SphericalMean`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1(b), Lemma 1, equation (14).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

noncomputable section

namespace WaveEquation

open Filter MeasureTheory Set
open PDE.Analysis PDE.Common

variable {n : ℕ}

/-- The spatial spherical mean of a spacetime field at fixed time.  The radius
is signed; consequently this function is even in `r`. -/
noncomputable def waveSphericalMean
    (u : ℝ^(n + 1) → ℝ) (x : ℝ^n) (t r : ℝ) : ℝ :=
  unitSphereAverage n (fun y ↦ u (timeSpaceCons t y)) x r

/-- Spherical means are even in the signed radius. -/
@[simp]
theorem waveSphericalMean_neg_radius (u : ℝ^(n + 1) → ℝ) (x : ℝ^n) (t r : ℝ) :
    waveSphericalMean u x t (-r) = waveSphericalMean u x t r :=
  unitSphereAverage_neg_radius _ _ _

/-- In positive spatial dimension, the mean at radius zero is the value at
the center. -/
@[simp]
theorem waveSphericalMean_zero [Fact (0 < n)] (u : ℝ^(n + 1) → ℝ) (x : ℝ^n) (t : ℝ) :
    waveSphericalMean u x t 0 = u (timeSpaceCons t x) := by
  simp [waveSphericalMean]

/-- Differentiate a wave spherical mean in time.

The angular domain is compact.  A continuous time derivative is therefore
uniformly bounded on a compact time-space cylinder, which supplies the
dominating function for differentiation under the integral. -/
theorem hasDerivAt_waveSphericalMean_time (u : ℝ^(n + 1) → ℝ) (x : ℝ^n) (t r : ℝ)
    (hu : ContDiff ℝ 1 u) :
    HasDerivAt (fun s ↦ waveSphericalMean u x s r)
      (unitSphereAverage n (fun y ↦ (∂[0] u) (timeSpaceCons t y)) x r) t := by
  classical
  let μ : Measure (Metric.sphere (0 : ℝ^n) 1) := (volume : Measure (ℝ^n)).toSphere
  let I : Set ℝ := Ioo (t - 1) (t + 1)
  let F : ℝ → Metric.sphere (0 : ℝ^n) 1 → ℝ := fun s ω ↦ u (timeSpaceCons s (x + r • (ω : ℝ^n)))
  let F' : ℝ → Metric.sphere (0 : ℝ^n) 1 → ℝ := fun s ω ↦ (∂[0] u)
        (timeSpaceCons s (x + r • (ω : ℝ^n)))
  have hu' : Continuous (∂[0] u) := (PDE.contDiff_partialDeriv_of_succ
      (m := 0) (i := (0 : Fin (n + 1))) hu).continuous
  obtain ⟨C, hC_nonneg, hC⟩ := exists_norm_le_on_timeSpaceCylinder
      (∂[0] u) hu' (t - 1) (t + 1) x |r|
  have hspatial (ω : Metric.sphere (0 : ℝ^n) 1) :
      x + r • (ω : ℝ^n) ∈ Metric.closedBall x |r| := by
    have hω : ‖(ω : ℝ^n)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
    rw [Metric.mem_closedBall]
    simp [dist_eq_norm, norm_smul, hω]
  have hpath_cont (s : ℝ) : Continuous (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦
          timeSpaceCons s (x + r • (ω : ℝ^n))) := by
    have hrconst : Continuous (fun _ω : Metric.sphere (0 : ℝ^n) 1 ↦ r) := continuous_const
    have hval : Continuous (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦ (ω : ℝ^n)) := continuous_subtype_val
    have hscale : Continuous (fun ω : Metric.sphere (0 : ℝ^n) 1 ↦ r • (ω : ℝ^n)) :=
      hrconst.smul hval
    apply (contDiff_timeSpaceCons_spatial n s (m := 1)).continuous.comp
    exact continuous_const.add hscale
  have hF_cont (s : ℝ) : Continuous (F s) := hu.continuous.comp (hpath_cont s)
  have hF'_cont (s : ℝ) : Continuous (F' s) := hu'.comp (hpath_cont s)
  have hcompactSupport (f : Metric.sphere (0 : ℝ^n) 1 → ℝ) :
      HasCompactSupport f := by
    exact isCompact_univ.of_isClosed_subset isClosed_closure (fun _ _ ↦ Set.mem_univ _)
  have hI : I ∈ nhds t := by
    apply Ioo_mem_nhds <;> linarith
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F')
      (bound := fun _ : Metric.sphere (0 : ℝ^n) 1 ↦ C) hI (Filter.Eventually.of_forall fun s ↦
        (hF_cont s).aestronglyMeasurable) ((hF_cont t).integrable_of_hasCompactSupport
        (hcompactSupport _)) (hF'_cont t).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω s hs ↦ by
        exact hC s ⟨hs.1.le, hs.2.le⟩ _ (hspatial ω)) (integrable_const C)
      (Filter.Eventually.of_forall fun ω s _ ↦ by
        exact PDE.hasDerivAt_timeSpaceCons u s (x + r • (ω : ℝ^n))
          ((hu.differentiable one_ne_zero).differentiableAt))
  have hderiv := hmain.2.div_const (unitSphereArea n)
  simpa [waveSphericalMean, unitSphereAverage, F, F', μ] using hderiv

/-- The second time derivative of a spherical mean is the spherical mean of
the second time-coordinate derivative. -/
theorem hasDerivAt_deriv_waveSphericalMean_time (u : ℝ^(n + 1) → ℝ) (x : ℝ^n) (t r : ℝ)
    (hu : ContDiff ℝ 2 u) :
    HasDerivAt (fun s ↦ deriv (fun q ↦ waveSphericalMean u x q r) s)
      (unitSphereAverage n (fun y ↦ (∂[0] (fun p ↦ (∂[0] u) p)) (timeSpaceCons t y)) x r) t := by
  let ut : ℝ^(n + 1) → ℝ := fun p ↦ (∂[0] u) p
  have hut : ContDiff ℝ 1 ut := PDE.contDiff_partialDeriv_of_succ
      (m := 1) (i := (0 : Fin (n + 1))) hu
  have heq : (fun s ↦ deriv (fun q ↦ waveSphericalMean u x q r) s) =
        fun s ↦ waveSphericalMean ut x s r := by
    funext s
    exact (hasDerivAt_waveSphericalMean_time u x s r
      (hu.of_le (by norm_num))).deriv
  rw [heq]
  simpa [ut, waveSphericalMean] using hasDerivAt_waveSphericalMean_time ut x t r hut

/-- If the wave residual vanishes along one time slice, then the averaged
second time derivative equals the averaged spatial Laplacian on that slice. -/
theorem secondTimeAverage_eq_laplacianAverage_of_timeSlice (u : ℝ^(n + 1) → ℝ) (x : ℝ^n) (t r : ℝ)
    (hu : ContDiff ℝ 2 u) (hwave : ∀ y : ℝ^n, waveOperator (n := n) u (timeSpaceCons t y) = 0) :
    unitSphereAverage n (fun y ↦ (∂[0] (fun p ↦ (∂[0] u) p)) (timeSpaceCons t y)) x r =
      unitSphereAverage n (laplacian (fun y ↦ u (timeSpaceCons t y))) x r := by
  have hfun : (fun y ↦ (∂[0] (fun p ↦ (∂[0] u) p)) (timeSpaceCons t y)) =
        laplacian (fun y ↦ u (timeSpaceCons t y)) := by
    funext y
    rw [laplacian_timeSlice u t y hu]
    exact sub_eq_zero.mp (hwave y)
  rw [hfun]

/-- A classical homogeneous wave solution has equal averaged second time
derivative and averaged spatial Laplacian. -/
theorem secondTimeAverage_eq_laplacianAverage (u : ℝ^(n + 1) → ℝ) (x : ℝ^n) (t r : ℝ)
    (hu : ContDiff ℝ 2 u) (hwave : ∀ p, waveOperator (n := n) u p = 0) :
    unitSphereAverage n (fun y ↦ (∂[0] (fun p ↦ (∂[0] u) p)) (timeSpaceCons t y)) x r =
      unitSphereAverage n (laplacian (fun y ↦ u (timeSpaceCons t y))) x r :=
  secondTimeAverage_eq_laplacianAverage_of_timeSlice u x t r hu (fun y ↦ hwave (timeSpaceCons t y))

/-- The spherical mean satisfies Euler-Poisson-Darboux whenever the wave
residual vanishes along the time slice being averaged. -/
theorem waveSphericalMean_eulerPoissonDarboux_of_timeSlice [Fact (0 < n)] (u : ℝ^(n + 1) → ℝ)
    (x : ℝ^n) (t : ℝ) {r : ℝ} (hr : 0 < r) (hu : ContDiff ℝ 2 u)
    (hwave : ∀ y : ℝ^n, waveOperator (n := n) u (timeSpaceCons t y) = 0) :
    deriv (deriv (fun s ↦ waveSphericalMean u x s r)) t = deriv (deriv (waveSphericalMean u x t))
      r + (((n : ℝ) - 1) / r) * deriv (waveSphericalMean u x t) r := by
  have hslice : ContDiff ℝ 2 (fun y ↦ u (timeSpaceCons t y)) :=
    hu.comp (contDiff_timeSpaceCons_spatial n t)
  calc
    deriv (deriv (fun s ↦ waveSphericalMean u x s r)) t = unitSphereAverage n (fun y ↦
            (∂[0] (fun p ↦ (∂[0] u) p)) (timeSpaceCons t y)) x r :=
      (hasDerivAt_deriv_waveSphericalMean_time u x t r hu).deriv
    _ = unitSphereAverage n (laplacian (fun y ↦ u (timeSpaceCons t y))) x r :=
      secondTimeAverage_eq_laplacianAverage_of_timeSlice u x t r hu hwave
    _ = deriv (deriv (waveSphericalMean u x t)) r + (((n : ℝ) - 1) / r) *
            deriv (waveSphericalMean u x t) r := by
      change unitSphereAverage n (laplacian (fun y ↦ u (timeSpaceCons t y))) x r = deriv (deriv
                (unitSphereAverage n (fun y ↦ u (timeSpaceCons t y)) x)) r + (((n : ℝ) - 1) / r) *
              deriv (unitSphereAverage n (fun y ↦ u (timeSpaceCons t y)) x) r
      exact (radialLaplacian_unitSphereAverage' (n := n) (fun y ↦ u (timeSpaceCons t y))
          x hr hslice).symm

/-- The spherical mean of a classical wave solution satisfies the
Euler-Poisson-Darboux equation for positive radius. -/
theorem waveSphericalMean_eulerPoissonDarboux [Fact (0 < n)] (u : ℝ^(n + 1) → ℝ) (x : ℝ^n) (t : ℝ)
    {r : ℝ} (hr : 0 < r) (hu : ContDiff ℝ 2 u) (hwave : ∀ p, waveOperator (n := n) u p = 0) :
    deriv (deriv (fun s ↦ waveSphericalMean u x s r)) t = deriv (deriv (waveSphericalMean u x t))
      r + (((n : ℝ) - 1) / r) * deriv (waveSphericalMean u x t) r :=
  waveSphericalMean_eulerPoissonDarboux_of_timeSlice u x t hr hu (fun y ↦ hwave (timeSpaceCons t y))

/-- The radial derivative of a classical spherical mean vanishes at the
center.  Only `C¹` regularity is needed for this center condition. -/
theorem deriv_waveSphericalMean_zero (u : ℝ^(n + 1) → ℝ) (x : ℝ^n) (t : ℝ) (hu : ContDiff ℝ 1 u) :
    deriv (waveSphericalMean u x t) 0 = 0 := by
  have hslice : ContDiff ℝ 1 (fun y ↦ u (timeSpaceCons t y)) :=
    hu.comp (contDiff_timeSpaceCons_spatial n t)
  exact deriv_unitSphereAverage_zero _ x hslice

end WaveEquation
