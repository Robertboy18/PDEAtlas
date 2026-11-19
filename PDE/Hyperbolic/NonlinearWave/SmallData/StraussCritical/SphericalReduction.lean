/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Calculus.SphericalMean.Regularity
public import PDE.Hyperbolic.Models.Wave.EulerPoissonDarboux
public import PDE.Hyperbolic.Models.Wave.OddDimensions.AnalyticBridge
import PDE.FDeriv.Laplacian.Continuity
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# The forced radial reduction in three dimensions

Multiplication of the spherical mean by its signed radius turns the
three-dimensional forced wave equation into a one-dimensional forced equation.
The source is the radius times the spherical mean of the original source.
Oddness extends the calculation through the center without dividing by zero.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Analysis PDE.Common

namespace WaveEquation.SmallData

/-- The radius-weighted spherical mean about the spatial origin. -/
def radiusMean (u : ℝ^4 → ℝ) (z : ℝ^2) : ℝ :=
  z 1 * waveSphericalMean u 0 (z 0) (z 1)

/-- Spherical reduction preserves every finite order of joint regularity. -/
theorem contDiff_radiusMean {u : ℝ^4 → ℝ} {k : ℕ} (hu : ContDiff ℝ k u) :
    ContDiff ℝ k (radiusMean u) := by
  have hfamily : ContDiff ℝ k
      (fun z : ℝ^2 × ℝ^3 ↦ u (timeSpaceCons (z.1 0) ((z.1 1) • z.2))) := by
    apply hu.comp
    have hp : ContDiff ℝ k (fun z : ℝ^2 × ℝ^3 ↦ (z.1 0, (z.1 1) • z.2)) := by
      have h₀ : ContDiff ℝ k (fun z : ℝ^2 × ℝ^3 ↦ z.1 0) :=
        (contDiff_piLp_apply 2).comp contDiff_fst
      have h₁ : ContDiff ℝ k (fun z : ℝ^2 × ℝ^3 ↦ z.1 1) :=
        (contDiff_piLp_apply 2).comp contDiff_fst
      have hs : ContDiff ℝ k (fun z : ℝ^2 × ℝ^3 ↦ (z.1 1) • z.2) := h₁.fun_smul contDiff_snd
      exact h₀.prodMk hs
    exact (contDiff_timeSpaceCons_uncurry 3).comp hp
  have hi := (PDE.contDiff_integral_compact_parametrization
    (μ := (volume : Measure (ℝ^3)).toSphere) hfamily continuous_subtype_val).div_const
      (unitSphereArea 3)
  have hc : ContDiff ℝ k (fun z : ℝ^2 ↦ z 1) := contDiff_piLp_apply 2
  unfold radiusMean waveSphericalMean unitSphereAverage
  simpa only [zero_add] using hc.mul hi

/-- The reduced profile is odd in its signed spatial coordinate. -/
theorem radiusMean_odd (u : ℝ^4 → ℝ) (t : ℝ) :
    Function.Odd (fun r ↦ radiusMean u (timeSpaceCons t
      (EuclideanSpace.single (0 : Fin 1) r))) := by
  intro r
  simp only [radiusMean, timeSpaceCons_zero, timeSpaceCons_single_one,
    waveSphericalMean_neg_radius, neg_mul]

/-- The second time derivative of the reduced profile is the reduced acceleration. -/
theorem secondTime_radiusMean {u : ℝ^4 → ℝ} (hu : ContDiff ℝ 2 u) (t r : ℝ) :
    deriv (deriv (fun s ↦ radiusMean u (timeSpaceCons s (EuclideanSpace.single (0 : Fin 1) r)))) t =
      r * unitSphereAverage 3 (fun y ↦ (∂[0] (∂[0] u)) (timeSpaceCons t y)) 0 r := by
  simp only [radiusMean, timeSpaceCons_zero, timeSpaceCons_single_one]
  have heq : deriv (fun s ↦ r * waveSphericalMean u 0 s r) =
      fun s ↦ r * deriv (fun q ↦ waveSphericalMean u 0 q r) s := by
    funext s
    exact deriv_const_mul_field _
  rw [heq, deriv_const_mul_field, (hasDerivAt_deriv_waveSphericalMean_time u 0 t r hu).deriv]

/-- The second radius derivative is the radius-weighted mean of the Laplacian,
including negative radii and the center. -/
theorem secondRadius_radiusMean {u : ℝ^4 → ℝ} (hu : ContDiff ℝ 2 u) (t r : ℝ) :
    deriv (deriv (fun s ↦ radiusMean u (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) s)))) r =
      r * unitSphereAverage 3 (PDE.laplacian (fun y ↦ u (timeSpaceCons t y))) 0 r := by
  let v := fun s ↦ radiusMean u (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) s))
  let L := fun s ↦ s * unitSphereAverage 3 (PDE.laplacian (fun y ↦ u (timeSpaceCons t y))) 0 s
  have hodd : Function.Odd (deriv (deriv v)) :=
    odd_deriv_of_even (even_deriv_of_odd (radiusMean_odd u t))
  have hLodd : Function.Odd L := by
    intro s
    simp only [L, unitSphereAverage_neg_radius, neg_mul]
  have hpos (s : ℝ) (hs : 0 < s) : deriv (deriv v) s = L s := by
    simpa only [v, L, radiusMean, timeSpaceCons_zero, timeSpaceCons_single_one,
      waveSphericalMean, Function.comp_def] using secondDeriv_radius_mul_unitSphereAverage
        (hu.comp (contDiff_timeSpaceCons_spatial 3 t)) 0 hs
  change deriv (deriv v) r = L r
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · exact neg_injective ((hodd r).symm.trans ((hpos (-r) (neg_pos.mpr hr)).trans (hLodd r)))
  · rw [hodd.map_zero, hLodd.map_zero]
  · exact hpos r hr

/-- The radial reduction carries the forced PDE to its averaged source. -/
theorem waveOperator_radiusMean {u f : ℝ^4 → ℝ} (hu : ContDiff ℝ 2 u) (hf : Continuous f) {t : ℝ}
    (hwave : ∀ y : ℝ^3, waveOperator u (timeSpaceCons t y) = f (timeSpaceCons t y)) (r : ℝ) :
    waveOperator (radiusMean u) (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) r)) =
      radiusMean f (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) r)) := by
  rw [waveOperator_one_timeSpaceCons_single _ (contDiff_radiusMean hu),
    secondTime_radiusMean hu, secondRadius_radiusMean hu]
  have heq : (fun y ↦ (∂[0] (∂[0] u)) (timeSpaceCons t y)) =
      fun y ↦ PDE.laplacian (fun x ↦ u (timeSpaceCons t x)) y + f (timeSpaceCons t y) := by
    funext y
    have he := hwave y
    rw [waveOperator, ← laplacian_timeSlice u t y hu] at he
    exact sub_eq_iff_eq_add'.mp he
  rw [heq]
  have hL : Continuous (PDE.laplacian (fun y ↦ u (timeSpaceCons t y))) :=
    (hu.comp (contDiff_timeSpaceCons_spatial 3 t)).continuous_coordinate_laplacian
  have hi (g : ℝ^3 → ℝ) (hg : Continuous g) :
      Integrable (fun ω : Metric.sphere (0 : ℝ^3) 1 ↦ g (0 + r • (ω : ℝ^3)))
        (volume : Measure (ℝ^3)).toSphere :=
    (hg.comp (by fun_prop)).integrable_of_hasCompactSupport
      (isCompact_univ.of_isClosed_subset isClosed_closure (fun _ _ ↦ Set.mem_univ _))
  simp only [radiusMean, waveSphericalMean, timeSpaceCons_zero, timeSpaceCons_single_one,
    unitSphereAverage]
  have hft : Continuous (fun y ↦ f (timeSpaceCons t y)) :=
    hf.comp (contDiff_timeSpaceCons_spatial 3 t (m := 1)).continuous
  rw [integral_add (hi _ hL) (hi _ hft), add_div]
  ring

end WaveEquation.SmallData
