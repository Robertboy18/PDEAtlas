/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.SmallData.Mass
public import PDE.Hyperbolic.Models.Wave.Kirchhoff.ClassicalSolution
import CAS.ExactTactic

/-!
# Support and mass of three-dimensional free waves

Compact displacement and velocity propagate in an outgoing Huygens shell.
The velocity potential has mass `t ∫h`; differentiating the displacement
potential gives the full affine mass `∫g + t ∫h`. Compact support justifies
the spatial integrals and their derivatives.
-/

@[expose] public noncomputable section

open MeasureTheory PDE.Analysis PDE.Common Set

namespace WaveEquation.SmallData

private theorem norm_sphere_point (ω : Metric.sphere (0 : ℝ^3) 1) :
    ‖(ω : ℝ^3)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using ω.property

/-- A velocity potential vanishes if its sampling sphere misses the data ball. -/
theorem kirchhoffPotential_eq_zero_of_shell {h : ℝ^3 → ℝ} {R t : ℝ}
    (hs : ∀ y : ℝ^3, R < ‖y‖ → h y = 0) (ht : 0 ≤ t) (x : ℝ^3) (hx : ‖x‖ < t - R ∨ R + t < ‖x‖) :
    kirchhoffPotential h (timeSpaceCons t x) = 0 := by
  rw [kirchhoffPotential_timeSpaceCons]
  have hz : ∀ ω : Metric.sphere (0 : ℝ^3) 1, h (x + t • (ω : ℝ^3)) = 0 := by
    intro ω
    apply hs
    have hn : ‖t • (ω : ℝ^3)‖ = t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, norm_sphere_point, mul_one]
    rcases hx with hx | hx
    · have hi := norm_sub_le (x + t • (ω : ℝ^3)) x
      simp only [add_sub_cancel_left, hn] at hi
      linarith
    · have hi := norm_sub_le (x + t • (ω : ℝ^3)) (t • (ω : ℝ^3))
      simp only [add_sub_cancel_right, hn] at hi
      linarith
  simp only [unitSphereAverage, hz, integral_zero, zero_div, mul_zero]

/-- Compact velocity data give the forward support cone. -/
theorem kirchhoffPotential_hasForwardSupport {h : ℝ^3 → ℝ} {R : ℝ}
    (hs : ∀ y : ℝ^3, R < ‖y‖ → h y = 0) :
    HasForwardSupport (kirchhoffPotential h) R :=
  fun _ ht x hx ↦ kirchhoffPotential_eq_zero_of_shell hs ht x (Or.inr hx)

/-- Compact support justifies exchanging spatial and angular integration. -/
theorem integrable_kirchhoff_sampling {h : ℝ^3 → ℝ} {R : ℝ} (hh : Continuous h)
    (hs : ∀ y : ℝ^3, R < ‖y‖ → h y = 0) (t : ℝ) :
    Integrable (fun z : ℝ^3 × Metric.sphere (0 : ℝ^3) 1 ↦ h (z.1 + t • (z.2 : ℝ^3)))
      (volume.prod (volume : Measure (ℝ^3)).toSphere) := by
  have hc : Continuous (fun z : ℝ^3 × Metric.sphere (0 : ℝ^3) 1 ↦
      h (z.1 + t • (z.2 : ℝ^3))) := by fun_prop
  apply hc.integrable_of_hasCompactSupport
  refine HasCompactSupport.intro ((isCompact_closedBall (0 : ℝ^3) (R + |t|)).prod isCompact_univ) ?_
  intro z hz
  apply hs
  have hx : R + |t| < ‖z.1‖ := by
    simpa only [mem_prod, mem_univ, and_true, Metric.mem_closedBall,
      dist_zero_right, not_le] using hz
  have hi := norm_sub_le (z.1 + t • (z.2 : ℝ^3)) (t • (z.2 : ℝ^3))
  simp only [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, norm_sphere_point, mul_one] at hi
  linarith

/-- The free velocity wave has spatial mass `t * ∫h`, at every real time. -/
theorem spatialMass_kirchhoffPotential {h : ℝ^3 → ℝ} {R : ℝ} (hh : Continuous h)
    (hs : ∀ y : ℝ^3, R < ‖y‖ → h y = 0) (t : ℝ) :
    spatialMass (kirchhoffPotential h) t = t * ∫ y : ℝ^3, h y := by
  unfold spatialMass
  simp only [kirchhoffPotential_timeSpaceCons, unitSphereAverage]
  rw [integral_const_mul, integral_div,
    integral_integral_swap (integrable_kirchhoff_sampling hh hs t)]
  simp_rw [integral_add_right_eq_self]
  simp only [integral_const, smul_eq_mul, measureReal_def]
  rw [show ((volume : Measure (ℝ^3)).toSphere univ).toReal = unitSphereArea 3 from rfl]
  congr 1
  exact mul_div_cancel_left₀ _ unitSphereArea_pos.ne'

/-- Compact displacement and velocity propagate inside the same forward cone. -/
theorem kirchhoffFormula_hasForwardSupport {g h : ℝ^3 → ℝ} {R : ℝ} (hg : ContDiff ℝ 1 g)
    (hh : Continuous h) (hgs : ∀ y : ℝ^3, R < ‖y‖ → g y = 0) (hhs : ∀ y : ℝ^3, R < ‖y‖ → h y = 0) :
    HasForwardSupport (spaceTimeUncurry (kirchhoffFormula g h)) R := by
  rw [kirchhoffFormula_eq_potentials hg hh]
  intro t ht x hx
  change (∂[0] (kirchhoffPotential g)) (timeSpaceCons t x) +
    kirchhoffPotential h (timeSpaceCons t x) = 0
  rw [(kirchhoffPotential_hasForwardSupport hgs).partialDeriv_time t ht x hx,
    kirchhoffPotential_hasForwardSupport hhs t ht x hx, add_zero]
/-- Both parts of the free wave lie in the outgoing Huygens shell. -/
theorem kirchhoffFormula_eq_zero_of_shell {g h : ℝ^3 → ℝ} {R t : ℝ} (hg : ContDiff ℝ 1 g)
    (hh : Continuous h) (hgs : ∀ y : ℝ^3, R < ‖y‖ → g y = 0) (hhs : ∀ y : ℝ^3, R < ‖y‖ → h y = 0)
    (hR : 0 ≤ R) (ht : 0 ≤ t) (x : ℝ^3) (hx : ‖x‖ < t - R ∨ R + t < ‖x‖) :
    spaceTimeUncurry (kirchhoffFormula g h) (timeSpaceCons t x) = 0 := by
  rcases hx with hx | hx
  · have hsupport {f : ℝ^3 → ℝ} (hs : ∀ y : ℝ^3, R < ‖y‖ → f y = 0) :
        Function.support f ⊆ Metric.closedBall 0 R := by
      intro y hy
      by_contra hb
      have hn : R < ‖y‖ := by
        simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hb
      exact hy (hs y hn)
    simpa only [spaceTimeUncurry, spatialPart_timeSpaceCons, PDE.time, timeSpaceCons_zero] using
      kirchhoffFormula_eq_zero_after_wavefront (t := t) x hR (by linarith)
        (hsupport hgs) (hsupport hhs)
  · exact kirchhoffFormula_hasForwardSupport hg hh hgs hhs t ht x hx
/-- Spatial integration of the full free wave recovers the affine initial mass. -/
theorem spatialMass_kirchhoffFormula {g h : ℝ^3 → ℝ} {R t : ℝ} (hg : ContDiff ℝ 2 g)
    (hh : Continuous h) (hgs : ∀ y : ℝ^3, R < ‖y‖ → g y = 0) (hhs : ∀ y : ℝ^3, R < ‖y‖ → h y = 0)
    (ht : 0 < t) :
    spatialMass (spaceTimeUncurry (kirchhoffFormula g h)) t = (∫ y : ℝ^3, g y) + t * ∫ y : ℝ^3,
      h y := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hgp := contDiff_kirchhoffPotential hg1
  have hm := hasDerivAt_spatialMass hgp (kirchhoffPotential_hasForwardSupport hgs) ht
  have he : spatialMass (kirchhoffPotential g) = fun s : ℝ ↦ s * ∫ y : ℝ^3, g y :=
    funext (spatialMass_kirchhoffPotential hg.continuous hgs)
  rw [he] at hm
  have hmass : spatialMass (∂[0] (kirchhoffPotential g)) t = ∫ y : ℝ^3, g y :=
    hm.unique (by cas)
  have hgi : Integrable (fun x : ℝ^3 ↦ (∂[0] (kirchhoffPotential g)) (timeSpaceCons t x)) :=
    ((PDE.contDiff_partialDeriv_of_succ (m := 1) (contDiff_kirchhoffPotential hg)).continuous.comp
      (contDiff_timeSpaceCons_spatial 3 t (m := 1)).continuous).integrable_of_hasCompactSupport
      ((kirchhoffPotential_hasForwardSupport hgs).partialDeriv_time.hasCompactSupport_slice
        ht.le)
  have hhi : Integrable (fun x : ℝ^3 ↦ kirchhoffPotential h (timeSpaceCons t x)) := by
    have hc : Continuous (kirchhoffPotential h) :=
      (contDiff_kirchhoffPotential (k := 0) (contDiff_zero.mpr hh)).continuous
    exact (hc.comp (contDiff_timeSpaceCons_spatial 3 t (m := 1)).continuous)
      |>.integrable_of_hasCompactSupport
        ((kirchhoffPotential_hasForwardSupport hhs).hasCompactSupport_slice ht.le)
  rw [kirchhoffFormula_eq_potentials hg1 hh]
  unfold spatialMass
  rw [integral_add hgi hhi]
  change spatialMass (∂[0] (kirchhoffPotential g)) t + spatialMass (kirchhoffPotential h) t = _
  rw [hmass, spatialMass_kirchhoffPotential hh hhs]

end WaveEquation.SmallData
