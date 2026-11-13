/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat.Radial
import CAS.ExactTactic

/-!
# Annular localization of a Goursat field

A smooth annular extension preserves the equation, zero characteristic and initial velocity near
the comparison cone.
-/

@[expose] public noncomputable section

section

open Set Filter PDE.Common WaveEquation
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- A characteristic field gives a global C³ comparison field with the same
physical values on the fixed spatial annulus. -/
theorem exists_contDiff_radialGoursat_extension {W : Parameter → ℝ} (hW : ContDiff ℝ 3 W) (ε : ℝ) :
    ∃ V : SpaceTime 3 → ℝ, ContDiff ℝ 3 V ∧
      ∀ z : SpaceTime 3, 1 / 2 ≤ ‖spatialPart z‖ → ‖spatialPart z‖ ≤ 3 / 2 →
        V z = radialGoursatField W ε z := by
  have hn : ContDiffOn ℝ (3 : ℕ∞) (fun x : ℝ^3 ↦ ‖x‖) {0}ᶜ := by
    intro x hx
    exact (contDiffAt_norm ℝ hx).contDiffWithinAt
  have hi : ContDiffOn ℝ (3 : ℕ∞) (fun x : ℝ^3 ↦ (‖x‖)⁻¹) {0}ᶜ := by
    intro x hx
    exact ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).contDiffWithinAt
  obtain ⟨ρ, hρ, _, hρeq⟩ := hn.exists_contDiff_compactSupport_eqOn_annulus
    (a := 1 / 2) (b := 3 / 2) (by norm_num) (by norm_num)
  obtain ⟨j, hj, _, hjeq⟩ := hi.exists_contDiff_compactSupport_eqOn_annulus
    (a := 1 / 2) (b := 3 / 2) (by norm_num) (by norm_num)
  let V : SpaceTime 3 → ℝ := fun z ↦ j (spatialPartCLM 3 z) *
    W (time z + ρ (spatialPartCLM 3 z) - 1, time z - ρ (spatialPartCLM 3 z) + 1, ε)
  have hρ3 : ContDiff ℝ 3 (fun z : SpaceTime 3 ↦ ρ (spatialPartCLM 3 z)) :=
    hρ.comp (spatialPartCLM 3).contDiff
  have ht : ContDiff ℝ 3 (time : SpaceTime 3 → ℝ) := (timeCLM 3).contDiff
  have hpath : ContDiff ℝ 3 (fun z : SpaceTime 3 ↦
      (time z + ρ (spatialPartCLM 3 z) - 1, time z - ρ (spatialPartCLM 3 z) + 1, ε)) :=
    ((ht.add hρ3).sub contDiff_const).prodMk
      (((ht.sub hρ3).add contDiff_const).prodMk contDiff_const)
  refine ⟨V, (hj.comp (spatialPartCLM 3).contDiff).mul (hW.comp hpath), ?_⟩
  intro z hlow hhigh
  dsimp only [V, radialGoursatField]
  rw [spatialPartCLM_eq_spatialPart, hρeq _ hlow hhigh, hjeq _ hlow hhigh]
  exact (div_eq_inv_mul _ _).symm

/-- Annular equality identifies the full germ at every interior annular point. -/
theorem eventuallyEq_radialGoursatField_of_annular_eq {W : Parameter → ℝ} {ε : ℝ}
    {V : SpaceTime 3 → ℝ}
    (heq : ∀ z : SpaceTime 3, 1 / 2 ≤ ‖spatialPart z‖ → ‖spatialPart z‖ ≤ 3 / 2 → V z =
      radialGoursatField W ε z)
    {z : SpaceTime 3} (hzlow : 1 / 2 < ‖spatialPart z‖) (hzhigh : ‖spatialPart z‖ < 3 / 2) :
    V =ᶠ[𝓝 z] radialGoursatField W ε := by
  have hc : Continuous (fun q : SpaceTime 3 ↦ ‖spatialPart q‖) := by
    have he : (fun q : SpaceTime 3 ↦ ‖spatialPartCLM 3 q‖) =
        fun q : SpaceTime 3 ↦ ‖spatialPart q‖ := by
      funext q
      rw [spatialPartCLM_eq_spatialPart]
    rw [← he]
    exact (spatialPartCLM 3).continuous.norm
  filter_upwards [hc.continuousAt.eventually (isOpen_Ioo.mem_nhds ⟨hzlow, hzhigh⟩)] with q hq
  exact heq q hq.1.le hq.2.le

/-- Annular localization preserves the signed quadratic equation on every
sufficiently short incoming backward cone. -/
theorem annular_extension_signed_quadratic_on_cone {W : Parameter → ℝ} (hW : ContDiff ℝ 2 W)
    {ε η T : ℝ}
    (hzero : ∀ b ∈ Ioo (-η) η, W (0, b, ε) = 0 ∧ HasDerivAt (fun a : ℝ ↦ W (a, b, ε)) ε 0)
    (hmixed : ∀ a ∈ Ioo (-η) 0, ∀ b ∈ Ioo (-η) η, HasDerivAt
      (fun t : ℝ ↦ deriv (fun s : ℝ ↦ W (s, t, ε)) a) (-Real.signedPower 2 (W (a, b, ε)) /
      (4 * (1 + (a - b) / 2))) b)
    {V : SpaceTime 3 → ℝ}
    (heq : ∀ z : SpaceTime 3, 1 / 2 ≤ ‖spatialPart z‖ → ‖spatialPart z‖ ≤ 3 / 2 → V z =
      radialGoursatField W ε z)
    (hTη : 2 * T < η) (hTsmall : T < 1 / 4) {x : ℝ^3} (hx : T + ‖x‖ = 1) {s : ℝ}
    (hs : s ∈ Icc 0 T) {y : ℝ^3} (hy : y ∈ Metric.closedBall x (T - s)) :
    waveOperator V (timeSpaceCons s y) + Real.signedPower 2 (V (timeSpaceCons s y)) = 0 := by
  obtain ⟨_, _, _, _, hradlow, hradhigh⟩ := backwardCone_characteristic_bounds hx hs hy
  have hgerm := eventuallyEq_radialGoursatField_of_annular_eq heq
    (z := timeSpaceCons s y) (by simpa using (show (1 : ℝ) / 2 < ‖y‖ by linarith))
    (by simpa using (show ‖y‖ < (3 : ℝ) / 2 by linarith))
  rw [waveOperator_congr_nhds hgerm, hgerm.eq_of_nhds]
  exact radialGoursatField_signed_quadratic_on_cone hW hzero hmixed hTη hTsmall hx hs hy

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end

section

open Set Filter PDE PDE.Common WaveEquation
open scoped Topology

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

/-- The incoming zero characteristic has time velocity `epsilon/r` in physical
coordinates. Both statements refer to the same lifted field. -/
theorem radialGoursatField_zero_characteristic_trace {W : Parameter → ℝ} (hW : ContDiff ℝ 1 W)
    {ε η t : ℝ}
    (hzero : ∀ b ∈ Ioo (-η) η, W (0, b, ε) = 0 ∧ HasDerivAt (fun a : ℝ ↦ W (a, b, ε)) ε 0) {x : ℝ^3}
    (hx : t + ‖x‖ - 1 = 0) (hb : t - ‖x‖ + 1 ∈ Ioo (-η) η) :
    radialGoursatField W ε (timeSpaceCons t x) = 0 ∧ HasDerivAt
      (fun s : ℝ ↦ radialGoursatField W ε (timeSpaceCons s x)) (ε / ‖x‖) t := by
  have hA : fderiv ℝ W (0, t - ‖x‖ + 1, ε) (1, 0, 0) = ε := by
    rw [← deriv_polynomial_goursat_first_eq_fderiv hW]
    exact (hzero _ hb).2.deriv
  have hBzero : HasDerivAt (fun b : ℝ ↦ W (0, b, ε)) 0 (t - ‖x‖ + 1) := by
    apply (hasDerivAt_const (t - ‖x‖ + 1) (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hb] with b hb'
    exact (hzero b hb').1
  have hpathB : HasDerivAt (fun b : ℝ ↦ ((0 : ℝ), b, ε)) (0, 1, 0) (t - ‖x‖ + 1) :=
    (hasDerivAt_const _ (0 : ℝ)).prodMk ((hasDerivAt_id _).prodMk (hasDerivAt_const _ ε))
  have hDB := (hW.differentiable one_ne_zero (0, t - ‖x‖ + 1, ε)).hasFDerivAt.comp_hasDerivAt
    (t - ‖x‖ + 1) hpathB
  have hB : fderiv ℝ W (0, t - ‖x‖ + 1, ε) (0, 1, 0) = 0 := hDB.unique hBzero
  constructor
  · simp only [radialGoursatField, time, timeSpaceCons_zero, spatialPart_timeSpaceCons,
      hx, (hzero _ hb).1, zero_div]
  · have hpath : HasDerivAt
        (fun s : ℝ ↦ (s + ‖x‖ - 1, s - ‖x‖ + 1, ε)) (1, 1, 0) t := by
      have ha : HasDerivAt (fun s : ℝ ↦ s + ‖x‖ - 1) 1 t := by
        generalize ‖x‖ = r
        cas
      have hb' : HasDerivAt (fun s : ℝ ↦ s - ‖x‖ + 1) 1 t := by
        generalize ‖x‖ = r
        cas
      exact ha.prodMk (hb'.prodMk (hasDerivAt_const t ε))
    have hd := ((hW.differentiable one_ne_zero
      (t + ‖x‖ - 1, t - ‖x‖ + 1, ε)).hasFDerivAt.comp_hasDerivAt t hpath).div_const ‖x‖
    have hplus : ((1, 1, 0) : Parameter) = (1, 0, 0) + (0, 1, 0) := by norm_num
    rw [hx, hplus, map_add, hA, hB, add_zero] at hd
    simpa only [Function.comp_def, radialGoursatField, time, timeSpaceCons_zero,
      spatialPart_timeSpaceCons] using hd

/-- Any annular classical extension has the same physical Cauchy velocity as
the branch wherever the fixed spatial point belongs to that annulus. -/
theorem annular_extension_initial_velocity {W : Parameter → ℝ} {ε v : ℝ} {V : SpaceTime 3 → ℝ}
    (hV : ContDiff ℝ 1 V)
    (heq : ∀ z : SpaceTime 3, 1 / 2 ≤ ‖spatialPart z‖ → ‖spatialPart z‖ ≤ 3 / 2 → V z =
      radialGoursatField W ε z)
    {x : ℝ^3} (hxlow : 1 / 2 ≤ ‖x‖) (hxhigh : ‖x‖ ≤ 3 / 2)
    (hv : HasDerivAt (fun t : ℝ ↦ W (t + ‖x‖ - 1, t - ‖x‖ + 1, ε) / ‖x‖) v 0) :
    (∂[0] V) (timeSpaceCons 0 x) = v := by
  have he : (fun t : ℝ ↦ V (timeSpaceCons t x)) =
      fun t : ℝ ↦ W (t + ‖x‖ - 1, t - ‖x‖ + 1, ε) / ‖x‖ := by
    funext t
    simpa only [radialGoursatField, time, timeSpaceCons_zero, spatialPart_timeSpaceCons] using
      heq (timeSpaceCons t x) (by simpa using hxlow) (by simpa using hxhigh)
  have hd := hasDerivAt_timeSpaceCons V 0 x (hV.differentiable one_ne_zero _)
  rw [he] at hd
  exact hd.unique hv

end PDE.Hyperbolic.NonlinearWave.Cauchy.Regularity.Classical.FinitePower.Goursat

end
