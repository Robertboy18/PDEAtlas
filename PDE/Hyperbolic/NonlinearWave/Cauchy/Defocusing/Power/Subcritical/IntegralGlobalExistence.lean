/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.DuhamelAmplitude
public import
  PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralBallRepresentation
public import PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical.IntegralConeEnergy

/-!
# Global C¹ integral existence for every real subcritical power

For compact C³ displacement and C² velocity, every real power `1 < p < 5` admits a global C¹
integral solution of the defocusing wave equation. The cone trace bounds and retarded representation
close the subcritical amplitude estimate on every finite lifespan. Bounded-amplitude continuation
then excludes the finite branch of the constructed lifespan alternative, as the blow-up criterion
(12) of Evans, §12.3.2, Theorem 2(ii), does for smooth solutions.

The same field has the ordinary Cauchy traces, speed-one spatial support, the spatially tested PDE,
and conserved energy on every finite prefix. This is a finite-regularity integral form of Theorem 3
of Evans, §12.3.3: the solution is C¹ and satisfies the integral identity (14) of §12.3.2.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §12.3.2, Theorem 2(ii) and equation (14); §12.3.3, Theorem 3
  and its proof.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory Metric PDE PDE.Common PDE.Analysis WaveEquation
open SobolevSpace SobolevSpace.GraphSpace
open scoped Sobolev SobolevSpace.WholeSpaceHilbert Topology Laplacian

namespace PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical

/-- A subcritical integral trajectory vanishing outside the cone `‖x‖ ≤ R + t`, so with compactly
supported data, has one amplitude bound on its entire finite lifespan. Its proper-prefix bounds
enter only the sublinear feedback step and do not enter the resulting constant. -/
theorem IsIntegralTrajectoryBefore.exists_uniform_amplitude_bound {p b L R : ℝ} (hp : 1 < p)
    (hp5 : p < 5) (hb : 0 < b) {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h)
    {u : ℝ × ℝ^3 → ℝ}
    (hu : IsIntegralTrajectoryBefore p b (cauchyFreeField g h) L u)
    (hpos : ∀ x : ℝ^3, u (0, x) = g x) (hvel : ∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0)
    (hsupp : ∀ z : ℝ × ℝ^3, z.1 ∈ Ico 0 L → R + z.1 < ‖z.2‖ → u z = 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ z : ℝ × ℝ^3, z.1 ∈ Ico 0 L → |u z| ≤ M := by
  have hhs : HasCompactSupport h := hu.hasCompactSupport_initial_velocity hvel hsupp
  have hgs : HasCompactSupport g := hu.hasCompactSupport_initial_position hsupp
  classical
  obtain ⟨G, hgG⟩ := hg.continuous.bounded_above_of_compact_support hgs
  have hG : 0 ≤ G := (norm_nonneg (g 0)).trans (hgG 0)
  have hinit (x : ℝ^3) : ‖u (0, x)‖ ≤ G := by rw [hpos]; exact hgG x
  obtain ⟨V, hV, hfree⟩ := exists_bound_cauchyFreeField_of_compact_data
    (hg.of_le (by norm_num)) (hh.of_le (by norm_num)) hgs hhs L
  let E := √(2 * semilinearWaveSpatialEnergy (Real.signedPowerPotential p)
    (fun z : ℝ^4 ↦ u (timeSpaceContinuousLinearEquiv 3 z)) 0)
  have hE : 0 ≤ E := Real.sqrt_nonneg _
  have he : 2 * semilinearWaveSpatialEnergy (Real.signedPowerPotential p)
      (fun z : ℝ^4 ↦ u (timeSpaceContinuousLinearEquiv 3 z)) 0 ≤ E ^ 2 :=
    (Real.sq_sqrt (mul_nonneg (by norm_num)
      (semilinearWaveSpatialEnergy_nonneg _ (Real.signedPowerPotential_nonneg hp.le)
        _ 0))).ge
  let F := E + G * √(L * volume.real (ball (0 : ℝ^3) 1))
  have hF : 0 ≤ F := add_nonneg hE (mul_nonneg hG (Real.sqrt_nonneg _))
  obtain ⟨B, hB, hbound⟩ := exists_uniform_amplitude_bound_of_duhamel hp hp5 L F V hF hV
  have hprefix (S : ℝ) (hS : 0 < S) (hSL : S < L) :
      ∀ t ∈ Ioo 0 S, ∀ x : ℝ^3, |u (t, x)| ≤ B := by
    let X := Ioo (0 : ℝ) S × ℝ^3
    let w : X → ℝ := fun z ↦ u (z.1.val, z.2)
    let v : X → ℝ := fun z ↦ cauchyFreeField g h (z.1.val, z.2)
    let r : X → ℝ := fun z ↦ z.1.val
    let σ : X → ℝ^3 → X := fun z y ↦ if hτ : 0 < z.1.val - ‖y‖ then
        (⟨z.1.val - ‖y‖, hτ, (sub_le_self _ (norm_nonneg y)).trans_lt z.1.property.2⟩, z.2 + y)
      else z
    have htrace (z : X) : ∃ W : H¹(ball (0 : ℝ^3) (r z)),
        baseRepresentative W =ᵐ[domainMeasure 3 (ball 0 (r z))] (fun y ↦ u (r z - ‖y‖, z.2 + y)) ∧
        ‖∇ W‖ ≤ E ∧ ‖wkpBaseCoordinateCLM W‖ / r z ≤ F :=
      hu.exists_centered_trace_bound hp.le hb hg hh hvel hsupp
        z.1.property.1 (z.1.property.2.trans hSL) (z.1.property.2.trans hSL).le hE hG hinit he z.2
    choose W hbase hgrad hnorm using htrace
    have hbdd : BddAbove (range fun z : X ↦ |w z|) := by
      obtain ⟨A, _, hA⟩ := hu.bounded_before S hS hSL
      exact ⟨A, fun _ ⟨z, hz⟩ ↦ hz ▸ hA (z.1.val, z.2) ⟨z.1.property.1.le, z.1.property.2⟩⟩
    have hrep (z : X) : baseRepresentative (W z) =ᵐ[domainMeasure 3 (ball 0 (r z))]
        fun y ↦ w (σ z y) := by
      filter_upwards [hbase z, ae_restrict_mem measurableSet_ball] with y hy hball
      have hτ : 0 < z.1.val - ‖y‖ := by
        apply sub_pos.mpr
        simpa only [mem_ball, dist_zero_right] using hball
      simpa only [σ, hτ, ↓reduceDIte, w, r] using hy
    have hduhamel (z : X) : w z = v z - (1 / (4 * Real.pi)) *
        ∫ y in ball (0 : ℝ^3) (r z), Real.signedPower p (baseRepresentative (W z) y) / ‖y‖ :=
      hu.eq_centered_retarded_ball (zero_lt_one.trans hp) hb
        ⟨z.1.property.1.le, z.1.property.2.trans hSL⟩ z.2 (W z) (hbase z)
    have hamp := hbound w v r σ W hbdd (fun z ↦ z.1.property.1)
      (fun z ↦ (z.1.property.2.trans hSL).le) (fun z ↦ hfree (z.1.val, z.2)
        ⟨z.1.property.1.le, (z.1.property.2.trans hSL).le⟩) (fun z ↦ (hgrad z).trans
        (le_add_of_nonneg_right (mul_nonneg hG (Real.sqrt_nonneg _)))) hnorm hrep hduhamel
    exact fun t ht x ↦ hamp (⟨t, ht⟩, x)
  refine ⟨max G B, hB.trans_le (le_max_right _ _), fun z hz ↦ ?_⟩
  by_cases ht : z.1 = 0
  · have hz0 : z = (0, z.2) := Prod.ext ht rfl
    change ‖u z‖ ≤ max G B
    rw [hz0]
    exact (hinit z.2).trans (le_max_left G B)
  · obtain ⟨S, htS, hSL⟩ := exists_between hz.2
    exact (hprefix S (hz.1.trans_lt htS) hSL z.1
      ⟨lt_of_le_of_ne hz.1 (Ne.symm ht), htS⟩ z.2).trans (le_max_right _ _)

/-- Every real subcritical signed power and arbitrary compact C³/C² data
construct a global C¹ integral solution with the tested PDE, ordinary
initial traces, speed-one propagation, and conserved energy. -/
theorem exists_global_integral_solution_of_compact_data {p : ℝ} (hp : 1 < p) (hp5 : p < 5)
    {g h : ℝ^3 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (hgs : HasCompactSupport g)
    (hhs : HasCompactSupport h) :
    ∃ b R : ℝ, 0 < b ∧ 0 < R ∧ ∃ u : ℝ × ℝ^3 → ℝ,
      IsGlobalIntegralTrajectory p b (cauchyFreeField g h) u ∧
      (∀ x : ℝ^3, u (0, x) = g x) ∧
      (∀ x : ℝ^3, HasDerivAt (fun t ↦ u (t, x)) (h x) 0) ∧
      (∀ z : ℝ × ℝ^3, 0 ≤ z.1 → R + z.1 < ‖z.2‖ → u z = 0) ∧
      (∀ φ : ℝ^3 → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → ∀ t : ℝ, 0 < t →
        HasDerivAt (deriv (fun s ↦ ∫ x : ℝ^3, u (s, x) * φ x))
          ((∫ x : ℝ^3, u (t, x) * laplacian φ x) -
            ∫ x : ℝ^3, Real.signedPower p (u (t, x)) * φ x) t) ∧
      ∀ S : ℝ, 0 < S → HasConservedEnergyOn p S u := by
  obtain ⟨b, R, hb, hR, hglobal | hfinite⟩ :=
    exists_supported_tested_lifespan_of_compact_data hp.le hg hh hgs hhs
  · obtain ⟨u, hu, hpos, hvel, hsupp, htest⟩ := hglobal
    refine ⟨b, R, hb, hR, u, hu, hpos, hvel, hsupp, htest, fun S hS ↦ ?_⟩
    have hbefore : IsIntegralTrajectoryBefore p b (cauchyFreeField g h) (S + 1) u :=
      ⟨by linarith, hu.regular.mono (fun _ hz ↦ hz.1),
        fun T _ _ ↦ hu.bounded_before T, fun z hz ↦ hu.equation z hz.1⟩
    exact hbefore.hasConservedEnergyOn_of_support hp.le hb hg hh hvel
      (fun z hz ↦ hsupp z hz.1) hS (by linarith)
  · obtain ⟨L, u, hu, hpos, hvel, hsupp, _, hblow⟩ := hfinite
    obtain ⟨M, _, hM⟩ := hu.exists_uniform_amplitude_bound hp hp5 hb hg hh hpos hvel hsupp
    obtain ⟨z, hz, _, hMz⟩ := hblow 0 hu.time_pos M
    exact (not_lt_of_ge (hM z hz) hMz).elim

end PDE.Hyperbolic.NonlinearWave.Cauchy.Defocusing.Power.Subcritical
