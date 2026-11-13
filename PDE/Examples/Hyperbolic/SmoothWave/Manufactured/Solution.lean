/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Examples.Hyperbolic.SmoothWave.Manufactured.Data
public import PDE.Hyperbolic.HigherRegularity.Smooth.Classical.WellPosedness
import PDE.Hyperbolic.HigherRegularity.Smooth.Classical.Compatibility
import CAS.ExactTactic
import PDE.Symbolic.PDEDerivatives

/-!
# Smooth wave existence on nonflat compatible data

The explicit wave is a classical solution, so the data satisfy every compatibility
condition (`compatible`). The smooth existence and uniqueness theorem
`exists_unique_classicalSolution` then gives a solution, unique on the closed cylinder,
and it equals the wave there (`raw_data_solution`). The forcing does not vanish at the
lateral boundary, and the potential takes both signs.
-/

@[expose] public noncomputable section

namespace PDE.Examples.SmoothWave.Manufactured

open Set PDE.Common SobolevSpace SobolevSpace.GraphSpace
open SobolevSpace.GraphSpace.BoundaryRegularity SobolevSpace.Evolution.Classical
open Hyperbolic.HigherRegularity.SmoothWave

/-- All time derivatives of the explicit wave equal the original wave. -/
theorem iterated_time_wave (j : ℕ) :
    iteratedPartialDeriv (List.replicate j (0 : Fin 2)) wave = wave := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change ∂[(0 : Fin 2)] (iteratedPartialDeriv (List.replicate j 0) wave) = wave
    rw [ih]
    exact funext partial_time_wave

/-- On the closed cylinder every time-derivative slice of the wave equals the wave. -/
theorem time_slice_wave (j : ℕ) {t : ℝ} (ht : t ∈ Icc 0 1)
    {x : ℝ^1} (hx : x ∈ closure domain) :
    derivativeSlice domain_open wave_regular (List.replicate j 0) t x =
      wave (timeSpaceCons t x) := by
  rw [derivativeSlice_eq_of_continuousOn domain_open (by norm_num : (0 : ℝ) < 1)
    wave_regular (List.replicate j 0)
    (contDiff_top_iteratedPartialDeriv wave_contDiff _).continuous.continuousOn ht hx,
    iterated_time_wave]

/-- The profile vanishes on the endpoints of the spatial interval. -/
theorem profile_boundary {x : ℝ^1} (hx : x ∈ frontier domain) : profile x = 0 := by
  have hxnorm : ‖x‖ = 1 := by
    simpa [domain, Boundary.Atlas.UnitBall.domain,
      frontier_ball (0 : ℝ^1) one_ne_zero,
      Metric.mem_sphere, dist_zero_right] using hx
  have hs : x 0 ^ 2 = 1 := by
    simpa [Fintype.sum_unique, hxnorm] using (EuclideanSpace.real_norm_sq_eq x).symm
  simp [profile, hs]

/-- The wave is a classical solution with initial displacement and velocity `profile`. -/
theorem wave_isClassicalSolution :
    IsClassicalSolution coefficients domain_open forcing_regular profile_regular
      profile_regular wave := by
  refine ⟨wave_contDiff.continuous.continuousOn, wave_regular, ?_, ?_, ?_, ?_⟩
  · intro t ht x hx
    rw [show derivativeSlice domain_open wave_regular [0, 0] t x = wave (timeSpaceCons t x)
      from time_slice_wave 2 ht (subset_closure hx),
      derivativeSlice_nil domain_open (by norm_num : (0 : ℝ) < 1) forcing_regular
        forcing_contDiff.continuous.continuousOn ht (subset_closure hx)]
    exact equation t x
  · intro t ht x hx
    change Real.exp t * profile x = 0
    rw [profile_boundary hx, mul_zero]
  · intro x hx
    have hc : Continuous profile := by unfold profile; fun_prop
    rw [(profile_regular 0).continuousRepresentative_eqOn_closure hc.continuousOn
      (fun _ _ ↦ rfl) hx]
    change Real.exp 0 * (1 - x 0 ^ 2) = 1 - x 0 ^ 2
    simp
  · intro x hx
    rw [show derivativeSlice domain_open wave_regular [0] 0 x = wave (timeSpaceCons 0 x)
      from time_slice_wave 1 ⟨le_rfl, zero_le_one⟩ hx]
    have hc : Continuous profile := by unfold profile; fun_prop
    rw [(profile_regular 0).continuousRepresentative_eqOn_closure hc.continuousOn
      (fun _ _ ↦ rfl) hx]
    change Real.exp 0 * (1 - x 0 ^ 2) = 1 - x 0 ^ 2
    simp

/-- The data satisfy every compatibility condition. -/
theorem compatible : HasCompatibleBoundaryValues coefficients domain_open domain_bounded
    (by norm_num : (0 : ℝ) < 1) forcing_regular profile_regular profile_regular :=
  wave_isClassicalSolution.hasCompatibleBoundaryValues (by norm_num) domain_bounded
    ((domain_graph 1).hasC1GraphBoundary le_rfl) (by norm_num)

/-- The problem has a classical solution, unique on the closed cylinder, and it equals the
wave there. -/
theorem raw_data_solution :
    ∃ U : SpaceTime 1 → ℝ,
      IsClassicalSolution coefficients domain_open forcing_regular profile_regular
        profile_regular U ∧
      EqOn U wave (splitSpaceTime ⁻¹' (closure domain ×ˢ Icc 0 1)) ∧
      ∀ V : SpaceTime 1 → ℝ,
        IsClassicalSolution coefficients domain_open forcing_regular profile_regular
          profile_regular V →
        EqOn U V (splitSpaceTime ⁻¹' (closure domain ×ˢ Icc 0 1)) := by
  obtain ⟨U, hU, huniq⟩ := exists_unique_classicalSolution coefficients (by norm_num)
    domain_open domain_bounded domain_graph (by norm_num) coefficients_symmetric
    (by norm_num : (0 : ℝ) < 1) coefficients_elliptic
    forcing_regular profile_regular profile_regular compatible
  exact ⟨U, hU, huniq wave wave_isClassicalSolution, huniq⟩

/-- The left-endpoint forcing is nonzero at every time. -/
theorem forcing_left (t : ℝ) :
    forcing (timeSpaceCons t (EuclideanSpace.single (0 : Fin 1) (-1))) = 4 * Real.exp t := by
  change Real.exp t * (3 - (-1) - (-1) ^ 2 - (-1) ^ 3) = 4 * Real.exp t
  cas

/-- The initial data are not flat at the lateral boundary. -/
theorem profile_derivative (x : ℝ^1) : (∂[(0 : Fin 1)] profile) x = -2 * x 0 := by
  unfold profile
  cas

/-- The drift is nonzero and the potential takes both signs inside the domain. -/
theorem lower_order_nontrivial :
    coefficients.drift 0 0 = 1 ∧
    coefficients.potential (EuclideanSpace.single 0 (-(1 / 2))) < 0 ∧
    0 < coefficients.potential (EuclideanSpace.single 0 (1 / 2)) := by
  norm_num [coefficients]

/-- Both signs of the potential occur strictly inside the spatial interval. -/
theorem potential_test_points_mem :
    EuclideanSpace.single (0 : Fin 1) (-(1 / 2)) ∈ domain ∧
      EuclideanSpace.single (0 : Fin 1) (1 / 2) ∈ domain := by
  norm_num [domain, Boundary.Atlas.UnitBall.domain, Metric.mem_ball,
    dist_zero_right, PiLp.norm_single]

end PDE.Examples.SmoothWave.Manufactured
