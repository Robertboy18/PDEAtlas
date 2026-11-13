/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.Poisson.Representation
public import PDE.Hyperbolic.Models.Wave.Kirchhoff.ClassicalSolution

/-!
# Construction of the two-dimensional Poisson solution

Hadamard descent transfers Kirchhoff's construction to the original Poisson
disk integral. For `C³` displacement and `C²` velocity data, it is jointly `C²`,
solves the wave equation at positive times, and has both joint Cauchy traces.
No decay or support assumptions are needed. This is Evans, §2.4.1, Theorem 3, for `n = 2`, where
the representation (38) is Poisson's formula (27).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1, equation (27) and Theorem 3 for n = 2.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian time SatisfiesPDEProblem)

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- The Poisson disk integral is jointly `C²` for classical Cauchy data. -/
theorem contDiff_two_poissonFormula {g h : ℝ^2 → ℝ} (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) :
    ContDiff ℝ 2 (spaceTimeUncurry (poissonFormula g h)) := by
  apply (contDiff_spaceTimeUncurry_iff _).mpr
  have hK := (contDiff_spaceTimeUncurry_iff _).mp
    (contDiff_two_kirchhoffFormula (hg.comp coordinateProjection.contDiff)
      (hh.comp coordinateProjection.contDiff))
  have he : (fun p : ℝ^2 × ℝ ↦ poissonFormula g h p.1 p.2) =
      (fun q : ℝ^3 × ℝ ↦ kirchhoffFormula (g ∘ coordinateProjection)
        (h ∘ coordinateProjection) q.1 q.2) ∘ (fun p ↦ (coordinateInclusion p.1, p.2)) := by
    funext p
    exact poissonFormula_eq_descent (hg.of_le (by norm_num)) hh.continuous p.1 p.2
  rw [he]
  exact hK.comp ((coordinateInclusion.contDiff.comp contDiff_fst).prodMk contDiff_snd)

/-- Each fixed-time Poisson field has the spatial regularity inherited from the joint field. -/
theorem contDiff_two_poissonFormula_slice {g h : ℝ^2 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (t : ℝ) :
    ContDiff ℝ 2 (fun x ↦ poissonFormula g h x t) := by
  have hreg := (contDiff_spaceTimeUncurry_iff _).mp (contDiff_two_poissonFormula hg hh)
  exact hreg.comp (contDiff_id.prodMk contDiff_const)

/-- Poisson's disk formula solves the wave equation at every positive time. -/
theorem waveOperator_poissonFormula {g h : ℝ^2 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) {p : ℝ^3} (hp : 0 < p 0) :
    waveOperator (spaceTimeUncurry (poissonFormula g h)) p = 0 := by
  let x := spatialPartCLM 2 p
  let t := p 0
  have hgK := hg.comp coordinateProjection.contDiff
  have hhK := hh.comp coordinateProjection.contDiff
  have hK := waveOperator_kirchhoffFormula hgK hhK
    (p := timeSpaceCons t (coordinateInclusion x)) (by simpa [t] using hp)
  rw [waveOperator_timeSpaceCons (contDiff_two_kirchhoffFormula hgK hhK)] at hK
  simp only [spaceTimeUncurry, spatialPart_timeSpaceCons, time, timeSpaceCons_zero] at hK
  simp_rw [← poissonFormula_eq_kirchhoffFormula (hg.of_le (by norm_num)) hh.continuous,
    coordinateProjection_coordinateInclusion] at hK
  change deriv (deriv (fun s ↦ poissonFormula g h x s)) t -
    laplacian ((fun y ↦ poissonFormula g h y t) ∘ coordinateProjection)
      (coordinateInclusion x) = 0 at hK
  rw [laplacian_comp_coordinateProjection (contDiff_two_poissonFormula_slice hg hh t),
    coordinateProjection_coordinateInclusion] at hK
  have he := waveOperator_timeSpaceCons (contDiff_two_poissonFormula hg hh) x t
  rw [show timeSpaceCons t x = p from timeSpaceCons_spatialPartCLM p] at he
  rw [he]
  simpa only [spaceTimeUncurry, spatialPart_timeSpaceCons, time, timeSpaceCons_zero] using hK

/-- The total Poisson candidate has the prescribed value on the initial slice. -/
theorem poissonFormula_initial_position (g h : ℝ^2 → ℝ) (x : ℝ^2) :
    spaceTimeUncurry (poissonFormula g h) (timeSpaceCons 0 x) = g x := by
  simp [spaceTimeUncurry, time, poissonFormula]

/-- Differentiating the descended field gives the prescribed initial velocity. -/
theorem partialDeriv_poissonFormula_initial_velocity {g h : ℝ^2 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (x : ℝ^2) :
    (∂[0] (spaceTimeUncurry (poissonFormula g h))) (timeSpaceCons 0 x) = h x := by
  have hgK := hg.comp coordinateProjection.contDiff
  have hhK := hh.comp coordinateProjection.contDiff
  have hK := partialDeriv_kirchhoffFormula_initial_velocity
    (hgK.of_le (by norm_num)) (hhK.of_le (by norm_num)) (coordinateInclusion x)
  rw [PDE.partialDeriv_timeSpaceCons_eq_deriv _ _ _
    ((contDiff_two_kirchhoffFormula hgK hhK).differentiable (by norm_num) _)] at hK
  simp only [spaceTimeUncurry, spatialPart_timeSpaceCons, time, timeSpaceCons_zero,
    Function.comp_apply, coordinateProjection_coordinateInclusion] at hK
  rw [PDE.partialDeriv_timeSpaceCons_eq_deriv _ _ _
    ((contDiff_two_poissonFormula hg hh).differentiable (by norm_num) _)]
  simp only [spaceTimeUncurry, spatialPart_timeSpaceCons, time, timeSpaceCons_zero]
  simp_rw [poissonFormula_eq_descent (hg.of_le (by norm_num)) hh.continuous]
  exact hK

/-- The displacement trace holds jointly in space and time, hence also from positive times. -/
theorem tendsto_poissonFormula_initial_position {g h : ℝ^2 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (x : ℝ^2) :
    Filter.Tendsto (spaceTimeUncurry (poissonFormula g h))
      (nhds (timeSpaceCons 0 x)) (nhds (g x)) := by
  simpa only [ContinuousAt, poissonFormula_initial_position] using
    (contDiff_two_poissonFormula hg hh).continuous.continuousAt (x := timeSpaceCons 0 x)

/-- The velocity trace holds jointly in space and time for the differentiated disk formula. -/
theorem tendsto_partialDeriv_poissonFormula_initial_velocity {g h : ℝ^2 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) (x : ℝ^2) :
    Filter.Tendsto (∂[0] (spaceTimeUncurry (poissonFormula g h)))
      (nhds (timeSpaceCons 0 x)) (nhds (h x)) := by
  have hreg : ContDiff ℝ 1 (∂[0] (spaceTimeUncurry (poissonFormula g h))) :=
    PDE.contDiff_partialDeriv_of_succ (m := 1) (contDiff_two_poissonFormula hg hh)
  simpa only [ContinuousAt, partialDeriv_poissonFormula_initial_velocity hg hh] using
    hreg.continuous.continuousAt (x := timeSpaceCons 0 x)

/-- Poisson's constructed field satisfies the wave residual and both assigned Cauchy data. -/
theorem poissonFormula_satisfiesResidualAssignedCauchyData {g h : ℝ^2 → ℝ}
    (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 2 h) :
    SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := 2) g h)
      (spaceTimeUncurry (poissonFormula g h)) := by
  refine forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial ?_ ?_ ?_
  · exact fun p hp ↦ waveOperator_poissonFormula hg hh hp
  · intro p hp
    have heq := timeSpaceCons_spatialPartCLM p
    rw [hp] at heq
    have hpos := poissonFormula_initial_position g h (spatialPartCLM 2 p)
    rw [heq] at hpos
    simpa only [spatialPartCLM_eq_spatialPart] using hpos
  · intro p hp
    have heq := timeSpaceCons_spatialPartCLM p
    rw [hp] at heq
    have hvel := partialDeriv_poissonFormula_initial_velocity hg hh (spatialPartCLM 2 p)
    rw [heq] at hvel
    simpa only [spatialPartCLM_eq_spatialPart] using hvel

end WaveEquation
