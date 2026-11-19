/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.EvenDimensions.Representation
public import PDE.Analysis.Calculus.CoordinateProjection

/-!
# Classical waves in every even dimension

For dimension `2k+2`, `C^(k+3)` displacement and `C^(k+2)` velocity data
produce the weighted ball formula (38) of Evans, §2.4.1(e), at positive time; this is his
Theorem 3 with `m = k + 2`. Its signed extension
is jointly `C²`, satisfies the wave equation and both assigned initial data,
and has both joint Cauchy traces.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1(e), equation (38) and Theorem 3.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (laplacian SatisfiesPDEProblem)

namespace WaveEquation

open PDE.Analysis PDE.Common

/-- The descended wave satisfies the PDE after the proved center independence
removes the extra spatial second derivative. -/
theorem waveOperator_evenWaveSolution (k : ℕ) {g h : ℝ^(2 * k + 2) → ℝ} (hg : ContDiff ℝ (k + 3) g)
    (hh : ContDiff ℝ (k + 2) h) {p : ℝ^(2 * k + 2 + 1)} (hp : 0 < p 0) :
    waveOperator (evenWaveSolution k g h) p = 0 := by
  let x := spatialPartCLM (2 * k + 2) p
  let t := p 0
  have hg₁ : ContDiff ℝ (k + 1) g := hg.of_le (by norm_cast; omega)
  have hgO := hg.comp coordinateProjection.contDiff
  have hhO := hh.comp coordinateProjection.contDiff
  have hO := waveOperator_oddWaveSolution k hgO hhO
    (p := timeSpaceCons t (coordinateInclusion x)) (by simpa [t] using hp)
  rw [waveOperator_timeSpaceCons (contDiff_two_oddWaveSolution k hgO hhO)] at hO
  simp_rw [oddWaveSolution_coordinateProjection_center k hg₁,
    coordinateProjection_coordinateInclusion] at hO
  change deriv (deriv (fun s ↦ evenWaveSolution k g h (timeSpaceCons s x))) t -
    laplacian ((fun y ↦ evenWaveSolution k g h (timeSpaceCons t y)) ∘
      coordinateProjection) (coordinateInclusion x) = 0 at hO
  rw [laplacian_comp_coordinateProjection (contDiff_two_evenWaveSolution_slice k hg hh t),
    coordinateProjection_coordinateInclusion] at hO
  have he := waveOperator_timeSpaceCons (contDiff_two_evenWaveSolution k hg hh) x t
  rw [show timeSpaceCons t x = p from timeSpaceCons_spatialPartCLM p] at he
  rw [he]
  exact hO

/-- The signed extension has the prescribed initial displacement. -/
theorem evenWaveSolution_initial_position (k : ℕ) {g h : ℝ^(2 * k + 2) → ℝ}
    (hg : ContDiff ℝ (k + 1) g) (x : ℝ^(2 * k + 2)) :
    evenWaveSolution k g h (timeSpaceCons 0 x) = g x := by
  rw [evenWaveSolution_timeSpaceCons,
    oddWaveSolution_initial_position k (hg.comp coordinateProjection.contDiff)]
  simp

/-- The time-coordinate derivative has the assigned initial velocity. -/
theorem partialDeriv_evenWaveSolution_initial_velocity (k : ℕ) {g h : ℝ^(2 * k + 2) → ℝ}
    (hg : ContDiff ℝ (k + 3) g) (hh : ContDiff ℝ (k + 2) h) (x : ℝ^(2 * k + 2)) :
    (∂[0] (evenWaveSolution k g h)) (timeSpaceCons 0 x) = h x := by
  have hgO := hg.comp coordinateProjection.contDiff
  have hhO := hh.comp coordinateProjection.contDiff
  have hO := partialDeriv_oddWaveSolution_initial_velocity k
    (hgO.of_le (by norm_cast; omega)) (hhO.of_le (by norm_cast; omega)) (coordinateInclusion x)
  rw [PDE.partialDeriv_timeSpaceCons_eq_deriv _ _ _
    ((contDiff_two_oddWaveSolution k hgO hhO).differentiable (by norm_num) _)] at hO
  rw [PDE.partialDeriv_timeSpaceCons_eq_deriv _ _ _
    ((contDiff_two_evenWaveSolution k hg hh).differentiable (by norm_num) _)]
  simp only [Function.comp_apply, coordinateProjection_coordinateInclusion] at hO
  simpa only [evenWaveSolution_timeSpaceCons] using hO

/-- The formula satisfies the wave residual and both assigned Cauchy data. -/
theorem evenWaveSolution_satisfiesResidualAssignedCauchyData (k : ℕ) {g h : ℝ^(2 * k + 2) → ℝ}
    (hg : ContDiff ℝ (k + 3) g) (hh : ContDiff ℝ (k + 2) h) :
    SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := 2 * k + 2) g h)
      (evenWaveSolution k g h) := by
  refine forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial ?_ ?_ ?_
  · exact fun p hp ↦ waveOperator_evenWaveSolution k hg hh hp
  · intro p hp
    have he := timeSpaceCons_spatialPartCLM p
    rw [hp] at he
    have hi := evenWaveSolution_initial_position k
      (hg.of_le (by norm_cast; omega)) (h := h) (spatialPartCLM (2 * k + 2) p)
    rwa [he] at hi
  · intro p hp
    have he := timeSpaceCons_spatialPartCLM p
    rw [hp] at he
    have hi := partialDeriv_evenWaveSolution_initial_velocity k hg hh (spatialPartCLM (2 * k + 2) p)
    rwa [he] at hi

/-- The displacement converges jointly in space and time to the prescribed datum.
In particular, this gives the limit through positive times in Theorem 3(iii) of Evans, §2.4.1. -/
theorem tendsto_evenWaveSolution_initial_position (k : ℕ) {g h : ℝ^(2 * k + 2) → ℝ}
    (hg : ContDiff ℝ (k + 3) g) (hh : ContDiff ℝ (k + 2) h) (x : ℝ^(2 * k + 2)) :
    Filter.Tendsto (evenWaveSolution k g h) (nhds (timeSpaceCons 0 x)) (nhds (g x)) := by
  simpa only [ContinuousAt, evenWaveSolution_initial_position k
    (hg.of_le (by norm_cast; omega))] using
      (contDiff_two_evenWaveSolution k hg hh).continuous.continuousAt (x := timeSpaceCons 0 x)

/-- The time derivative has the joint initial velocity trace. -/
theorem tendsto_partialDeriv_evenWaveSolution_initial_velocity (k : ℕ) {g h : ℝ^(2 * k + 2) → ℝ}
    (hg : ContDiff ℝ (k + 3) g) (hh : ContDiff ℝ (k + 2) h) (x : ℝ^(2 * k + 2)) :
    Filter.Tendsto (∂[0] (evenWaveSolution k g h)) (nhds (timeSpaceCons 0 x)) (nhds (h x)) := by
  have hreg := PDE.contDiff_partialDeriv_of_succ (m := 1) (i := 0)
    (contDiff_two_evenWaveSolution k hg hh)
  simpa only [ContinuousAt, partialDeriv_evenWaveSolution_initial_velocity k hg hh] using
    hreg.continuous.continuousAt (x := timeSpaceCons 0 x)

/-- Any other globally `C²` Cauchy solution agrees with the constructed field
at nonnegative times. -/
theorem eq_evenWaveSolution_of_satisfiesResidualAssignedCauchyData (k : ℕ) {g h : ℝ^(2 * k + 2) → ℝ}
    (hg : ContDiff ℝ (k + 3) g) (hh : ContDiff ℝ (k + 2) h) {u : ℝ^(2 * k + 2 + 1) → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hsol : SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := 2 * k + 2) g h) u)
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ^(2 * k + 2)) :
    u (timeSpaceCons t x) = evenWaveSolution k g h (timeSpaceCons t x) := by
  have : Fact (0 < 2 * k + 2) := ⟨by omega⟩
  exact eq_on_nonnegative_time_of_satisfiesResidualAssignedCauchyData hu
    (contDiff_two_evenWaveSolution k hg hh) hsol
    (evenWaveSolution_satisfiesResidualAssignedCauchyData k hg hh) ht x

end WaveEquation
