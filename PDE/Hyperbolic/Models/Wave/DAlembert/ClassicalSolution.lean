/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Hyperbolic.Models.Wave.DAlembert.Derivatives
public import PDE.Hyperbolic.Models.Wave.InitialValueProblem

/-!
# The classical one-dimensional d'Alembert solution

We prove the `C²` regularity, wave residual, assigned Cauchy data,
and initial limits that together justify calling the d'Alembert representation

`u(x, t) = ½ (g(x + t) + g(x - t)) + ½ ∫_{x-t}^{x+t} h(y) dy`

a classical solution of the one-dimensional wave equation with `u(·, 0) = g`
and `u_t(·, 0) = h`. This is Evans, §2.4.1, Theorem 1 (solution of the
wave equation for `n = 1`), under his hypotheses `g ∈ C²`, `h ∈ C¹`.

## Main results

* `dAlembertSolution1D` (from `DAlembert.Formula`): the field on spacetime `ℝ^2`,
  with `xt 0 = t` and `xt 1 = x`.
* `contDiff_two_dAlembertSolution1D`: it is `C²` on all of spacetime.
* `dAlembertSolution1D_satisfiesResidualAssignedCauchyData`: it satisfies the
  residual `u_tt - u_xx = 0` for `t > 0` and the two exact initial identities.
* `tendsto_dAlembertSolution1D_initial_position`,
  `tendsto_partialDeriv_dAlembertSolution1D_initial_velocity`: the joint
  spacetime limits at the initial slice.

## Implementation notes

The initial data are functions on `ℝ^1`; they are converted to functions on
`ℝ` through `EuclideanSpace.single 0`, and the regularity hypotheses are
stated for these scalar reparametrizations.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1, Theorem 1.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (SatisfiesPDEProblem)

namespace WaveEquation

open PDE.Common

/-- D'Alembert's formula satisfies the wave equation at every spacetime point. -/
theorem waveOperator_dAlembertFormula
    (g h : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h) (p : ℝ^2) :
    waveOperator (n := 1) (fun q ↦ dAlembertFormula g h (q 1) (q 0)) p = 0 := by
  simp only [waveOperator, Fin.sum_univ_one]
  change (∂[0] (fun q ↦ (∂[0] (fun r : ℝ^2 ↦ dAlembertFormula g h (r 1) (r 0))) q)) p -
    (∂[1] (fun q ↦ (∂[1] (fun r : ℝ^2 ↦ dAlembertFormula g h (r 1) (r 0))) q)) p = 0
  rw [partialDeriv2_dAlembert_time g h hg hh, partialDeriv2_dAlembert_space g h hg hh, sub_self]

/-- On the initial slice, the time derivative of d'Alembert's field is the prescribed velocity. -/
theorem dAlembert_satisfies_initial_vel (g h : ℝ^1 → ℝ)
    (hg : ContDiff ℝ 2 (fun x : ℝ ↦ g (EuclideanSpace.single (0 : Fin 1) x)))
    (hh : ContDiff ℝ 1 (fun x : ℝ ↦ h (EuclideanSpace.single (0 : Fin 1) x))) (x0 : ℝ^1) :
    (∂[(0 : Fin 2)] (dAlembertSolution1D g h)) (timeSpaceCons 0 x0) = h x0 := by
  have hx : EuclideanSpace.single (0 : Fin 1) (x0 0) = x0 := by
    ext i
    fin_cases i
    simp
  unfold dAlembertSolution1D
  rw [partialDeriv_dAlembert_time _ _ hg hh]
  have hspace : timeSpaceCons 0 x0 (1 : Fin 2) = x0 0 := timeSpaceCons_succ 0 x0 (0 : Fin 1)
  simp only [one_div, Fin.isValue, hspace, timeSpaceCons_zero, add_zero, sub_zero, sub_self,
    mul_zero, hx, zero_add]
  ring

/-- D'Alembert's field is `C²` in spacetime for `C²` displacement and `C¹` velocity. -/
theorem contDiff_two_dAlembertSolution1D (g h : ℝ^1 → ℝ)
    (hg : ContDiff ℝ 2 (fun x : ℝ ↦ g (EuclideanSpace.single (0 : Fin 1) x)))
    (hh : ContDiff ℝ 1 (fun x : ℝ ↦ h (EuclideanSpace.single (0 : Fin 1) x))) :
    ContDiff ℝ 2 (dAlembertSolution1D g h) :=
  contDiff_two_dAlembertFormula _ _ hg hh

/-- D'Alembert's formula satisfies the one-dimensional wave residual and both assigned Cauchy
data. Its classical regularity is supplied by `contDiff_two_dAlembertSolution1D`. -/
theorem dAlembertSolution1D_satisfiesResidualAssignedCauchyData (g h : ℝ^1 → ℝ)
    (hg : ContDiff ℝ 2 (fun x : ℝ ↦ g (EuclideanSpace.single (0 : Fin 1) x)))
    (hh : ContDiff ℝ 1 (fun x : ℝ ↦ h (EuclideanSpace.single (0 : Fin 1) x))) :
    SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := 1) g h)
      (dAlembertSolution1D g h) := by
  refine forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial ?_ ?_ ?_
  · exact fun p _ ↦ waveOperator_dAlembertFormula _ _ hg hh p
  · intro p hp
    have heq := timeSpaceCons_spatialPartCLM p
    rw [hp] at heq
    simpa only [heq] using dAlembert_satisfies_initial_pos g h (spatialPartCLM 1 p)
  · intro p hp
    have heq := timeSpaceCons_spatialPartCLM p
    rw [hp] at heq
    simpa only [heq] using dAlembert_satisfies_initial_vel g h hg hh (spatialPartCLM 1 p)

/-- The d'Alembert field converges jointly in spacetime to its initial displacement. -/
theorem tendsto_dAlembertSolution1D_initial_position (g h : ℝ^1 → ℝ)
    (hg : ContDiff ℝ 2 (fun x : ℝ ↦ g (EuclideanSpace.single (0 : Fin 1) x)))
    (hh : ContDiff ℝ 1 (fun x : ℝ ↦ h (EuclideanSpace.single (0 : Fin 1) x))) (x0 : ℝ^1) :
    Filter.Tendsto (dAlembertSolution1D g h) (nhds (timeSpaceCons 0 x0)) (nhds (g x0)) := by
  simpa only [ContinuousAt, dAlembert_satisfies_initial_pos] using
    (contDiff_two_dAlembertSolution1D g h hg hh).continuous.continuousAt (x := timeSpaceCons 0 x0)

/-- The time derivative converges jointly in spacetime to the initial velocity. -/
theorem tendsto_partialDeriv_dAlembertSolution1D_initial_velocity (g h : ℝ^1 → ℝ)
    (hg : ContDiff ℝ 2 (fun x : ℝ ↦ g (EuclideanSpace.single (0 : Fin 1) x)))
    (hh : ContDiff ℝ 1 (fun x : ℝ ↦ h (EuclideanSpace.single (0 : Fin 1) x))) (x0 : ℝ^1) :
    Filter.Tendsto (fun p ↦ (∂[(0 : Fin 2)] (dAlembertSolution1D g h)) p)
      (nhds (timeSpaceCons 0 x0)) (nhds (h x0)) := by
  have hregular : ContDiff ℝ 1 (fun p ↦ (∂[(0 : Fin 2)] (dAlembertSolution1D g h)) p) :=
    PDE.contDiff_partialDeriv_of_succ (m := 1) (i := (0 : Fin 2))
      (contDiff_two_dAlembertSolution1D g h hg hh)
  simpa only [ContinuousAt, dAlembert_satisfies_initial_vel g h hg hh] using
    hregular.continuous.continuousAt (x := timeSpaceCons 0 x0)

end WaveEquation
