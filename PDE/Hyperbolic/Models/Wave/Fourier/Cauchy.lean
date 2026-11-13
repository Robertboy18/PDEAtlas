/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import PDE.Hyperbolic.Models.Wave.DAlembert.ClassicalSolution
public import PDE.Hyperbolic.Models.Wave.Fourier.Representation

/-!
# Classical wave solutions given by Fourier inversion

The cosine/sine Fourier formula on the real line is a classical `C²` solution
of the unit-speed wave equation. We prove the wave residual, both assigned
initial data, and their joint spacetime traces by identifying the field with
d'Alembert's solution.

The hypotheses are `C²` displacement and `C¹` velocity, with each datum and its
Fourier transform integrable. Real Schwartz data satisfy these assumptions.
The field is the case `n = 1` of the Fourier representation (26) of Evans, §4.3.1, Example 4,
and through d'Alembert's formula (8) we obtain the conclusions of Evans, §2.4.1(a), Theorem 1.
The Schwartz-data case in every dimension is `Fourier.Schwartz.Cauchy`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §2.4.1(a), equation (8) and Theorem 1; §4.3.1,
  Example 4, equations (24)-(26).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (SatisfiesPDEProblem)
open MeasureTheory PDE.Common
open scoped FourierTransform SchwartzMap Topology

namespace WaveEquation

/-- The real spacetime field of the one-dimensional cosine/sine Fourier solution.
Time is coordinate zero and position is coordinate one, as in `dAlembertSolution1D`. -/
def fourierSolution1D (g h : ℝ → ℝ) (p : ℝ^2) : ℝ :=
  (fourierSolution (fun y ↦ (g y : ℂ)) (fun y ↦ (h y : ℂ)) (p 1) (p 0)).re

section IntegrableData

variable {g h : ℝ → ℝ}
  (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 1 h)
  (hgi : Integrable g) (hhi : Integrable h)
  (hfg : Integrable (𝓕 (fun y ↦ (g y : ℂ))))
  (hfh : Integrable (𝓕 (fun y ↦ (h y : ℂ))))

include hg hh hgi hhi hfg hfh

private theorem fourierSolution1D_eq :
    fourierSolution1D g h = dAlembertSolution1D (fun x ↦ g (x 0)) (fun x ↦ h (x 0)) := by
  funext p
  have H := congrArg Complex.re
    (fourierSolution_ofReal_eq_dAlembertFormula hgi hhi hg.continuous hh.continuous
      hfg hfh (p 1) (p 0))
  simpa only [fourierSolution1D, dAlembertSolution1D, PiLp.single_apply,
    ite_true, Complex.ofReal_re] using H

/-- The inverse Fourier wave field is `C²` on all of spacetime. -/
theorem contDiff_two_fourierSolution1D : ContDiff ℝ 2 (fourierSolution1D g h) := by
  rw [fourierSolution1D_eq hg hh hgi hhi hfg hfh]
  apply contDiff_two_dAlembertSolution1D
  · simpa using hg
  · simpa using hh

/-- The cosine/sine Fourier field solves the wave equation at every point,
including the initial slice. -/
theorem waveOperator_fourierSolution1D (p : ℝ^2) :
    waveOperator (n := 1) (fourierSolution1D g h) p = 0 := by
  rw [fourierSolution1D_eq hg hh hgi hhi hfg hfh]
  unfold dAlembertSolution1D
  simpa only [PiLp.single_apply, ite_true] using! waveOperator_dAlembertFormula g h hg hh p

/-- The Fourier field satisfies the wave residual and both assigned Cauchy data.
The separate regularity theorem supplies its classical `C²` interpretation. -/
theorem fourierSolution1D_satisfiesResidualAssignedCauchyData :
    SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := 1) (fun x ↦ g (x 0))
      (fun x ↦ h (x 0))) (fourierSolution1D g h) := by
  rw [fourierSolution1D_eq hg hh hgi hhi hfg hfh]
  apply dAlembertSolution1D_satisfiesResidualAssignedCauchyData
  · simpa using hg
  · simpa using hh

/-- The inverse Fourier wave field approaches its initial displacement jointly
in space and time. -/
theorem tendsto_fourierSolution1D_initial_position (x : ℝ^1) :
    Filter.Tendsto (fourierSolution1D g h) (𝓝 (timeSpaceCons 0 x)) (𝓝 (g (x 0))) := by
  rw [fourierSolution1D_eq hg hh hgi hhi hfg hfh]
  apply tendsto_dAlembertSolution1D_initial_position
  · simpa using hg
  · simpa using hh

/-- The time derivative of the Fourier field approaches the initial velocity
jointly in space and time. -/
theorem tendsto_partialDeriv_fourierSolution1D_initial_velocity (x : ℝ^1) :
    Filter.Tendsto (∂[(0 : Fin 2)] (fourierSolution1D g h))
      (𝓝 (timeSpaceCons 0 x)) (𝓝 (h (x 0))) := by
  rw [fourierSolution1D_eq hg hh hgi hhi hfg hfh]
  apply tendsto_partialDeriv_dAlembertSolution1D_initial_velocity
  · simpa using hg
  · simpa using hh

end IntegrableData

/-- Real Schwartz displacement and velocity give a Fourier solution satisfying the
wave residual and both assigned initial data, without separate integrability assumptions. -/
theorem fourierSolution1D_schwartz_satisfiesResidualAssignedCauchyData (g h : 𝓢(ℝ, ℝ)) :
    SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem (n := 1) (fun x ↦ g (x 0))
      (fun x ↦ h (x 0))) (fourierSolution1D g h) := by
  apply fourierSolution1D_satisfiesResidualAssignedCauchyData
    (g.smooth 2) (h.smooth 1) g.integrable h.integrable
  · exact (𝓕 (SchwartzMap.postcompCLM Complex.ofRealCLM g)).integrable
  · exact (𝓕 (SchwartzMap.postcompCLM Complex.ofRealCLM h)).integrable

end WaveEquation
