/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Common.Euclidean.SpaceTime
public import PDE.Hyperbolic.Models.Wave.Fourier.Schwartz.Regularity
public import PDE.Hyperbolic.Models.Wave.InitialValueProblem

/-!
# All-dimensional classical Fourier wave solutions from Schwartz data

Real Schwartz displacement and velocity determine a joint C² field by inverse
Fourier transformation of the cosine/sinc multipliers. Linear coordinate
conversion and real projection preserve the Hessian equation. The resulting
field satisfies the canonical unit-speed wave operator at every time, both
assigned Cauchy data, and their joint spacetime traces.

This is the homogeneous linear wave Cauchy problem on the whole space, in
arbitrary finite dimension including zero.

In the notation of Evans, §4.3.1, Example 4, `realSolution g h` is the inverse Fourier transform
of the solution (26) of (25), `û = ĝ cos(t|y|) + ĥ sin(t|y|)/|y|`. Mathlib's transform has `2π`
in the exponent, so the multipliers become `cos(2πt|ξ|)` and `sin(2πt|ξ|)/(2π|ξ|)`. For Schwartz
data we prove that this field is `C²` and solves the initial value problem (24).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §4.3.1, Example 4, equations (24)-(26).
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open PDE (SatisfiesPDEProblem)
open scoped Topology

namespace WaveEquation.Fourier

open PDE.Common WaveEquation

variable {n : ℕ}

/-- Real Schwartz data give a field in the canonical time-first spacetime coordinates. -/
def realSolution (g h : SchwartzMap (ℝ^n) ℝ) : ℝ^(n + 1) → ℝ :=
  Complex.reCLM ∘ cauchySolution (SchwartzMap.postcompCLM Complex.ofRealCLM g)
    (SchwartzMap.postcompCLM Complex.ofRealCLM h) ∘ timeSpaceContinuousLinearEquiv n

/-- The Fourier field is C² jointly in all canonical spacetime coordinates. -/
theorem contDiff_two_realSolution (g h : SchwartzMap (ℝ^n) ℝ) :
    ContDiff ℝ 2 (realSolution g h) :=
  Complex.reCLM.contDiff.comp ((contDiff_two_cauchySolution _ _).comp
    (timeSpaceContinuousLinearEquiv n).contDiff)

/-- At time zero the Fourier field equals the assigned real displacement. -/
theorem realSolution_initial_position (g h : SchwartzMap (ℝ^n) ℝ) (x : ℝ^n) :
    realSolution g h (timeSpaceCons 0 x) = g x := by
  simp [realSolution, Function.comp_def, PDE.time, cauchySolution_initial_position]

/-- The canonical time derivative equals the assigned real velocity at time zero. -/
theorem partialDeriv_realSolution_initial_velocity (g h : SchwartzMap (ℝ^n) ℝ)
    (x : ℝ^n) : (∂[(0 : Fin (n + 1))] (realSolution g h)) (timeSpaceCons 0 x) = h x := by
  let u := cauchySolution (SchwartzMap.postcompCLM Complex.ofRealCLM g)
    (SchwartzMap.postcompCLM Complex.ofRealCLM h)
  let L := (timeSpaceContinuousLinearEquiv n).toContinuousLinearMap
  have hu : ContDiff ℝ 2 u := contDiff_two_cauchySolution _ _
  have htime : L (EuclideanSpace.single (0 : Fin (n + 1)) 1) = (1, 0) := by
    change timeSpaceContinuousLinearEquiv n (EuclideanSpace.single (0 : Fin (n + 1)) 1) = (1, 0)
    rw [timeSpaceContinuousLinearEquiv_apply,
      ← spatialPartCLM_eq_spatialPart, spatialPartCLM_single_zero]
    simp [PDE.time]
  change fderiv ℝ (Complex.reCLM ∘ u ∘ L) (timeSpaceCons 0 x) _ = _
  rw [fderiv_comp _ Complex.reCLM.differentiableAt
    ((hu.differentiable (by norm_num)).differentiableAt.comp _ L.differentiableAt),
    fderiv_comp _ ((hu.differentiable (by norm_num)).differentiableAt) L.differentiableAt]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, htime]
  change (fderiv ℝ u (0, x) (1, 0)).re = h x
  rw [cauchySolution_initial_velocity]
  rfl

/-- The constructed Fourier field solves the wave equation at every spacetime point. -/
theorem waveOperator_realSolution (g h : SchwartzMap (ℝ^n) ℝ) (p : ℝ^(n + 1)) :
    waveOperator (realSolution g h) p = 0 := by
  let u := cauchySolution (SchwartzMap.postcompCLM Complex.ofRealCLM g)
    (SchwartzMap.postcompCLM Complex.ofRealCLM h)
  let L := (timeSpaceContinuousLinearEquiv n).toContinuousLinearMap
  have hu : ContDiff ℝ 2 u := contDiff_two_cauchySolution _ _
  have hsecond (i : Fin (n + 1)) : (∂[i] (∂[i] (realSolution g h))) p = (fderiv ℝ (fderiv ℝ u) (L p)
          (L (EuclideanSpace.single i 1)) (L (EuclideanSpace.single i 1))).re := by
    change (∂[i] (∂[i] (Complex.reCLM ∘ (u ∘ L)))) p = _
    rw [PDE.secondPartialDeriv_eq_iteratedFDeriv_apply i i
      (Complex.reCLM.contDiff.comp (hu.comp L.contDiff)).contDiffAt,
      Complex.reCLM.iteratedFDeriv_comp_left (hu.comp L.contDiff).contDiffAt le_rfl,
      L.iteratedFDeriv_comp_right hu p le_rfl]
    simp [ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_two_apply]
  have htime : L (EuclideanSpace.single (0 : Fin (n + 1)) 1) = (1, 0) := by
    change timeSpaceContinuousLinearEquiv n (EuclideanSpace.single (0 : Fin (n + 1)) 1) = (1, 0)
    rw [timeSpaceContinuousLinearEquiv_apply,
      ← spatialPartCLM_eq_spatialPart, spatialPartCLM_single_zero]
    simp [PDE.time]
  have hspace (i : Fin n) :
      L (EuclideanSpace.single i.succ 1) = (0, EuclideanSpace.single i 1) := by
    change timeSpaceContinuousLinearEquiv n
      (EuclideanSpace.single i.succ 1) = (0, EuclideanSpace.single i 1)
    rw [timeSpaceContinuousLinearEquiv_apply,
      ← spatialPartCLM_eq_spatialPart, spatialPartCLM_single_succ]
    simp [PDE.time]
  have hw := congrArg Complex.reCLM (cauchySolution_waveTrace
    (SchwartzMap.postcompCLM Complex.ofRealCLM g)
    (SchwartzMap.postcompCLM Complex.ofRealCLM h) (L p))
  simpa only [waveOperator, hsecond, htime, hspace, waveTrace_apply,
    map_sub, map_sum, map_zero, Complex.reCLM_apply] using hw

/-- The Fourier field satisfies the homogeneous wave residual and both assigned Cauchy data. -/
theorem realSolution_satisfiesResidualAssignedCauchyData (g h : SchwartzMap (ℝ^n) ℝ) :
    SatisfiesPDEProblem (waveResidualAssignedCauchyDataProblem g h) (realSolution g h) := by
  apply forcedWaveResidualAssignedCauchyDataProblem.of_residual_initial
  · exact fun p _ ↦ waveOperator_realSolution g h p
  · intro p hp
    have heq : p = timeSpaceCons 0 (spatialPartCLM n p) := by
      rw [← hp, timeSpaceCons_spatialPartCLM]
    rw [heq, realSolution_initial_position, spatialPartCLM_timeSpaceCons]
  · intro p hp
    have heq : p = timeSpaceCons 0 (spatialPartCLM n p) := by
      rw [← hp, timeSpaceCons_spatialPartCLM]
    rw [heq, partialDeriv_realSolution_initial_velocity, spatialPartCLM_timeSpaceCons]

/-- The field converges to its assigned displacement jointly in space and time. -/
theorem tendsto_realSolution_initial_position (g h : SchwartzMap (ℝ^n) ℝ) (x : ℝ^n) :
    Filter.Tendsto (realSolution g h) (𝓝 (timeSpaceCons 0 x)) (𝓝 (g x)) := by
  simpa only [ContinuousAt, realSolution_initial_position] using
    (contDiff_two_realSolution g h).continuous.continuousAt (x := timeSpaceCons 0 x)

/-- The time derivative converges to the assigned velocity jointly in space and time. -/
theorem tendsto_partialDeriv_realSolution_initial_velocity (g h : SchwartzMap (ℝ^n) ℝ) (x : ℝ^n) :
    Filter.Tendsto (∂[(0 : Fin (n + 1))] (realSolution g h)) (𝓝 (timeSpaceCons 0 x)) (𝓝 (h x)) := by
  simpa only [ContinuousAt, partialDeriv_realSolution_initial_velocity] using
    (PDE.contDiff_partialDeriv_of_succ (m := 1) (i := (0 : Fin (n + 1)))
      (contDiff_two_realSolution g h)).continuous.continuousAt (x := timeSpaceCons 0 x)

end WaveEquation.Fourier
