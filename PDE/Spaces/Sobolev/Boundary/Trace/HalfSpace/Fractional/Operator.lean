/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Fractional.WholeSpaceCompatibility
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.TraceSpace
public import PDE.Spaces.Sobolev.Extension.HalfSpace.FirstOrder.Operator
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# The half-space trace into real fractional Sobolev space

Reflection extension and the whole-space Fourier estimate define a
bounded trace from the half-space `H¹` space into real `H^{1/2}`.
Its physical `L²` representative is the trace. Restricting the
explicit Fourier lifting gives a bounded right inverse, so the trace is onto.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Sobolev

namespace SobolevSpace.Trace.HalfSpace.Fractional

open SobolevSpace.Fractional SobolevSpace.Fractional.Trace GraphSpace

/-- Restriction is a left inverse of the already proved reflection extension. -/
theorem restrict_reflectionExtension (n : ℕ) (u : H¹(HalfSpace.upper (n + 1))) :
    restrictCLM (k := 1) (p := 2)
      (HalfSpace.measurableSet_upper (n := n + 1)) (Set.subset_univ _)
        (Extension.GraphSpace.HalfSpace.extendCLM (n := n + 1) (p := 2) u) = u := by
  apply WkpSpaceOn.ext_of_base_ae (HalfSpace.isOpen_upper (n := n + 1))
  exact (restrictCLM_apply_ae (HalfSpace.measurableSet_upper (n := n + 1))
    (Set.subset_univ _) _ (baseIndex (n + 1) 1)).trans
      ((Extension.GraphSpace.HalfSpace.operator (n := n + 1) (p := 2)).agree_ae u)

/-- The bounded fractional trace on the half-space `H¹` space. -/
def fractionalTrace (n : ℕ) : H¹(HalfSpace.upper (n + 1)) →L[ℝ] H^{1 / 2}(ℝ^n; ℝ) :=
  (wholeSpaceTraceRealCLM n).comp
    ((h1GraphEquiv (n + 1)).symm.toContinuousLinearMap.comp
      (Extension.GraphSpace.HalfSpace.extendCLM (n := n + 1) (p := 2)))

/-- The explicit bounded lifting from real fractional boundary data into half-space `H¹`. -/
def fractionalLifting (n : ℕ) : H^{1 / 2}(ℝ^n; ℝ) →L[ℝ] H¹(HalfSpace.upper (n + 1)) :=
  (restrictCLM (k := 1) (p := 2)
    (HalfSpace.measurableSet_upper (n := n + 1)) (Set.subset_univ _)).comp
      ((h1GraphEquiv (n + 1)).toContinuousLinearMap.comp (wholeSpaceLiftingRealCLM n))

/-- The Fourier-defined fractional trace has exactly the physical `L²` boundary value. -/
theorem physical_fractionalTrace (n : ℕ) (u : H¹(HalfSpace.upper (n + 1))) :
    HsSpaceReal.toL2FunCLM n (by norm_num : (0 : ℝ) ≤ 1 / 2) (fractionalTrace n u) =
      trace n u := by
  have h := trace_restrict_toWkpSpace n
    ((h1GraphEquiv (n + 1)).symm
      (Extension.GraphSpace.HalfSpace.extendCLM (n := n + 1) (p := 2) u))
  rw [ContinuousLinearEquiv.apply_symm_apply, restrict_reflectionExtension] at h
  exact h.symm

/-- Restricting a whole-space element commutes with fractional trace. -/
theorem fractionalTrace_restrict (n : ℕ) (u : H^{1}(ℝ^(n + 1); ℝ)) :
    fractionalTrace n (restrictCLM (k := 1) (p := 2)
      (HalfSpace.measurableSet_upper (n := n + 1)) (Set.subset_univ _)
        (h1GraphEquiv (n + 1) u)) = wholeSpaceTraceRealCLM n u := by
  apply HsSpaceReal.toL2FunCLM_injective (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [physical_fractionalTrace, trace_restrict_toWkpSpace]

/-- The half-space lifting is a right inverse of the fractional trace. -/
theorem fractionalTrace_fractionalLifting (n : ℕ) (v : H^{1 / 2}(ℝ^n; ℝ)) :
    fractionalTrace n (fractionalLifting n v) = v := by
  change fractionalTrace n (restrictCLM (HalfSpace.measurableSet_upper (n := n + 1))
    (Set.subset_univ _) (h1GraphEquiv (n + 1)
    (wholeSpaceLiftingRealCLM n v))) = v
  rw [fractionalTrace_restrict, wholeSpaceTraceRealCLM_wholeSpaceLiftingRealCLM]

/-- Every element of real `H^{1/2}` is the boundary trace of a half-space `H¹` function. -/
theorem fractionalTrace_surjective (n : ℕ) : Function.Surjective (fractionalTrace n) :=
  fun v ↦ ⟨fractionalLifting n v, fractionalTrace_fractionalLifting n v⟩

/-- Trace bound obtained from the Fourier estimate and the reflection and
integer-order equivalence. Every factor is the norm of a constructed bounded map. -/
theorem norm_fractionalTrace_le (n : ℕ) (u : H¹(HalfSpace.upper (n + 1))) :
    ‖fractionalTrace n u‖ ≤
      (Real.sqrt Real.pi * ‖(h1GraphEquiv (n + 1)).symm.toContinuousLinearMap‖ *
        ‖Extension.GraphSpace.HalfSpace.extendCLM (n := n + 1) (p := 2)‖) * ‖u‖ := by
  let E := Extension.GraphSpace.HalfSpace.extendCLM (n := n + 1) (p := 2)
  let I := (h1GraphEquiv (n + 1)).symm.toContinuousLinearMap
  calc
    ‖fractionalTrace n u‖ ≤ Real.sqrt Real.pi * ‖I (E u)‖ :=
      norm_wholeSpaceTraceRealCLM_apply_le n _
    _ ≤ Real.sqrt Real.pi * (‖I‖ * (‖E‖ * ‖u‖)) :=
      mul_le_mul_of_nonneg_left
        ((I.le_opNorm _).trans (mul_le_mul_of_nonneg_left (E.le_opNorm u) (norm_nonneg I)))
        (Real.sqrt_nonneg _)
    _ = _ := by simp only [I, E, mul_assoc]

/-- The explicitly constructed half-space lifting obeys the Fourier lifting bound,
followed by the integer Bessel–graph comparison; restriction is contractive. -/
theorem norm_fractionalLifting_le (n : ℕ) (v : H^{1 / 2}(ℝ^n; ℝ)) :
    ‖fractionalLifting n v‖ ≤
      (‖(h1GraphEquiv (n + 1)).toContinuousLinearMap‖ * (Real.sqrt Real.pi)⁻¹) * ‖v‖ := by
  calc
    ‖fractionalLifting n v‖ ≤ ‖h1GraphEquiv (n + 1) (wholeSpaceLiftingRealCLM n v)‖ :=
      norm_restrictCLM_apply_le (HalfSpace.measurableSet_upper (n := n + 1))
        (Set.subset_univ _) _
    _ ≤ ‖(h1GraphEquiv (n + 1)).toContinuousLinearMap‖ *
        ‖wholeSpaceLiftingRealCLM n v‖ :=
      (h1GraphEquiv (n + 1)).toContinuousLinearMap.le_opNorm _
    _ = _ := by rw [norm_wholeSpaceLiftingRealCLM, mul_assoc]

/-- The fractional trace and the physical trace have the same kernel. -/
theorem ker_fractionalTrace (n : ℕ) : (fractionalTrace n).ker = (trace n).ker := by
  ext u
  change fractionalTrace n u = 0 ↔ trace n u = 0
  rw [← physical_fractionalTrace]
  exact ((HsSpaceReal.toL2FunCLM_injective
    (by norm_num : (0 : ℝ) ≤ 1 / 2)).eq_iff' (map_zero _)).symm

end SobolevSpace.Trace.HalfSpace.Fractional
