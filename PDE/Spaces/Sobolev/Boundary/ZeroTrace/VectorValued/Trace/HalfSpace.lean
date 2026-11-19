/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Extension.VectorValued.ZeroBoundary.Space
public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.ZeroExtension

/-!
# Vanishing half-space trace of the supported smooth closure

An interior test function vanishes on the flat boundary. Continuity of the trace passes
this identity to its Sobolev closure, for every finite exponent at least one.
The extension from this closure agrees with the extension on the trace kernel.
-/

@[expose] public noncomputable section

open MeasureTheory TopologicalSpace
open scoped Distributions ENNReal Sobolev

namespace SobolevSpace.VectorValued.Trace.HalfSpace

open GraphSpace SobolevSpace.Trace.HalfSpace

variable {n : ℕ} {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Interior Banach-valued test functions have zero half-space trace. -/
theorem traceLp_testFunction_eq_zero (hp : 1 ≤ p)
    (φ : 𝓓(⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩, F)) :
    traceLp n p hp (testFunctionToWkp (k := 1) (p := ENNReal.ofReal p) φ) = 0 := by
  apply Lp.ext
  filter_upwards [traceLp_coeFn_ae hp _ (φ.contDiff.of_le (by simp))
    φ.hasCompactSupport (testFunctionToWkp_base_ae φ),
    Lp.coeFn_zero F (ENNReal.ofReal p) (volume : Measure (ℝ^n))] with y hy hz
  rw [hy, hz]
  apply φ.zero_on_compl
  change ¬0 < joinTangentialNormal (y, 0) (Fin.last n)
  simp only [joinTangentialNormal_last, lt_self_iff_false, not_false_eq_true]

/-- The continuous half-space trace vanishes on the supported smooth closure. -/
theorem traceLp_eq_zero_of_mem_Wkp0 (hp : 1 ≤ p)
    (U : W^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F))
    (hU : U ∈ (wkp0SubmoduleOn (k := 1) (p := ENNReal.ofReal p)
      (Ω := ⟨ℝ^(n + 1)₊, SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩)
      (F := F)).toSubmodule) :
    traceLp n p hp U = 0 :=
  Wkp0SpaceOn.closed_property_of_testFunctions
    (isClosed_eq (traceLp n p hp).continuous continuous_const)
    (traceLp_testFunction_eq_zero hp) ⟨U, hU⟩

/-- The closure and trace-kernel constructions give the same whole-space function. -/
theorem zeroExtension_eq_zeroExtendCLM (hp : 1 ≤ p)
    (U : W₀^{1,ENNReal.ofReal p}(⟨ℝ^(n + 1)₊,
      SobolevSpace.HalfSpace.isOpen_upper (n + 1)⟩; F)) :
    zeroExtension U =
      zeroExtendCLM hp ⟨U.val, traceLp_eq_zero_of_mem_Wkp0 hp U.val U.property⟩ :=
  rfl

end SobolevSpace.VectorValued.Trace.HalfSpace
