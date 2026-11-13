/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/
module

public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.HeightAverage
public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Scalar
public import PDE.Spaces.Sobolev.GraphSpace.Operators.PartialDerivativeEnergy

/-!
# Height averages converge to the Sobolev trace

The normal derivative controls the difference between a height average and
the physical boundary trace: the boundary `Lᵖ` error, raised to the power `p`,
is at most `ε ^ (p - 1)` times the normal derivative energy. For `p > 1` this
factor tends to zero, so the height averages converge in boundary `Lᵖ` to
`traceLp`. Both statements are the Banach-valued ones at `F := ℝ`, read through
the canonical isometry between the two Sobolev graphs.
-/

@[expose] public section

open PDE (iteratedPartialDeriv)

noncomputable section

namespace SobolevSpace.Trace.HalfSpace

open MeasureTheory Filter Set
open scoped ENNReal Sobolev Topology
open VectorValued.Trace.HalfSpace (upperScalarEquiv traceLp_upperScalarEquiv_symm)

variable (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

/-- The base `Lᵖ` coordinate of a global test function is represented by its
literal restriction to the upper half-space. -/
theorem coeFn_base_globalTestFunctionToUpperW1pLinear (φ : GlobalTestFunction n) :
    (GraphSpace.wkpBaseCoordinateCLM (globalTestFunctionToUpperW1pLinear n p φ) :
      ℝ^(n + 1) → ℝ) =ᵐ[volume.restrict ℝ^(n+1)₊] φ.1.toFun := by
  rw [GraphSpace.wkpBaseCoordinateCLM_apply, globalTestFunctionToUpperW1pLinear_eq_mk]
  simpa only [GraphSpace.baseIndex_toList, iteratedPartialDeriv] using
    GraphSpace.mkWkpSpaceOnOfContDiff_apply_ae (p := ENNReal.ofReal p)
      (Ω := HalfSpace.upper (n + 1)) φ.1.toFun φ.1.contDiff φ.1.hasCompactSupport
      (GraphSpace.baseIndex (n + 1) 1)

/-- The p-energy of the difference between a height average and the Sobolev
trace is at most `ε ^ (p - 1)` times the normal derivative p-energy. -/
theorem norm_heightAverageLp_sub_traceLp_rpow_le
    (hp : 1 ≤ p) (ε : ℝ) (hε : 0 < ε)
    (U : W^{1,ENNReal.ofReal p}(ℝ^(n+1)₊)) :
    ‖heightAverageLp n p hp ε hε (GraphSpace.wkpBaseCoordinateCLM U) -
        traceLp n p hp U‖ ^ p ≤
      ε ^ (p - 1) * ‖∂[Fin.last n] U‖ ^ p := by
  have h := VectorValued.Trace.HalfSpace.norm_heightAverageLp_sub_traceLp_rpow_le n p hp ε hε
    ((upperScalarEquiv n p).symm U)
  rw [traceLp_upperScalarEquiv_symm, VectorValued.norm_partialDeriv_eq_coordinate] at h
  rw [GraphSpace.norm_partialDeriv_eq_wkpCoordinateCLM]
  exact h

/-- Along every positive scale tending to zero, height averages of a Sobolev
function converge in boundary `Lᵖ` to its physical trace. -/
theorem tendsto_heightAverageLp_of_tendsto
    (hp : 1 < p) (U : W^{1,ENNReal.ofReal p}(ℝ^(n+1)₊))
    {ι : Type*} {l : Filter ι} (ε : ι → ℝ)
    (hε : ∀ i, 0 < ε i) (hε₀ : Tendsto ε l (𝓝 0)) :
    Tendsto (fun i ↦ heightAverageLp n p hp.le (ε i) (hε i)
      (GraphSpace.wkpBaseCoordinateCLM U)) l (𝓝 (traceLp n p hp.le U)) := by
  have h := VectorValued.Trace.HalfSpace.tendsto_heightAverageLp_of_tendsto n p hp
    ((upperScalarEquiv n p).symm U) ε hε hε₀
  rw [traceLp_upperScalarEquiv_symm] at h
  exact h

/-- As height tends to zero from above, the averaging operators recover
the Sobolev trace in boundary `Lᵖ`, in every boundary dimension. -/
theorem tendsto_heightAverageLp
    (hp : 1 < p) (U : W^{1,ENNReal.ofReal p}(ℝ^(n+1)₊)) :
    Tendsto (fun ε : Ioi (0 : ℝ) ↦ heightAverageLp n p hp.le ε ε.2
      (GraphSpace.wkpBaseCoordinateCLM U))
      (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 (traceLp n p hp.le U)) :=
  tendsto_heightAverageLp_of_tendsto n p hp U
    (fun ε : Ioi (0 : ℝ) ↦ (ε : ℝ)) (fun ε ↦ ε.2)
    (tendsto_comap.mono_right nhdsWithin_le_nhds)

end SobolevSpace.Trace.HalfSpace
