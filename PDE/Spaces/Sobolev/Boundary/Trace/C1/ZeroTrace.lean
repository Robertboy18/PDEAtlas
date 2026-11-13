/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ZeroTrace.Localization
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.ZeroTrace.Reconstruction
public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.C1.Scalar
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Scalar
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Trace.C1Converse

/-!
# Zero trace on an operational C¹ domain

For every real exponent `1 ≤ p`, the kernel of the geometric `Lᵖ` trace on a domain
with a `C1ExtensionAtlas` is the closure-defined space `W^{1,p}_0(Ω)`. This is Evans §5.5,
Theorem 2, with the atlas in place of the hypotheses that `U` is bounded with `C¹` boundary.

This is the real-valued case of the Banach-valued theorem
`SobolevSpace.VectorValued.Trace.C1.traceLp_eq_zero_iff_mem_Wkp0`, which carries the proof:
localization of a vanishing trace to the flattened charts, the half-space theorem, and
reconstruction through the atlas partition. The scalar Sobolev graph is the Banach-valued graph
at codomain `ℝ` (`VectorValued.scalarEquiv`), the two traces agree under this identification
(`VectorValued.Trace.C1.traceLp_eq_scalar_traceLp`), and so do the two closures of the interior
test functions (`VectorValued.scalarEquiv_mem_wkp0_iff`).

The hypothesis is the operational atlas; `Boundary.Atlas.Geometric.GraphConstruction`
constructs one from a bounded open set with C¹ graph boundary.

The imported modules `ZeroTrace.Localization`, `ZeroTrace.CompactSupport` and
`ZeroTrace.Reconstruction` keep the real-valued statements about the scalar operators `flattenCLM`,
`cutoffCLM` and `boundaryFromUpperCLM`: a vanishing trace localizes to the flattened charts, fields
with compact support inside the domain lie in `W^{1,p}_0(Ω)`, and reconstruction through a chart
maps `W^{1,p}_0` of the half-space into `W^{1,p}_0(Ω)`. The theorem below does not use them.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 2 and its proof, pp. 273-275.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Trace.C1

open MeasureTheory Set GraphSpace
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
variable [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]
variable (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

/-- Evans §5.5, Theorem 2: on a domain with a `C1ExtensionAtlas` and for real `p ≥ 1`,
`traceLp p u = 0` if and only if `u` lies in `W^{1,p}_0(Ω)`, the closure of the test functions
supported in `Ω`. This is the case `F = ℝ` of
`SobolevSpace.VectorValued.Trace.C1.traceLp_eq_zero_iff_mem_Wkp0`. -/
theorem traceLp_eq_zero_iff_mem_Wkp0
    (u : W^{1,ENNReal.ofReal p}(Ω)) :
    traceLp p u = 0 ↔
      u ∈ (wkp0SubmoduleOn (n := m + 1) (k := 1) (p := ENNReal.ofReal p)
        (Ω := Ω)).toSubmodule := by
  let V : TopologicalSpace.Opens ℝ^(m + 1) := ⟨Ω, hΩ.isOpen⟩
  let U := (VectorValued.scalarEquiv (Ω := V)).symm u
  have hp : 1 ≤ p := ENNReal.one_le_ofReal.mp (Fact.out : 1 ≤ ENNReal.ofReal p)
  have htrace : VectorValued.Trace.C1.traceLp p hp U = traceLp p u :=
    VectorValued.Trace.C1.traceLp_eq_scalar_traceLp hp U
  rw [← htrace]
  exact (VectorValued.Trace.C1.traceLp_eq_zero_iff_mem_Wkp0 hp U).trans
    (VectorValued.scalarEquiv_mem_wkp0_iff U).symm

/-- The case `p = 2`: for `u ∈ H¹(Ω)`, `trace u = 0` if and only if `u ∈ H¹₀(Ω)`. -/
theorem trace_eq_zero_iff_mem_H10 (u : H¹(Ω)) :
    trace u = 0 ↔ u ∈ (h10SubmoduleOn (n := m + 1) (Ω := Ω)).toSubmodule := by
  obtain ⟨v, rfl⟩ := (domainW1pTwoEquivH1 (Ω := Ω)).surjective u
  rw [← boundaryLpTwoEquivL2_traceLp, map_eq_zero_iff _ (ContinuousLinearEquiv.injective _)]
  rw [traceLp_eq_zero_iff_mem_Wkp0 2]
  exact (domainW1pTwoEquivH1_mem_H10_iff v).symm

/-- The kernel of the geometric finite-exponent trace is `W^{1,p}_0(Ω)`. -/
theorem ker_traceLp_eq_wkp0SubmoduleOn :
    (traceLp (Ω := Ω) p).ker =
      (wkp0SubmoduleOn (n := m + 1) (k := 1) (p := ENNReal.ofReal p)
        (Ω := Ω)).toSubmodule := by
  ext u
  exact traceLp_eq_zero_iff_mem_Wkp0 p u

end SobolevSpace.Trace.C1
