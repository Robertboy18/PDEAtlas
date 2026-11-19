/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.VectorValued.HalfSpace.Scalar
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Scalar
public import PDE.Spaces.Sobolev.Boundary.ZeroTrace.VectorValued.Trace.HalfSpaceConverse

/-!
# Geometric zero trace and interior approximation on the half-space

For every real `1 ≤ p < ∞`, the kernel of the completed geometric half-space
trace is exactly `W^{1,p}_0`, the closure of the interior smooth test functions.

This is the real-valued case of the Banach-valued theorem
`SobolevSpace.VectorValued.Trace.HalfSpace.traceLp_eq_zero_iff_mem_Wkp0`. The scalar Sobolev graph
is the Banach-valued graph at codomain `ℝ` (`VectorValued.scalarEquiv`), the two traces agree
under this identification (`VectorValued.Trace.HalfSpace.traceLp_upperScalarEquiv_symm`), and so do
the two closures of the interior test functions (`VectorValued.scalarEquiv_mem_wkp0_iff`).

On the half-space this is the reduced statement (6) in the proof of Evans §5.5, Theorem 2,
without the assumption of compact support. The forward implication is step 1 of that proof.
For the converse Evans uses the estimate (9) and the cutoffs `1 - ζ(m x_n)`; the Banach-valued
proof instead extends `u` by zero and approximates the extension by interior test functions.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 2 and its proof, (6)-(9), pp. 273-275.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

namespace SobolevSpace.Trace.HalfSpace

open MeasureTheory Set GraphSpace
open scoped ENNReal Topology Sobolev

variable {n : ℕ} (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p)

/-- For real `p ≥ 1`, including `p = 1`, `traceLp n p hp u = 0` if and only if `u` lies in
`W^{1,p}_0` of the upper half-space. This is the case `F = ℝ` of
`SobolevSpace.VectorValued.Trace.HalfSpace.traceLp_eq_zero_iff_mem_Wkp0`. -/
theorem traceLp_eq_zero_iff_mem_Wkp0
    (u : W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1))) :
    traceLp n p hp u = 0 ↔
      u ∈ (wkp0SubmoduleOn (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
        (Ω := HalfSpace.upper (n + 1))).toSubmodule := by
  rw [← VectorValued.Trace.HalfSpace.traceLp_upperScalarEquiv_symm hp u]
  exact (VectorValued.Trace.HalfSpace.traceLp_eq_zero_iff_mem_Wkp0 hp _).trans
    (VectorValued.scalarEquiv_mem_wkp0_iff
      ((VectorValued.Trace.HalfSpace.upperScalarEquiv n p).symm u)).symm

/-- Interior smooth test functions have zero completed geometric trace: a test function lies in
`W^{1,p}_0` by definition, and `traceLp_eq_zero_iff_mem_Wkp0` applies. -/
theorem traceLp_testFunction_eq_zero
    (φ : TestFunctionOn (n + 1) (HalfSpace.upper (n + 1))) :
    traceLp n p hp (testFunctionToWkp (k := 1) (p := ENNReal.ofReal p) φ) = 0 :=
  (traceLp_eq_zero_iff_mem_Wkp0 p hp _).mpr (testFunctionToWkp_mem_Wkp0 φ)

/-- Equality of the geometric trace kernel with the closed interior Sobolev core. -/
theorem ker_traceLp_eq_wkp0SubmoduleOn :
    (traceLp n p hp).ker =
      (wkp0SubmoduleOn (n := n + 1) (k := 1) (p := ENNReal.ofReal p)
        (Ω := HalfSpace.upper (n + 1))).toSubmodule := by
  ext u
  exact traceLp_eq_zero_iff_mem_Wkp0 p hp u

end SobolevSpace.Trace.HalfSpace
