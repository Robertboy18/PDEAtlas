/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.KernelQuotient
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.Operator

/-!
# The Hilbert trace space on the upper half-space

We equip the range of the flat `H¹` trace with its natural quotient
Hilbert norm. The resulting `HilbertTraceSpace n` is

`H¹(ℝ^(n + 1)₊) / ker(Tr)`.

The flat trace is the half-space case, for `p = 2`, of the operator `T` of Evans §5.5,
Theorem 1, whose proof starts from this case. Evans's §5.5 does not describe the range of `T`;
we describe it through the quotient.

The quotient embeds injectively into boundary `L²(ℝ^n)`. Orthogonal decomposition gives
each trace class a unique representative in `ker(Tr)ᗮ`; this representative is
the canonical minimal-energy extension and preserves the quotient norm.

The quotient identities and minimal-norm results come from
`ContinuousLinearMap.KernelQuotient`, applied to `trace`.

`Trace.HalfSpace.Fractional.TraceSpace` identifies this quotient with Fourier-defined
`H^(1/2)(ℝ^n)`.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 1 and its proof, pp. 271-273.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace
namespace Trace.HalfSpace

open MeasureTheory Set
open scoped ENNReal Sobolev

variable (n : ℕ)

/-- Upper-half-space `H¹` in dimension `n + 1`. -/
abbrev UpperH1 :=
  H¹(HalfSpace.upper (n + 1))

/-- Boundary `L²` on the flat boundary `ℝ^n`. -/
abbrev BoundaryL2 :=
  Lp ℝ 2 (volume : Measure (ℝ^n))

/-- The closed kernel of the flat upper-half-space trace. -/
def traceKernel : ClosedSubmodule ℝ (UpperH1 n) :=
  ContinuousLinearMap.KernelQuotient.closedKernel (trace n)

/-- The trace kernel is closed as a submodule of upper-half-space `H¹`. -/
instance traceKernelIsClosed :
    IsClosed ((traceKernel n).toSubmodule : Set (UpperH1 n)) :=
  (traceKernel n).isClosed

/--
The Hilbert trace space on the flat boundary, with the quotient norm inherited
from upper-half-space `H¹`.
-/
abbrev HilbertTraceSpace :=
  UpperH1 n ⧸ (trace n).ker

/-- Send an upper-half-space `H¹` function to its class modulo zero trace. -/
def traceClass : UpperH1 n →L[ℝ] HilbertTraceSpace n :=
  (trace n).ker.mkQL

/--
The canonical minimal-energy extension of a Hilbert trace class. Its image is
the orthogonal complement of the trace kernel.
-/
def minimalExtension : HilbertTraceSpace n →L[ℝ] UpperH1 n :=
  ContinuousLinearMap.KernelQuotient.representative (trace n)

/--
Realize a Hilbert trace class as its boundary `L²` value. This map is
well-defined because the flat trace vanishes on `traceKernel`.
-/
def boundaryValue : HilbertTraceSpace n →L[ℝ] BoundaryL2 n :=
  (trace n).ker.liftQL (trace n) le_rfl

end Trace.HalfSpace
end SobolevSpace
