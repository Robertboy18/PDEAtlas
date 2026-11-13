/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Analysis.Operator.KernelQuotient
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.Operator

/-!
# The Hilbert trace space of an operational C1 domain

For an operational `C1` domain `Ω`, we equip the range of the
`H¹(Ω)` trace with its canonical quotient Hilbert norm:

`H¹(Ω) / ker(Tr)`.

Here `trace` is the operator `T` of Evans §5.5, Theorem 1, for `p = 2`, and its kernel is `H¹₀(Ω)`
by Theorem 2 there (see `Trace.C1.ZeroTrace`). Evans's §5.5 does not describe the range of `T`;
we describe it through the quotient.

The quotient embeds injectively into `L²(∂Ω)`. Orthogonal decomposition gives
each trace class a unique representative in the orthogonal complement of the
trace kernel. This representative preserves the quotient norm and is the
minimal-energy extension of its boundary value.

The quotient identities and minimal-norm results come from
`ContinuousLinearMap.KernelQuotient`, applied to `trace`.

`Trace.C1.Fractional.Identification` identifies this quotient with the chartwise
fractional `H^(1/2)(∂Ω)` space.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorems 1 and 2, pp. 271-275.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

noncomputable section

set_option linter.missingDocs true

namespace SobolevSpace
namespace Trace.C1

open MeasureTheory Set
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
  [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/-- The domain `H¹(Ω)` space on which the operational `C1` trace acts. -/
abbrev DomainH1 :=
  H¹(Ω)

/-- The boundary `L²(∂Ω)` space with respect to the surface measure of `Ω`. -/
abbrev BoundaryL2 :=
  Lp ℝ 2 (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)

/-- The closed kernel of the operational `C1`-domain trace. -/
def traceKernel : ClosedSubmodule ℝ (DomainH1 (m := m) (Ω := Ω)) :=
  ContinuousLinearMap.KernelQuotient.closedKernel
    (trace (m := m) (Ω := Ω))

/-- The operational `C1`-domain trace kernel is closed. -/
instance traceKernelIsClosed :
    IsClosed
      ((traceKernel (m := m) (Ω := Ω)).toSubmodule :
        Set (DomainH1 (m := m) (Ω := Ω))) :=
  (traceKernel (m := m) (Ω := Ω)).isClosed

/--
The intrinsic Hilbert trace space of an operational `C1` domain, with the
quotient norm inherited from `H¹(Ω)`.
-/
abbrev HilbertTraceSpace :=
  DomainH1 (m := m) (Ω := Ω) ⧸ (trace (m := m) (Ω := Ω)).ker

/-- Send a domain `H¹` function to its class modulo zero trace. -/
def traceClass :
    DomainH1 (m := m) (Ω := Ω) →L[ℝ]
      HilbertTraceSpace (m := m) (Ω := Ω) :=
  (trace (m := m) (Ω := Ω)).ker.mkQL

/--
The canonical minimal-energy extension of an intrinsic boundary trace class.
-/
def minimalExtension :
    HilbertTraceSpace (m := m) (Ω := Ω) →L[ℝ]
      DomainH1 (m := m) (Ω := Ω) :=
  ContinuousLinearMap.KernelQuotient.representative
    (trace (m := m) (Ω := Ω))

/-- Realize an intrinsic trace class as its boundary `L²` value. -/
def boundaryValue :
    HilbertTraceSpace (m := m) (Ω := Ω) →L[ℝ]
      BoundaryL2 (m := m) (Ω := Ω) :=
  (trace (m := m) (Ω := Ω)).ker.liftQL (trace (m := m) (Ω := Ω)) le_rfl

end Trace.C1
end SobolevSpace
