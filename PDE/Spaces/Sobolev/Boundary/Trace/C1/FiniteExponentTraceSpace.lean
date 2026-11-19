/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.FiniteExponentOperator
public import PDE.Spaces.Sobolev.Boundary.Trace.C1.TraceSpace

/-!
# Finite-exponent trace space of an operational C¹ domain

For an operational `C¹` domain `Ω` and `1 ≤ p`, we equip the range of the
finite-exponent trace `Trₚ : W^{1,p}(Ω) → Lᵖ(∂Ω)` with its intrinsic quotient norm:

`W^{1,p}(Ω) / ker(Trₚ)`.

The quotient maps continuously and injectively into `Lᵖ(∂Ω)` and is linearly equivalent to the
algebraic range of `Trₚ` by the first isomorphism theorem. For `1 < p`, classically that range
is the fractional Sobolev space `W^{1-1/p,p}(∂Ω)`. `Trace.C1.Fractional.FiniteExponent.Range`
characterizes it by chartwise Gagliardo regularity of order `1 - 1/p` and gives a bounded
lifting of compatible chart data. The endpoint `p = 1` is included as an abstract quotient.
The theorem `rightInverse_traceLpClass_iff` records what a right inverse must satisfy.

At `p = 2` the space is canonically equivalent to the Hilbert trace space `HilbertTraceSpace`
built from `Trace.C1.trace`.

## Main declarations

* `traceLpKernel`, `LpTraceSpace`, `traceLpClass`: the closed kernel, the quotient, and the
  quotient map.
* `boundaryValueLp`, `range_boundaryValueLp`: realization of a trace
  class as its boundary `Lᵖ` value.
* `traceLpEquivRange`: the linear equivalence with `range Trₚ`.
* `lpTraceSpaceTwoEquivHilbertTraceSpace`: the exponent-two comparison.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, Theorem 1, pp. 272-273, for the trace operator
  `T : W^{1,p}(U) → L^p(∂U)`, `1 ≤ p < ∞`, on a bounded `C¹` domain.
  <https://doi.org/10.1090/gsm/019>
* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Pure and Applied Mathematics 140,
  Academic Press, 2003, Chapter 7, Fractional Order Spaces, pp. 205-260, for traces of Sobolev
  functions and the spaces `W^{1-1/p,p}(∂Ω)`.
  <https://shop.elsevier.com/books/sobolev-spaces/adams/978-0-12-044143-3>
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
  (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]

/-- The domain `W^{1,p}(Ω)` space on which the finite-exponent trace acts. -/
abbrev DomainW1p :=
  W^{1,ENNReal.ofReal p}(Ω)

/-- The boundary `Lᵖ(∂Ω)` space with respect to the surface measure of `Ω`. -/
abbrev BoundaryLp :=
  Lp ℝ (ENNReal.ofReal p)
    (Boundary.Geometry.SurfaceMeasure.surfaceMeasure Ω)

/-- The closed kernel of the operational `C1` finite-exponent trace. -/
def traceLpKernel :
    ClosedSubmodule ℝ (DomainW1p (m := m) (Ω := Ω) p) :=
  ContinuousLinearMap.KernelQuotient.closedKernel
    (traceLp (m := m) (Ω := Ω) p)

/--
The intrinsic finite-exponent trace space of an operational `C1` domain, with
the quotient norm inherited from `W^{1,p}(Ω)`.
-/
abbrev LpTraceSpace :=
  DomainW1p (m := m) (Ω := Ω) p ⧸ (traceLp (m := m) (Ω := Ω) p).ker

/-- Send a domain `W^{1,p}` function to its trace class. -/
def traceLpClass :
    DomainW1p (m := m) (Ω := Ω) p →L[ℝ]
      LpTraceSpace (m := m) (Ω := Ω) p :=
  (traceLp (m := m) (Ω := Ω) p).ker.mkQL

/-- Realize an intrinsic trace class as its boundary `Lᵖ` value. -/
def boundaryValueLp :
    LpTraceSpace (m := m) (Ω := Ω) p →L[ℝ]
      BoundaryLp (m := m) (Ω := Ω) p :=
  (traceLp (m := m) (Ω := Ω) p).ker.liftQL (traceLp (m := m) (Ω := Ω) p) le_rfl

/--
The first isomorphism theorem identifies the quotient trace space with the
algebraic range of the operational `C1` finite-exponent trace.
-/
noncomputable def traceLpEquivRange :
    LpTraceSpace (m := m) (Ω := Ω) p ≃ₗ[ℝ]
      LinearMap.range
        (traceLp (m := m) (Ω := Ω) p).toLinearMap :=
  (traceLp (m := m) (Ω := Ω) p).toLinearMap.quotKerEquivRange

/-- The range equivalence and the boundary-value realization have the same value. -/
theorem coe_traceLpEquivRange
    (q : LpTraceSpace (m := m) (Ω := Ω) p) :
    ((traceLpEquivRange (m := m) (Ω := Ω) p q :
        LinearMap.range
          (traceLp (m := m) (Ω := Ω) p).toLinearMap) :
        BoundaryLp (m := m) (Ω := Ω) p) =
      boundaryValueLp (m := m) (Ω := Ω) p q := by
  obtain ⟨u, rfl⟩ :=
    (ContinuousLinearMap.KernelQuotient.closedKernel
      (traceLp (m := m) (Ω := Ω) p)).toSubmodule.mkQ_surjective q
  rfl

/-- The boundary-value realization has exactly the range of the original trace. -/
theorem range_boundaryValueLp :
    LinearMap.range
        (boundaryValueLp (m := m) (Ω := Ω) p).toLinearMap =
      LinearMap.range
        (traceLp (m := m) (Ω := Ω) p).toLinearMap :=
  Submodule.range_liftQ (traceLp (m := m) (Ω := Ω) p).ker
    (traceLp (m := m) (Ω := Ω) p).toLinearMap le_rfl

/--
A bounded map into the Sobolev domain splits the quotient map exactly when
its `C1` trace realizes every intrinsic boundary value.
-/
theorem rightInverse_traceLpClass_iff
    (E :
      LpTraceSpace (m := m) (Ω := Ω) p →L[ℝ]
        DomainW1p (m := m) (Ω := Ω) p) :
    Function.RightInverse E
        (traceLpClass (m := m) (Ω := Ω) p) ↔
      ∀ q,
        traceLp (m := m) (Ω := Ω) p (E q) =
          boundaryValueLp (m := m) (Ω := Ω) p q := by
  constructor
  · intro hE q
    have heq := congrArg (boundaryValueLp (m := m) (Ω := Ω) p) (hE q)
    simpa [boundaryValueLp, traceLpClass] using heq
  · intro hE q
    apply LinearMap.ker_eq_bot.mp
      (Submodule.ker_liftQ_eq_bot (traceLp (m := m) (Ω := Ω) p).ker
        (traceLp (m := m) (Ω := Ω) p).toLinearMap le_rfl le_rfl)
    simpa [boundaryValueLp, traceLpClass] using hE q

/-! ## Compatibility with the Hilbert trace space -/

section ExponentTwo

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}
  [hΩ : Boundary.C1ExtensionAtlas (m + 1) Ω]

/--
The canonical `W^{1,2} ≃ H¹` identification carries the finite-exponent
zero-trace space onto the Hilbert zero-trace space.
-/
theorem domainW1pTwoEquivH1_mem_traceKernel_iff
    (u : W^{1,(ENNReal.ofReal (2 : ℝ))}(Ω)) :
    domainW1pTwoEquivH1 (m := m) (Ω := Ω) u ∈
        traceKernel (m := m) (Ω := Ω) ↔
      u ∈ traceLpKernel (m := m) (Ω := Ω) 2 := by
  change trace (m := m) (Ω := Ω)
      (domainW1pTwoEquivH1 (m := m) (Ω := Ω) u) = 0 ↔
    traceLp (m := m) (Ω := Ω) 2 u = 0
  rw [← boundaryLpTwoEquivL2_traceLp (m := m) (Ω := Ω) u]
  exact (boundaryLpTwoEquivL2 (m := m) (Ω := Ω)).map_eq_zero_iff

/--
At exponent two, the intrinsic finite-exponent trace space is canonically
continuously linearly equivalent to the Hilbert trace space.
-/
noncomputable def lpTraceSpaceTwoEquivHilbertTraceSpace :
    LpTraceSpace (m := m) (Ω := Ω) 2 ≃L[ℝ]
      HilbertTraceSpace (m := m) (Ω := Ω) :=
  ContinuousLinearMap.KernelQuotient.congr
    (traceLp (m := m) (Ω := Ω) 2)
    (trace (m := m) (Ω := Ω))
    (domainW1pTwoEquivH1 (m := m) (Ω := Ω))
    fun u ↦ by
      rw [← boundaryLpTwoEquivL2_traceLp (m := m) (Ω := Ω) u]
      exact
        (boundaryLpTwoEquivL2
          (m := m) (Ω := Ω)).map_eq_zero_iff.symm

/-- The exponent-two trace-space equivalence is induced by `W^{1,2} ≃ H¹`. -/
@[simp]
theorem lpTraceSpaceTwoEquivHilbertTraceSpace_traceLpClass
    (u : W^{1,(ENNReal.ofReal (2 : ℝ))}(Ω)) :
    lpTraceSpaceTwoEquivHilbertTraceSpace (m := m) (Ω := Ω)
        (traceLpClass (m := m) (Ω := Ω) 2 u) =
      traceClass (m := m) (Ω := Ω)
        (domainW1pTwoEquivH1 (m := m) (Ω := Ω) u) :=
  rfl

/--
Boundary realization commutes with the canonical equivalence between the
finite exponent-two and Hilbert trace spaces.
-/
theorem boundaryValue_lpTraceSpaceTwoEquivHilbertTraceSpace
    (q : LpTraceSpace (m := m) (Ω := Ω) 2) :
    boundaryValue (m := m) (Ω := Ω)
        (lpTraceSpaceTwoEquivHilbertTraceSpace
          (m := m) (Ω := Ω) q) =
      boundaryLpTwoEquivL2 (m := m) (Ω := Ω)
        (boundaryValueLp (m := m) (Ω := Ω) 2 q) := by
  obtain ⟨u, rfl⟩ :=
    (ContinuousLinearMap.KernelQuotient.closedKernel
      (traceLp (m := m) (Ω := Ω) 2)).toSubmodule.mkQ_surjective q
  change trace (m := m) (Ω := Ω) (domainW1pTwoEquivH1 (m := m) (Ω := Ω) u) =
    boundaryLpTwoEquivL2 (m := m) (Ω := Ω) (traceLp (m := m) (Ω := Ω) 2 u)
  exact (boundaryLpTwoEquivL2_traceLp (m := m) (Ω := Ω) u).symm


end ExponentTwo

end Trace.C1
end SobolevSpace
