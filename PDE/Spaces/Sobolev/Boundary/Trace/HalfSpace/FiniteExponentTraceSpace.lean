/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.FiniteExponentCompletion
public import PDE.Spaces.Sobolev.Boundary.Trace.HalfSpace.TraceSpace

/-!
# Finite-exponent trace space on the upper half-space

For `1 ≤ p`, we equip the range of the flat finite-exponent trace
with its intrinsic quotient norm:

`W^{1,p}(ℝ^(n + 1)₊) / ker(Trₚ)`.

The flat trace `Trₚ` is the half-space case of the operator `T` of Evans §5.5, Theorem 1,
whose proof starts from this case. Evans's §5.5 does not describe the range of `T`; we describe
it through the quotient.

The quotient maps continuously and injectively into boundary `Lᵖ(ℝ^n)` and
is linearly equivalent to the algebraic range of `Trₚ`. For `1 < p < ∞`,
`Trace.HalfSpace.Fractional.TraceSpace.FiniteExponent` identifies the quotient with
the Gagliardo space `W^{1-1/p,p}(ℝ^n)`. The endpoint `p = 1`
is included using the completed `W^{1,1}` trace.

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

variable (n : ℕ) (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] (hp : 1 ≤ p)

/-- The upper-half-space Sobolev space `W^{1,p}(ℝ^(n + 1)₊)` at a real exponent. -/
abbrev UpperW1p :=
  W^{1,ENNReal.ofReal p}(HalfSpace.upper (n + 1))

/-- The flat boundary Lebesgue space `Lᵖ(ℝ^n)` at a real exponent. -/
abbrev BoundaryLp :=
  Lp ℝ (ENNReal.ofReal p) (volume : Measure (ℝ^n))

/-- The closed kernel of the flat finite-exponent trace. -/
def traceLpKernel : ClosedSubmodule ℝ (UpperW1p n p) :=
  ContinuousLinearMap.KernelQuotient.closedKernel (traceLp n p hp)

/--
The intrinsic finite-exponent trace space on the flat boundary, with the
quotient norm inherited from upper-half-space `W^{1,p}`.
-/
abbrev LpTraceSpace :=
  UpperW1p n p ⧸ (traceLp n p hp).ker

/-- Send an upper-half-space `W^{1,p}` function to its trace class. -/
def traceLpClass : UpperW1p n p →L[ℝ] LpTraceSpace n p hp :=
  (traceLp n p hp).ker.mkQL

/-- Realize an intrinsic trace class as its boundary `Lᵖ` value. -/
def boundaryValueLp : LpTraceSpace n p hp →L[ℝ] BoundaryLp n p :=
  (traceLp n p hp).ker.liftQL (traceLp n p hp) le_rfl

/--
The first isomorphism theorem identifies the quotient trace space with the
algebraic range of the flat finite-exponent trace.
-/
noncomputable def traceLpEquivRange :
    LpTraceSpace n p hp ≃ₗ[ℝ] LinearMap.range (traceLp n p hp).toLinearMap :=
  (traceLp n p hp).toLinearMap.quotKerEquivRange

/-- The range equivalence and the boundary-value realization have the same value. -/
theorem coe_traceLpEquivRange (q : LpTraceSpace n p hp) :
    ((traceLpEquivRange n p hp q :
        LinearMap.range (traceLp n p hp).toLinearMap) : BoundaryLp n p) =
      boundaryValueLp n p hp q := by
  obtain ⟨u, rfl⟩ := (ContinuousLinearMap.KernelQuotient.closedKernel
      (traceLp n p hp)).toSubmodule.mkQ_surjective q
  rfl

/-- The boundary-value realization has exactly the range of the original trace. -/
theorem range_boundaryValueLp :
    LinearMap.range (boundaryValueLp n p hp).toLinearMap =
      LinearMap.range (traceLp n p hp).toLinearMap :=
  Submodule.range_liftQ (traceLp n p hp).ker (traceLp n p hp).toLinearMap le_rfl

/--
A bounded map into the Sobolev domain splits the quotient map exactly when
its flat trace realizes every intrinsic boundary value.
-/
theorem rightInverse_traceLpClass_iff
    (E : LpTraceSpace n p hp →L[ℝ] UpperW1p n p) :
    Function.RightInverse E (traceLpClass n p hp) ↔
      ∀ q, traceLp n p hp (E q) = boundaryValueLp n p hp q := by
  constructor
  · intro hE q
    have heq := congrArg (boundaryValueLp n p hp) (hE q)
    simpa [boundaryValueLp, traceLpClass] using heq
  · intro hE q
    apply LinearMap.ker_eq_bot.mp
      (Submodule.ker_liftQ_eq_bot (traceLp n p hp).ker
        (traceLp n p hp).toLinearMap le_rfl le_rfl)
    simpa [boundaryValueLp, traceLpClass] using hE q

/-! ## Compatibility with the Hilbert trace space -/

section ExponentTwo

variable (n : ℕ)

/--
The canonical `W^{1,2} ≃ H¹` identification carries the finite-exponent
zero-trace space onto the Hilbert zero-trace space.
-/
theorem upperW1pTwoEquivH1_mem_traceKernel_iff
    (u : W^{1,(ENNReal.ofReal (2 : ℝ))}(HalfSpace.upper (n + 1))) :
    upperW1pTwoEquivH1 n u ∈ traceKernel n ↔
      u ∈ traceLpKernel n 2 (by norm_num) := by
  change trace n (upperW1pTwoEquivH1 n u) = 0 ↔
    traceLp n 2 (by norm_num) u = 0
  rw [← boundaryLpTwoEquivL2_traceLp n u]
  exact (boundaryLpTwoEquivL2 n).map_eq_zero_iff

/--
At exponent two, the intrinsic finite-exponent trace space is canonically
continuously linearly equivalent to the Hilbert trace space.
-/
noncomputable def lpTraceSpaceTwoEquivHilbertTraceSpace :
    LpTraceSpace n 2 (by norm_num) ≃L[ℝ] HilbertTraceSpace n :=
  ContinuousLinearMap.KernelQuotient.congr
    (traceLp n 2 (by norm_num)) (trace n) (upperW1pTwoEquivH1 n)
    fun u ↦ by
      rw [← boundaryLpTwoEquivL2_traceLp n u]
      exact (boundaryLpTwoEquivL2 n).map_eq_zero_iff.symm

/-- The exponent-two trace-space equivalence is induced by `W^{1,2} ≃ H¹`. -/
@[simp]
theorem lpTraceSpaceTwoEquivHilbertTraceSpace_traceLpClass
    (u : W^{1,(ENNReal.ofReal (2 : ℝ))}(HalfSpace.upper (n + 1))) :
    lpTraceSpaceTwoEquivHilbertTraceSpace n
        (traceLpClass n 2 (by norm_num) u) =
      traceClass n (upperW1pTwoEquivH1 n u) :=
  rfl

/--
Boundary realization commutes with the canonical equivalence between the
finite exponent-two and Hilbert trace spaces.
-/
theorem boundaryValue_lpTraceSpaceTwoEquivHilbertTraceSpace
    (q : LpTraceSpace n 2 (by norm_num)) :
    boundaryValue n (lpTraceSpaceTwoEquivHilbertTraceSpace n q) =
      boundaryLpTwoEquivL2 n (boundaryValueLp n 2 (by norm_num) q) := by
  obtain ⟨u, rfl⟩ := (ContinuousLinearMap.KernelQuotient.closedKernel
      (traceLp n 2 (by norm_num))).toSubmodule.mkQ_surjective q
  change trace n (upperW1pTwoEquivH1 n u) =
    boundaryLpTwoEquivL2 n (traceLp n 2 (by norm_num) u)
  exact (boundaryLpTwoEquivL2_traceLp n u).symm


end ExponentTwo

end Trace.HalfSpace
end SobolevSpace
