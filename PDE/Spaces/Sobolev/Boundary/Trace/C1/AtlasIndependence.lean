/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Spaces.Sobolev.Boundary.Trace.C1.FiniteExponentOperator

/-!
# Independence of the Sobolev trace from the boundary atlas

For finite exponents, restrictions of ambient smooth test functions are dense in `W¹ᵖ(Ω)`.
A continuous linear trace is therefore determined by its classical boundary values.
Every operational C¹ atlas constructs a trace with these values in the same intrinsic
surface-measure space, so the resulting operator is independent of the atlas.

Evans defines `T` in step 4 of the proof of §5.5, Theorem 1, as the limit of `T u_m` for smooth
`u_m → u`, and notes that the limit does not depend on the approximating sequence. The same
density argument gives the independence of the atlas.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §5.5, proof of Theorem 1, step 4, (3), p. 273.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

namespace SobolevSpace.Trace.C1

open MeasureTheory Set GraphSpace Boundary
open Boundary.Geometry.SurfaceMeasure
open scoped ENNReal Sobolev

variable {m : ℕ} {Ω : Set (ℝ^(m + 1))}

/-- On a domain with a `C1ExtensionAtlas` and for real `p ≥ 1`, a continuous linear operator
`T : W^{1,p}(Ω) → Lᵖ(∂Ω)` that sends the restriction of every global test function to its
boundary values equals `traceLp p`. -/
theorem eq_traceLp_of_classical [hΩ : C1ExtensionAtlas (m + 1) Ω]
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (T : W^{1,ENNReal.ofReal p}(Ω) →L[ℝ]
      Lp ℝ (ENNReal.ofReal p) (surfaceMeasure Ω))
    (hT : ∀ φ : HalfSpace.GlobalTestFunction m,
      T (mkWkpSpaceOnOfContDiff (n := m + 1) (k := 1) (p := ENNReal.ofReal p)
        (Ω := Ω) φ.1.toFun φ.1.contDiff φ.1.hasCompactSupport) =
        globalTestFunctionBoundaryLpLinear (Ω := Ω) (ENNReal.ofReal p) φ) :
    T = traceLp p := by
  have heq := (denseRange_globalTestFunctionToDomainW1pLinear
    (Ω := Ω) (ENNReal.ofReal p) ENNReal.ofReal_ne_top).equalizer
    T.continuous (traceLp p).continuous ?_
  · exact ContinuousLinearMap.ext fun U ↦ congrFun heq U
  funext φ
  change T (globalTestFunctionToDomainW1pLinear (Ω := Ω) (ENNReal.ofReal p) φ) =
    traceLp p (globalTestFunctionToDomainW1pLinear (Ω := Ω) (ENNReal.ofReal p) φ)
  rw [traceLp_classical, globalTestFunctionToDomainW1pLinear_eq_mk]
  exact hT φ

/-- The finite-exponent trace is the same continuous linear map for any two
operational C¹ atlases on the domain. -/
theorem traceLp_eq_of_atlases
    (A B : C1ExtensionAtlas (m + 1) Ω)
    (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] :
    traceLp (hΩ := A) p = traceLp (hΩ := B) p := by
  apply eq_traceLp_of_classical (hΩ := B) p (traceLp (hΩ := A) p)
  intro φ
  rw [← globalTestFunctionToDomainW1pLinear_eq_mk
    (hΩ := A) (ENNReal.ofReal p) φ, traceLp_classical (hΩ := A)]
  rfl

end SobolevSpace.Trace.C1
