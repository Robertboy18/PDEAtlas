/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Notation.Divergence
public import PDE.Spaces.Sobolev.Calculus.Divergence.FirstOrder
public import PDE.Spaces.Sobolev.Variational.Spaces.GelfandTriple.VectorZeroBoundary

/-!
# Divergence on the vector zero-boundary space

The trace of the full weak matrix gradient is a continuous linear map to L².
The shared notation `∇· u` gives this L² class. Its kernel is a
linear incompressibility constraint. The comparison with `negativeDivergence`
retains the sign used by integration by parts.

The input space distinguishes this operator from the arbitrary-order Sobolev
divergence, whose result is a scalar Sobolev function.
-/

@[expose] public noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory
open scoped ENNReal Sobolev

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The weak divergence of a zero-boundary vector field. -/
def ZeroBoundaryVectorSpace.divergence :
    H¹₀(Ω; ℝ^n) →L[ℝ] DerivLp n 2 Ω :=
  (∑ i : Fin n, (wkpCoordinateCLM (singleDerivIndex n i)).comp
    (ContinuousLinearMap.proj i)).comp ZeroBoundaryVectorSpace.toSobolev

/-- For a zero-boundary vector field, the shared divergence notation returns the
positive sum of diagonal weak derivatives as an `L²` class. -/
instance ZeroBoundaryVectorSpace.instDivergence :
    PDE.Divergence (H¹₀(Ω; ℝ^n)) (DerivLp n 2 Ω) where
  divergence u := ZeroBoundaryVectorSpace.divergence u

/-- The divergence is the sum of matching scalar derivative coordinates. -/
theorem ZeroBoundaryVectorSpace.divergence_apply (u : H¹₀(Ω; ℝ^n)) :
    ∇· u = ∑ i : Fin n, derivCoordCLM i (u i) := by
  simp only [ZeroBoundaryVectorSpace.divergence, ContinuousLinearMap.comp_apply, sum_apply]
  rfl

/-- The negative-divergence integration-by-parts convention is the negative of
the continuous divergence map. -/
theorem ZeroBoundaryVectorSpace.negativeDivergence_toSobolev (u : H¹₀(Ω; ℝ^n)) :
    negativeDivergence (ZeroBoundaryVectorSpace.toSobolev u) = -(∇· u) := by
  simp only [negativeDivergence, ZeroBoundaryVectorSpace.divergence,
    ContinuousLinearMap.comp_apply, sum_apply, ContinuousLinearMap.proj_apply]

public meta section

open Lean PrettyPrinter.Delaborator SubExpr

/-- Display the applied zero-boundary divergence in mathematical notation. -/
@[delab app.DFunLike.coe]
def ZeroBoundaryVectorSpace.delabDivergence : Delab := whenPPOption getPPNotation do
  guard <| !(← getPPOption getPPExplicit)
  let e ← getExpr
  guard <| e.getAppNumArgs == 6
  guard <| (e.getArg! 4).isAppOf ``ZeroBoundaryVectorSpace.divergence
  let u ← withAppArg delab
  `(∇· $u)

end

end SobolevSpace.GraphSpace
