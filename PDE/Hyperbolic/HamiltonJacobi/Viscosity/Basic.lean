/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Hamilton–Jacobi touching tests on space × time

For a real Hilbert space `E`, a point of `E × ℝ` is `(x, t)`. The equation is
`u_t + H(Dₓu, x) = 0`; the spatial gradient uses the inner product on `E`.
No inner product on the product, or finite-dimensional assumption, is needed.
The two touching-test inequalities are (16) and (17) in the definition of viscosity solution in
Evans, §10.1.1, on an arbitrary open spacetime domain.

## Main definitions

* `IsSpatialViscositySubsolution`: the inequality `≤ 0` at every upper contact.
* `IsSpatialViscositySupersolution`: the inequality `≥ 0` at every lower contact.
* `IsSpatialViscositySolution`: both inequalities.

## Implementation notes

Tests are locally `C¹` at the contact point, expressed by `ContDiffAt ℝ 1`.
They need not be globally `C¹`. Evans tests with `C^∞` functions; for a continuous Hamiltonian
in finite dimensions, `SmoothTests` shows that the two test classes give the same
semicontinuous sub- and supersolutions. The predicates impose no continuity or
semicontinuity on the candidate. The initial-value class in `InitialValue` adds boundedness
and uniform continuity on each finite closed time slab.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §10.1.1, definition of viscosity solution, (16)-(17).
  <https://doi.org/10.1090/gsm/019>
-/

open scoped Gradient

@[expose] public section

noncomputable section

namespace HamiltonJacobi

open Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A subsolution of `u_t + H(Dₓu, x) = 0`, tested at upper contacts relative
to an open spacetime domain. Each test is `C¹` near its contact point. -/
def IsSpatialViscositySubsolution
    (H : E → E → ℝ) (U : Set (E × ℝ)) (u : E × ℝ → ℝ) : Prop :=
  IsOpen U ∧ ∀ z ∈ U, ∀ φ : E × ℝ → ℝ, ContDiffAt ℝ 1 φ z →
    IsLocalMaxOn (fun y ↦ u y - φ y) U z →
      fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1 ≤ 0

/-- A supersolution of `u_t + H(Dₓu, x) = 0`, tested at lower contacts
relative to an open spacetime domain using tests that are locally `C¹`. -/
def IsSpatialViscositySupersolution
    (H : E → E → ℝ) (U : Set (E × ℝ)) (u : E × ℝ → ℝ) : Prop :=
  IsOpen U ∧ ∀ z ∈ U, ∀ φ : E × ℝ → ℝ, ContDiffAt ℝ 1 φ z →
    IsLocalMinOn (fun y ↦ u y - φ y) U z →
      0 ≤ fderiv ℝ φ z (0, 1) + H (∇ (fun x ↦ φ (x, z.2)) z.1) z.1

/-- Both touching-test inequalities for `u_t + H(Dₓu, x) = 0` on `U`. -/
def IsSpatialViscositySolution
    (H : E → E → ℝ) (U : Set (E × ℝ)) (u : E × ℝ → ℝ) : Prop :=
  IsSpatialViscositySubsolution H U u ∧ IsSpatialViscositySupersolution H U u

omit [CompleteSpace E] in
/-- Restricting the joint derivative to spatial directions gives the
Fréchet derivative of the fixed-time slice. -/
theorem fderiv_spaceSlice {f : E × ℝ → ℝ} {z : E × ℝ} (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ (fun x ↦ f (x, z.2)) z.1 =
      (fderiv ℝ f z).comp ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) :=
  (hf.hasFDerivAt.comp z.1 ((hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1))).fderiv

/-- The spatial gradient is the Riesz representative of the joint
Fréchet derivative restricted to directions `(h, 0)`. -/
theorem gradient_spaceSlice_eq {f : E × ℝ → ℝ} {z : E × ℝ} (hf : DifferentiableAt ℝ f z) :
    ∇ (fun x ↦ f (x, z.2)) z.1 = (InnerProductSpace.toDual ℝ E).symm
      ((fderiv ℝ f z).comp ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ))) := by
  rw [gradient, fderiv_spaceSlice hf]

end HamiltonJacobi

end
