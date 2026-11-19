/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.DirichletInverse.Bijective
import PDE.Spaces.Sobolev.Compactness.Rellich.ZeroExtension

/-!
# The full Dirichlet inverse on `L²`

The weak inverse maps loads to `H¹₀` functions. Composing with the
base-coordinate inclusion gives the compact `L²` solution operator. Both maps
use Mathlib's continuous linear inverse, and the coefficient and domain
hypotheses prove its two-sided inverse identities.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- The weak inverse evaluated on an `L²` forcing. -/
def dirichletSolution (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    DerivLp n 2 Ω →L[ℝ] H¹₀(Ω) :=
  (P.form hopen hbounded).inverse.comp (h10L2GelfandTriple hopen).pivotToDual

/-- The same Dirichlet solution viewed in the `L²` pivot space. -/
def l2SolutionOperator (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    DerivLp n 2 Ω →L[ℝ] DerivLp n 2 Ω :=
  baseCoordCLM.comp (P.dirichletSolution hopen hbounded)

/-- Rellich compactness applies to the full Dirichlet inverse, regardless of
whether its lower-order part is symmetric. -/
theorem isCompactOperator_l2SolutionOperator (P : SmoothFullCoefficients n Ω)
    (hopen : IsOpen Ω) (hbounded : Bornology.IsBounded Ω) :
    IsCompactOperator (P.l2SolutionOperator hopen hbounded) :=
  (baseCoordCLM.isCompactOperator_of_bounded hopen.measurableSet hbounded).comp_clm
    (P.dirichletSolution hopen hbounded)

/-- When the full form is invertible, the constructed inverse satisfies the weak equation for
every `L²` load and every `H¹₀` test. -/
theorem form_dirichletSolution_of_isInvertible
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hinv : (P.form hopen hbounded).IsInvertible)
    (f : DerivLp n 2 Ω) (v : H¹₀(Ω)) :
    P.form hopen hbounded (P.dirichletSolution hopen hbounded f) v =
      ⟪f, baseCoordCLM v⟫_ℝ := by
  have h := hinv.self_apply_inverse ((h10L2GelfandTriple hopen).pivotToDual f)
  exact congrArg (fun ell : StrongDual ℝ (H¹₀(Ω)) ↦ ell v) h

variable [Fact (0 < n)]

/-- The maximum-principle data make the full form continuously invertible. -/
theorem isInvertible_form
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x) :
    (P.form hopen hbounded).IsInvertible := by
  have hbij := P.bijective_form hopen hbounded hgraph halpha hell hc
  exact ⟨ContinuousLinearEquiv.ofBijective (P.form hopen hbounded)
    (LinearMap.ker_eq_bot.mpr hbij.injective)
    (LinearMap.range_eq_top.mpr hbij.surjective),
    ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- The constructed inverse satisfies the weak equation for every `L²`
load and every `H¹₀` test. -/
theorem form_dirichletSolution
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x)
    (f : DerivLp n 2 Ω) (v : H¹₀(Ω)) :
    P.form hopen hbounded (P.dirichletSolution hopen hbounded f) v =
      ⟪f, baseCoordCLM v⟫_ℝ :=
  P.form_dirichletSolution_of_isInvertible hopen hbounded
    (P.isInvertible_form hopen hbounded hgraph halpha hell hc) f v

/-- The `L²` inverse is injective: zero solution forces zero load by density
of the test space. -/
theorem injective_l2SolutionOperator
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x) :
    Function.Injective (P.l2SolutionOperator hopen hbounded) :=
  (baseCoordCLM_injective hopen).comp
    ((P.isInvertible_form hopen hbounded hgraph halpha hell hc).inverse.injective.comp
      (h10L2GelfandTriple hopen).pivotToDual_injective)

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
