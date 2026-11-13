/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.SolutionOperator.DirichletInverse.Positivity
public import PDE.Elliptic.Regularity.SolutionOperator.DirichletInverse.Eigenfunction
public import PDE.Spaces.Sobolev.GraphSpace.Model.Complex
import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Coefficients.Shift
import PDE.Analysis.Spectral.Positive.LpComplexEigenvalue
import PDE.Analysis.Complex.Norm.RealPart

/-!
# Complex spectral comparison by Dirichlet resolvents

For every nonnegative shift, the elliptic hypotheses construct a
positive inverse on `L²`. A positive adjoint eigenfunction gives its exact
weighted integral identity. Modulus comparison therefore gives
`r + s ≤ |λ + s|` for every `s ≥ 0`, hence `r ≤ Re λ`.

The complex state is the complex Sobolev graph of `Eigenfunction.Complex`. Its coupled real
equations retain the full principal, drift, and potential terms.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- A positive adjoint eigenfunction bounds the real part of every
complex eigenvalue of the full Dirichlet operator. The positive shifted
inverses are derived from the coefficients and geometry. -/
theorem le_re_of_complex_parts
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x)
    (q : H¹₀(Ω)) (hq : ∀ᵐ x ∂domainMeasure n Ω, 0 < baseCoordCLM q x)
    {r : ℝ} (hr : 0 < r)
    (hqeq : ∀ v : H¹₀(Ω),
      P.form hopen hbounded v q = r * ⟪baseCoordCLM v, baseCoordCLM q⟫_ℝ)
    (U : ComplexWkSpaceOn n 1 Ω)
    (hUr : U.re ∈ h10SubmoduleOn (n := n) (Ω := Ω))
    (hUi : U.im ∈ h10SubmoduleOn (n := n) (Ω := Ω))
    (hUne : U.1 (baseIndex n 1) ≠ 0) (lambda : ℂ)
    (hre : ∀ v : H¹₀(Ω),
      P.form hopen hbounded ⟨U.re, hUr⟩ v =
        lambda.re * ⟪baseCoordCLM ⟨U.re, hUr⟩, baseCoordCLM v⟫_ℝ -
          lambda.im * ⟪baseCoordCLM ⟨U.im, hUi⟩, baseCoordCLM v⟫_ℝ)
    (him : ∀ v : H¹₀(Ω),
      P.form hopen hbounded ⟨U.im, hUi⟩ v =
        lambda.re * ⟪baseCoordCLM ⟨U.im, hUi⟩, baseCoordCLM v⟫_ℝ +
          lambda.im * ⟪baseCoordCLM ⟨U.re, hUr⟩, baseCoordCLM v⟫_ℝ) :
    r ≤ lambda.re := by
  apply Complex.le_re_of_forall_add_le_norm_add hr.le
  intro s hs
  let S := P.shiftPotential hopen s
  have hSc (x : ℝ^n) (hx : x ∈ Ω) : 0 ≤ S.potential x :=
    add_nonneg (hc x hx) hs
  let A := S.l2SolutionOperator hopen hbounded
  have hA := S.nonneg_l2SolutionOperator hopen hbounded hgraph halpha hell hSc
  have hqshift (v : H¹₀(Ω)) :
      S.form hopen hbounded v q = (r + s) * ⟪baseCoordCLM v, baseCoordCLM q⟫_ℝ := by
    change (P.shiftPotential hopen s).form hopen hbounded v q = _
    rw [form_shiftPotential, hqeq]
    ring
  have hweight (f : DerivLp n 2 Ω) :
      (r + s) * ⟪baseCoordCLM q, A f⟫_ℝ = ⟪baseCoordCLM q, f⟫_ℝ :=
    S.mul_inner_l2SolutionOperator_of_adjoint_eigenfunction hopen hbounded hgraph
      halpha hell hSc (r + s) q hqshift f
  let u : H¹₀(Ω) := ⟨U.re, hUr⟩
  let v : H¹₀(Ω) := ⟨U.im, hUi⟩
  have hur : u = S.dirichletSolution hopen hbounded
      ((lambda.re + s) • baseCoordCLM u - lambda.im • baseCoordCLM v) := by
    apply S.eq_dirichletSolution_of_form_eq hopen hbounded hgraph halpha hell hSc
    intro w
    rw [form_shiftPotential, hre, inner_sub_left, real_inner_smul_left,
      real_inner_smul_left]
    ring
  have hui : v = S.dirichletSolution hopen hbounded
      ((lambda.re + s) • baseCoordCLM v + lambda.im • baseCoordCLM u) := by
    apply S.eq_dirichletSolution_of_form_eq hopen hbounded hgraph halpha hell hSc
    intro w
    rw [form_shiftPotential, him, inner_add_left, real_inner_smul_left,
      real_inner_smul_left]
    ring
  have hreal : baseCoordCLM u =
      (lambda.re + s) • A (baseCoordCLM u) - lambda.im • A (baseCoordCLM v) := by
    have h := congrArg baseCoordCLM hur
    simpa only [map_sub, map_smul, A, l2SolutionOperator,
      ContinuousLinearMap.comp_apply] using h
  have himag : baseCoordCLM v =
      (lambda.re + s) • A (baseCoordCLM v) + lambda.im • A (baseCoordCLM u) := by
    have h := congrArg baseCoordCLM hui
    simpa only [map_add, map_smul, A, l2SolutionOperator,
      ContinuousLinearMap.comp_apply] using h
  apply A.toLinearMap.le_norm_of_pos_adjoint_weight hA (baseCoordCLM q) hq
    (add_pos_of_pos_of_nonneg hr hs) hweight (U.1 (baseIndex n 1)) hUne
    (lambda + (s : ℂ))
  · simpa only [Complex.add_re, Complex.ofReal_re, Complex.add_im,
      Complex.ofReal_im, add_zero, u, v, baseCoordCLM_apply, ComplexWkSpaceOn.re,
      ComplexWkSpaceOn.im, realCoordinateTuple, LinearMap.coe_mk, AddHom.coe_mk,
      WithLp.ofLp_toLp, ContinuousLinearMap.coe_coe] using hreal
  · simpa only [Complex.add_re, Complex.ofReal_re, Complex.add_im,
      Complex.ofReal_im, add_zero, u, v, baseCoordCLM_apply, ComplexWkSpaceOn.re,
      ComplexWkSpaceOn.im, realCoordinateTuple, LinearMap.coe_mk, AddHom.coe_mk,
      WithLp.ofLp_toLp, ContinuousLinearMap.coe_coe] using himag

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
