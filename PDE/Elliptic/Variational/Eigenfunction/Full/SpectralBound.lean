/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Eigenfunction.Full.Adjoint
public import PDE.Elliptic.Variational.Eigenfunction.Full.ResolventComparison
public import PDE.Elliptic.Regularity.SolutionOperator.HigherLoad.Complex

/-!
# A positive eigenpair below every complex real part

Smooth coefficients and smooth graph geometry construct both the
positive Dirichlet eigenfunction and its positive adjoint weight. Every
complex weak eigenvalue then satisfies `λ₁ ≤ Re λ`.

The reference is Evans, *Partial Differential Equations*, §6.5.2, Theorem 3.
The adjoint-weight argument gives the ordering stated above. Geometric
simplicity is a separate step.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- Full elliptic data construct a positive normalized eigenpair
whose eigenvalue bounds the real part of every complex Dirichlet weak
eigenvalue. All inverses, positivity, and adjoint data are derived. -/
theorem exists_pos_eigenpair_spectral_bound
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconn : IsConnected Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x) :
    ∃ (r : ℝ) (u : H¹₀(Ω)) (z : ℝ^n → ℝ),
      0 < r ∧ ‖baseCoordCLM u‖ = 1 ∧
      ContDiffOn ℝ (⊤ : ℕ∞) z (closure Ω) ∧
      (∀ k, ContDiffUpToBoundary k z Ω) ∧
      z =ᵐ[domainMeasure n Ω] weakSolutionBase u ∧
      (∀ x ∈ frontier Ω, z x = 0) ∧ (∀ x ∈ Ω, 0 < z x) ∧
      (∀ x ∈ Ω, P.classicalLoad z x = r * z x) ∧
      (∀ v : H¹₀(Ω),
        P.form hopen hbounded u v = r * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ) ∧
      ∀ (lambda : ℂ) (U : ComplexWkSpaceOn n 1 Ω),
        U.re ∈ h10SubmoduleOn (n := n) (Ω := Ω) →
        U.im ∈ h10SubmoduleOn (n := n) (Ω := Ω) →
        U.1 (baseIndex n 1) ≠ 0 →
        (∀ v : H¹₀(Ω), P.complexForm hopen hbounded U v =
          lambda * ∫ x, U.1 (baseIndex n 1) x *
            (baseCoordCLM v x : ℂ) ∂domainMeasure n Ω) →
        r ≤ lambda.re := by
  obtain ⟨r, u, z, hr, hnorm, hz, hzraw, hzae, hboundary, hzpos, hload, heq⟩ :=
    P.exists_pos_eigenpair hopen hbounded hconn hgraph halpha hell hc
  have hunonneg : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ baseCoordCLM u x := by
    filter_upwards [hzae, ae_restrict_mem hopen.measurableSet] with x hx hxΩ
    exact (hzpos x hxΩ).le.trans_eq hx
  have hune : baseCoordCLM u ≠ 0 := by
    intro hu
    rw [hu, norm_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨q, w, _, _, _, hwae, _, hwpos, hqeq⟩ :=
    P.exists_pos_adjoint_eigenfunction hopen hbounded hconn hgraph halpha hell
      r u hunonneg hune heq
  have hqpos : ∀ᵐ x ∂domainMeasure n Ω, 0 < baseCoordCLM q x := by
    filter_upwards [hwae, ae_restrict_mem hopen.measurableSet] with x hx hxΩ
    exact (hwpos x hxΩ).trans_eq hx
  refine ⟨r, u, z, hr, hnorm, hz, hzraw, hzae, hboundary, hzpos, hload, heq, ?_⟩
  intro lambda U hUr hUi hUne hUeq
  exact P.le_re_of_complex_parts hopen hbounded hgraph halpha hell hc
    q hqpos hr hqeq U hUr hUi hUne lambda
    (fun v ↦ (P.parts_of_complexForm_eq hopen hbounded U hUr hUi lambda v (hUeq v)).1)
    (fun v ↦ (P.parts_of_complexForm_eq hopen hbounded U hUr hUi lambda v (hUeq v)).2)

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
