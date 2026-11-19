/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Eigenfunction.Full.SpectralBound
public import PDE.Elliptic.Variational.Eigenfunction.Full.ComplexSimplicity

/-!
# The principal eigenpair of the full Dirichlet operator

Smooth coefficients and connected smooth graph geometry construct a
positive normalized eigenfunction in the `H² ∩ H¹₀` domain. Its
eigenvalue is positive, its real and complex eigenspaces are geometrically
simple, and it bounds the real part of every complex weak eigenvalue.

This is Evans's §6.5.2, Theorem 3 (Principal eigenvalue for nonsymmetric elliptic operators). Evans
states it for an operator in nondivergence form with coefficients in `C^∞(Ū)` on a bounded connected
domain with smooth boundary, with `c ≥ 0`, (22); we use the full divergence form with smooth
coefficients, a nonnegative potential and a boundary that is locally a `C^k` graph for every `k`.
The spectral ordering is `λ₁ ≤ Re λ`, and the eigenspace result asserts geometric, not algebraic,
simplicity, as in Evans's part (iii).

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.5.2, the assumptions on the operator and (22), p. 360, and
  Theorem 3 (Principal eigenvalue for nonsymmetric elliptic operators), p. 361.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- The full principal eigenpair, from coefficients and geometry
alone. The complex comparison quantifies every complex weak
eigenfunction. Simplicity identifies whole Sobolev graphs. -/
theorem exists_principal_eigenpair
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconn : IsConnected Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x) :
    ∃ (r : ℝ) (u : H¹₀(Ω)) (Z : W^{2,2}(Ω)) (z : ℝ^n → ℝ),
      0 < r ∧ ‖baseCoordCLM u‖ = 1 ∧
      wkpBaseCoordinateCLM Z = baseCoordCLM u ∧
      wkpBaseCoordinateCLM (P.load hopen hbounded 0 Z) = r • baseCoordCLM u ∧
      ContDiffOn ℝ (⊤ : ℕ∞) z (closure Ω) ∧
      (∀ k, ContDiffUpToBoundary k z Ω) ∧
      z =ᵐ[domainMeasure n Ω] weakSolutionBase u ∧
      (∀ x ∈ frontier Ω, z x = 0) ∧ (∀ x ∈ Ω, 0 < z x) ∧
      (∀ x ∈ Ω, P.classicalLoad z x = r * z x) ∧
      (∀ v : H¹₀(Ω),
        P.form hopen hbounded u v = r * ⟪baseCoordCLM u, baseCoordCLM v⟫_ℝ) ∧
      (∀ v : H¹₀(Ω),
        (∀ w : H¹₀(Ω),
          P.form hopen hbounded v w = r * ⟪baseCoordCLM v, baseCoordCLM w⟫_ℝ) →
        ∃ c : ℝ, v = c • u) ∧
      (∀ (lambda : ℂ) (U : ComplexWkSpaceOn n 1 Ω),
        U.re ∈ h10SubmoduleOn (n := n) (Ω := Ω) →
        U.im ∈ h10SubmoduleOn (n := n) (Ω := Ω) →
        U.1 (baseIndex n 1) ≠ 0 →
        (∀ v : H¹₀(Ω), P.complexForm hopen hbounded U v =
          lambda * ∫ x, U.1 (baseIndex n 1) x *
            (baseCoordCLM v x : ℂ) ∂domainMeasure n Ω) →
        r ≤ lambda.re) ∧
      ∀ U : ComplexWkSpaceOn n 1 Ω,
        U.re ∈ h10SubmoduleOn (n := n) (Ω := Ω) →
        U.im ∈ h10SubmoduleOn (n := n) (Ω := Ω) →
        (∀ v : H¹₀(Ω), P.complexForm hopen hbounded U v =
          (r : ℂ) * ∫ x, U.1 (baseIndex n 1) x *
            (baseCoordCLM v x : ℂ) ∂domainMeasure n Ω) →
        ∃ c : ℂ, U = complexOfRealGraphs ((c.re • u).1) ((c.im • u).1) := by
  obtain ⟨r, u, z, hr, hnorm, hz, hzraw, hzae, hboundary, hzpos, hload, heq, hbound⟩ :=
    P.exists_pos_eigenpair_spectral_bound hopen hbounded hconn hgraph halpha hell hc
  let Z := (hzraw 2).toWkpSpaceOn hopen hbounded 2
  have hbase : wkpBaseCoordinateCLM Z = baseCoordCLM u :=
    Lp.ext (((hzraw 2).toWkpSpaceOn_base_ae hopen hbounded 2).trans hzae)
  have hZload : wkpBaseCoordinateCLM (P.load hopen hbounded 0 Z) =
      r • baseCoordCLM u := by
    change wkpBaseCoordinateCLM
      (P.load hopen hbounded 0 ((hzraw 2).toWkpSpaceOn hopen hbounded 2)) = _
    rw [P.load_toWkpSpaceOn]
    apply Lp.ext
    filter_upwards [(P.classicalLoad_regular hopen hbounded (hzraw 2)).toWkpSpaceOn_base_ae
      hopen hbounded 2, Lp.coeFn_smul r (baseCoordCLM u), hzae,
      ae_restrict_mem hopen.measurableSet] with x hf hs hu hx
    change z x = baseCoordCLM u x at hu
    simpa only [hf, hs, Pi.smul_apply, smul_eq_mul, ← hu] using hload x hx
  have hunonneg : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ baseCoordCLM u x := by
    filter_upwards [hzae, ae_restrict_mem hopen.measurableSet] with x hx hxΩ
    exact (hzpos x hxΩ).le.trans_eq hx
  have hune : baseCoordCLM u ≠ 0 := by
    intro hu
    rw [hu, norm_zero] at hnorm
    exact zero_ne_one hnorm
  refine ⟨r, u, Z, z, hr, hnorm, hbase, hZload, hz, hzraw, hzae, hboundary,
    hzpos, hload, heq, ?_, hbound, ?_⟩
  · intro v hv
    exact P.eq_smul_of_nonneg_eigenfunction hopen hbounded hconn hgraph
      halpha hell hc hr hunonneg hune heq hv
  · intro U hUr hUi hUeq
    exact P.eq_complexOfRealGraphs_of_nonneg_eigenfunction hopen hbounded hconn hgraph
      halpha hell hc hr u hunonneg hune heq U hUr hUi hUeq

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
