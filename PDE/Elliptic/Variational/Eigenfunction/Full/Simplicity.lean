/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Variational.Eigenfunction.Full.Sign
public import PDE.Elliptic.Variational.Eigenfunction.Full.Adjoint
import PDE.Analysis.MeasureTheory.Lp.Nonvanishing
import PDE.Elliptic.Variational.WeakSpectrum

/-!
# Geometric simplicity of the positive full Dirichlet eigenvalue

Every nonzero vector in the weak eigenspace has a nowhere zero
continuous representative. Applied to a linear combination vanishing at one point,
the subspace argument proves that this eigenspace is one-dimensional. The
simplicity is geometric.
-/

@[expose] public noncomputable section

open scoped Sobolev

namespace SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

open scoped SobolevSpace.GraphSpace

variable {n : ℕ} [Fact (0 < n)] {Ω : Set (ℝ^n)}

/-- A positive adjoint eigenfunction forces geometric simplicity of the
corresponding real weak eigenspace. -/
theorem eq_smul_of_pos_adjoint_eigenfunction
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconn : IsConnected Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x)
    (q : H¹₀(Ω)) (hq : ∀ᵐ x ∂domainMeasure n Ω, 0 < baseCoordCLM q x)
    {r : ℝ} (hr : 0 < r)
    (hqeq : ∀ v : H¹₀(Ω),
      P.form hopen hbounded v q = r * ⟪baseCoordCLM v, baseCoordCLM q⟫_ℝ)
    {u v : H¹₀(Ω)} (hune : u ≠ 0)
    (hueq : ∀ w : H¹₀(Ω),
      P.form hopen hbounded u w = r * ⟪baseCoordCLM u, baseCoordCLM w⟫_ℝ)
    (hveq : ∀ w : H¹₀(Ω),
      P.form hopen hbounded v w = r * ⟪baseCoordCLM v, baseCoordCLM w⟫_ℝ) :
    ∃ c : ℝ, v = c • u := by
  let E := Weak.weakEigenspace (P.form hopen hbounded) massFormCLM r
  have hmem (w : H¹₀(Ω)) :
      w ∈ E ↔ ∀ t : H¹₀(Ω),
        P.form hopen hbounded w t = r * ⟪baseCoordCLM w, baseCoordCLM t⟫_ℝ := by
    simp only [E, Weak.mem_weakEigenspace_iff, massFormCLM_apply]
  apply E.exists_eq_smul_of_nonvanishing_representatives hopen hconn.nonempty
    baseCoordCLM.toLinearMap _ ((hmem u).mpr hueq) hune ((hmem v).mpr hveq)
  intro w hw hwne
  have hbasene : baseCoordCLM w ≠ 0 := by
    intro hzero
    exact hwne ((baseCoordCLM_injective hopen) (hzero.trans (map_zero baseCoordCLM).symm))
  exact P.exists_nonvanishingRepresentative_of_eigenfunction hopen hbounded hconn.isPreconnected
    hgraph halpha hell hc q hq hr hqeq w hbasene ((hmem w).mp hw)

/-- Any nonnegative nonzero eigenfunction at a positive real eigenvalue
spans its weak eigenspace. The adjoint witness is constructed from
the coefficients and geometry. -/
theorem eq_smul_of_nonneg_eigenfunction
    (P : SmoothFullCoefficients n Ω) (hopen : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hconn : IsConnected Ω)
    (hgraph : ∀ k : ℕ, Boundary.HasContDiffGraphBoundary k Ω)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hell : ∀ x ∈ Ω, MatrixEllipticLowerBound (P.principal x) alpha)
    (hc : ∀ x ∈ Ω, 0 ≤ P.potential x)
    {r : ℝ} (hr : 0 < r) {u v : H¹₀(Ω)}
    (hu : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ baseCoordCLM u x)
    (hune : baseCoordCLM u ≠ 0)
    (hueq : ∀ w : H¹₀(Ω),
      P.form hopen hbounded u w = r * ⟪baseCoordCLM u, baseCoordCLM w⟫_ℝ)
    (hveq : ∀ w : H¹₀(Ω),
      P.form hopen hbounded v w = r * ⟪baseCoordCLM v, baseCoordCLM w⟫_ℝ) :
    ∃ c : ℝ, v = c • u := by
  obtain ⟨q, z, _, _, _, hzae, _, hzpos, hqeq⟩ :=
    P.exists_pos_adjoint_eigenfunction hopen hbounded hconn hgraph halpha hell
      r u hu hune hueq
  have hq : ∀ᵐ x ∂domainMeasure n Ω, 0 < baseCoordCLM q x := by
    filter_upwards [hzae, ae_restrict_mem hopen.measurableSet] with x hx hxΩ
    exact (hzpos x hxΩ).trans_eq hx
  apply P.eq_smul_of_pos_adjoint_eigenfunction hopen hbounded hconn hgraph
    halpha hell hc q hq hr hqeq _ hueq hveq
  intro hu
  exact hune (by rw [hu, map_zero])

end SobolevSpace.GraphSpace.BoundaryRegularity.SmoothFullCoefficients
