/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Regularity.Interior.ClassicalPoisson
public import PDE.Elliptic.Regularity.Interior.LaplaceEigenfunction
public import PDE.Elliptic.Variational.FirstEigenfunction
public import PDE.Spaces.Sobolev.Inequalities.Morrey.HigherOrder.Interior
import PDE.Analysis.MeasureTheory.LocalRepresentative

/-!
# Classical Dirichlet eigenfunctions and the positive first eigenfunction

Interior Sobolev bootstrap and local Morrey reconstruction give classical representatives
of weak Laplace eigenfunctions on arbitrary open domains in positive dimension. The weak
equation then becomes the pointwise Laplace equation. No boundary atlas or regularity of
the boundary is used.

On connected domains, a nonnegative nonzero eigenfunction has a strictly positive interior
representative. When the least Rayleigh quotient is attained, its eigenspace is
one-dimensional. On bounded nonempty connected open domains, these conclusions apply to the
normalized first eigenfunction constructed by compact variational spectral theory.

For `L = -Δ` these are parts (i)-(iii) of Evans's §6.5.1, Theorem 2 (Variational principle for the
principal eigenvalue). `exists_pos_first_dirichlet_eigenfunction` gives a normalized eigenfunction,
positive in the domain, whose eigenvalue is the least Rayleigh quotient, as in (5), and
`eq_smul_of_first_dirichlet_eigenfunctions_of_pos_dimension` shows that any two weak eigenfunctions
for that eigenvalue are proportional. The interior regularity is the counterpart of Evans's remark
after §6.5.1, Theorem 1, that eigenfunctions are smooth inside the domain by the regularity theory
of §6.3.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Graduate Studies in Mathematics 19,
  American Mathematical Society, 2010, §6.5.1, Theorem 1 and the remark after it, p. 355; Theorem 2
  (Variational principle for the principal eigenvalue) and its proof, pp. 356-360.
  <https://doi.org/10.1090/gsm/019>
-/

@[expose] public section

open PDE (laplacian)

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- Every weak Laplace eigenfunction has representatives of every finite classical
order in the interior. The neighborhoods, higher Sobolev fields, and compatible
classical representatives are constructed from the weak equation. -/
theorem IsWeakPoissonSolution.exists_contDiffAt_eigenfunction_representative
    (hn : 0 < n) (k : ℕ) {lambda : ℝ} {u : H¹₀(Ω)}
    (hu : IsWeakPoissonSolution (n := n) (Ω := Ω)
      (lambda • baseCoordCLM (n := n) (Ω := Ω) u) u) :
    ∃ f : ℝ^n → ℝ, (∀ x ∈ Ω, ContDiffAt ℝ k f x) ∧
      f =ᵐ[domainMeasure n Ω] (baseCoordCLM (n := n) (Ω := Ω) u : ℝ^n → ℝ) := by
  apply MeasureTheory.exists_contDiffAt_ae_eq_of_locally (μ := volume)
  intro x hx
  obtain ⟨V, hV, hxV, hVΩ, W, hW⟩ :=
    BoundaryRegularity.exists_dirichletEigenfunction_interiorRegularity_open_neighborhood_of_compact
      (k + n / 2) lambda u hu {x} isCompact_singleton (by simpa using hx)
  obtain ⟨f, hreg, hrep⟩ := exists_contDiffAt_representative_of_order (k := k)
    hn hV W (by omega)
  exact ⟨V, hV, hxV (by simp), hVΩ, f,
    (fun y hy ↦ (hreg y hy).contDiffWithinAt), hrep.trans hW⟩

/-- The weak equation `−Δu = λu` constructs a `C²` interior representative satisfying
that equation pointwise. No representative or pointwise equation is an input. -/
theorem IsWeakPoissonSolution.exists_classical_eigenfunction_representative
    (hn : 0 < n) {lambda : ℝ} {u : H¹₀(Ω)}
    (hu : IsWeakPoissonSolution (n := n) (Ω := Ω)
      (lambda • baseCoordCLM (n := n) (Ω := Ω) u) u) :
    ∃ f : ℝ^n → ℝ,
      (baseCoordCLM (n := n) (Ω := Ω) u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f ∧
      (∀ x ∈ Ω, ContDiffAt ℝ 2 f x) ∧
      ∀ x ∈ Ω, -laplacian f x = lambda * f x := by
  obtain ⟨f, hreg, hrep⟩ :=
    IsWeakPoissonSolution.exists_contDiffAt_eigenfunction_representative hn 2 hu
  have hforce :
      ((lambda • baseCoordCLM (n := n) (Ω := Ω) u : DerivLp n 2 Ω) : ℝ^n → ℝ)
        =ᵐ[domainMeasure n Ω] fun x ↦ lambda * f x := by
    filter_upwards [Lp.coeFn_smul lambda (baseCoordCLM (n := n) (Ω := Ω) u), hrep]
      with x hsm hr
    rw [hsm]
    simp only [Pi.smul_apply, smul_eq_mul, hr]
  refine ⟨f, hrep.symm, hreg, ?_⟩
  exact IsWeakPoissonSolution.neg_laplacian_eq_of_representatives
    hu hrep.symm hreg hforce
    ((show ContinuousOn f Ω from
      fun x hx ↦ (hreg x hx).continuousAt.continuousWithinAt).const_mul lambda)

/-- A variational Dirichlet Laplace eigenfunction has a classical interior
representative solving the pointwise eigen-equation on every open domain. -/
theorem exists_classical_representative_of_weak_dirichlet_eigenfunction
    (hn : 0 < n) (hΩ : IsOpen Ω) {lambda : ℝ} {u : H¹₀(Ω)}
    (hu : Weak.IsWeakEigenfunction (V := H¹₀(Ω))
      (dirichletForm (n := n) (Ω := Ω))
      (massFormCLM (n := n) (Ω := Ω)) lambda u) :
    ∃ f : ℝ^n → ℝ,
      (baseCoordCLM (n := n) (Ω := Ω) u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f ∧
      (∀ x ∈ Ω, ContDiffAt ℝ 2 f x) ∧
      ∀ x ∈ Ω, -laplacian f x = lambda * f x := by
  apply IsWeakPoissonSolution.exists_classical_eigenfunction_representative hn
  apply (isWeakSolution_iff_isWeakPoissonSolution (n := n) (Ω := Ω)
    hΩ (lambda • baseCoordCLM (n := n) (Ω := Ω) u) u).mp
  intro v
  have hload : loadFunctional (n := n) (Ω := Ω)
      (lambda • baseCoordCLM (n := n) (Ω := Ω) u) v =
      lambda * massFormCLM (n := n) (Ω := Ω) u v := by
    rw [loadFunctional_apply, real_inner_smul_left, massFormCLM_apply]
  exact (hu.2 v).trans hload.symm

/-- A nonnegative nonzero weak Dirichlet Laplace eigenfunction has a strictly positive
classical representative throughout a connected open domain. Boundedness and boundary
regularity are not required. The sign of its eigenvalue follows from its energy identity. -/
theorem exists_pos_representative_of_nonnegative_weak_dirichlet_eigenfunction
    (hn : 0 < n) (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    {lambda : ℝ} {u : H¹₀(Ω)}
    (hu : Weak.IsWeakEigenfunction (V := H¹₀(Ω))
      (dirichletForm (n := n) (Ω := Ω))
      (massFormCLM (n := n) (Ω := Ω)) lambda u)
    (hnonneg : ∀ᵐ x ∂domainMeasure n Ω,
      0 ≤ (baseCoordCLM (n := n) (Ω := Ω) u) x) :
    ∃ f : ℝ^n → ℝ,
      (baseCoordCLM (n := n) (Ω := Ω) u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f ∧
      (∀ x ∈ Ω, ContDiffAt ℝ 2 f x) ∧
      (∀ x ∈ Ω, -laplacian f x = lambda * f x) ∧
      ∀ x ∈ Ω, 0 < f x := by
  obtain ⟨f, hrep, hreg, heq⟩ :=
    exists_classical_representative_of_weak_dirichlet_eigenfunction hn hΩ hu
  have hmass : 0 < ‖baseCoordCLM (n := n) (Ω := Ω) u‖ ^ 2 := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    intro hzero
    exact hu.1 ((baseCoordCLM_injective hΩ)
      (hzero.trans (baseCoordCLM (n := n) (Ω := Ω)).map_zero.symm))
  have henergy := hu.2 u
  rw [massFormCLM_apply, real_inner_self_eq_norm_sq] at henergy
  have hlambda : 0 ≤ lambda :=
    nonneg_of_mul_nonneg_left
      (henergy ▸ dirichletForm_self_nonneg (n := n) (Ω := Ω) u) hmass
  exact ⟨f, hrep, hreg, heq,
    pos_of_nonnegative_h10_representative hΩ hconn hu.1 hnonneg hlambda hrep hreg heq⟩

/-- In positive dimension the least Dirichlet Rayleigh eigenspace is one-dimensional
on a connected open domain; the domain is nonempty because the least quotient is attained.
Classical regularity is proved from the weak equation, and is not a hypothesis on the
eigenspace. -/
theorem eq_smul_of_first_dirichlet_eigenfunctions_of_pos_dimension
    (hn : 0 < n) (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (lambda : ℝ)
    (hleast : IsLeast ((fun v : H¹₀(Ω) ↦
      dirichletForm v v / ‖baseCoordCLM (n := n) (Ω := Ω) v‖ ^ 2) ''
        {v | v ≠ 0}) lambda)
    {u v : H¹₀(Ω)}
    (hu : Weak.IsWeakEigenfunction (V := H¹₀(Ω))
      (dirichletForm (n := n) (Ω := Ω))
      (massFormCLM (n := n) (Ω := Ω)) lambda u)
    (hv : Weak.IsWeakEigenfunction (V := H¹₀(Ω))
      (dirichletForm (n := n) (Ω := Ω))
      (massFormCLM (n := n) (Ω := Ω)) lambda v) :
    ∃ c : ℝ, v = c • u := by
  have hne : Ω.Nonempty := by
    obtain ⟨w, hw, -⟩ := hleast.1
    refine nonempty_iff_ne_empty.mpr fun hempty ↦ hw (baseCoordCLM_injective hΩ (Lp.ext ?_))
    refine ae_iff.mpr (measure_mono_null (subset_univ _) ?_)
    simp [domainMeasure, hempty]
  exact eq_smul_of_first_dirichlet_eigenfunctions hΩ hconn hne lambda hleast
    (fun _ hw ↦ exists_classical_representative_of_weak_dirichlet_eigenfunction hn hΩ hw)
    hu hv

/-- A bounded connected nonempty open domain has a normalized first Dirichlet
Laplace eigenfunction with a strictly positive `C²` interior representative.
Its eigenvalue is positive and is the attained least `L²` Rayleigh quotient.
No boundary smoothness or continuity up to the boundary is asserted. -/
theorem exists_pos_first_dirichlet_eigenfunction
    (hn : 0 < n) (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hconn : IsPreconnected Ω) (hne : Ω.Nonempty) :
    ∃ (lambda : ℝ) (u : H¹₀(Ω)) (f : ℝ^n → ℝ), 0 < lambda ∧
      ‖baseCoordCLM (n := n) (Ω := Ω) u‖ = 1 ∧
      Weak.IsWeakEigenfunction (V := H¹₀(Ω))
        (dirichletForm (n := n) (Ω := Ω))
        (massFormCLM (n := n) (Ω := Ω)) lambda u ∧
      (baseCoordCLM (n := n) (Ω := Ω) u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f ∧
      (∀ x ∈ Ω, ContDiffAt ℝ 2 f x) ∧
      (∀ x ∈ Ω, -laplacian f x = lambda * f x) ∧
      (∀ x ∈ Ω, 0 < f x) ∧
      IsLeast ((fun v : H¹₀(Ω) ↦
        dirichletForm v v / ‖baseCoordCLM (n := n) (Ω := Ω) v‖ ^ 2) ''
          {v | v ≠ 0}) lambda := by
  have hidentity : variableCoeffForm (identityCoefficientOperator (n := n) (Ω := Ω)) =
      dirichletForm (n := n) (Ω := Ω) := by
    ext v w
    exact variableCoeffForm_identity v w
  obtain ⟨lambda, u, hpos, hnorm, hu, hleast⟩ :=
    exists_first_variableCoeff_eigenfunction hn hΩ hbounded hne
      (identityCoefficientOperator (n := n) (Ω := Ω))
      integratedElliptic_identity symmetricCoefficientOperator_identity
  rw [hidentity] at hu hleast
  let v : H¹₀(Ω) := absoluteValueH10 hΩ u
  have hv : Weak.IsWeakEigenfunction (V := H¹₀(Ω))
      (dirichletForm (n := n) (Ω := Ω))
      (massFormCLM (n := n) (Ω := Ω)) lambda v :=
    isWeakEigenfunction_absoluteValueH10_dirichlet hΩ lambda hleast hu
  have hvnonneg : ∀ᵐ x ∂domainMeasure n Ω,
      0 ≤ (baseCoordCLM (n := n) (Ω := Ω) v) x := by
    filter_upwards [absoluteValueH10_base_ae hΩ u] with x hx
    rw [hx]
    exact abs_nonneg _
  obtain ⟨f, hrep, hreg, heq, hfpos⟩ :=
    exists_pos_representative_of_nonnegative_weak_dirichlet_eigenfunction hn hΩ hconn hv hvnonneg
  exact ⟨lambda, v, f, hpos, (norm_base_absoluteValueH10 hΩ u).trans hnorm,
    hv, hrep, hreg, heq, hfpos, hleast⟩

end SobolevSpace.GraphSpace
