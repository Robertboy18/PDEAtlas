/-
Copyright (c) 2026 LeanPDE Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanPDE Team
-/

module

public import PDE.Elliptic.Classical.MaximumPrinciple.MatrixEigenfunction
public import PDE.Elliptic.Regularity.Coefficients.ClassicalEllipticity
public import PDE.Elliptic.Regularity.Interior.ClassicalEigenfunction
public import PDE.Elliptic.Variational.FirstEigenfunction
import PDE.Spaces.Sobolev.Approximation.Density.Global

/-!
# Positive weak eigenfunctions for variable coefficients

The interior regularity theorem constructs a classical representative of a weak
eigenfunction. Its divergence equation includes the drift obtained by differentiating
the coefficients. Continuity turns almost-everywhere nonnegativity and ellipticity into
pointwise inequalities, so the strong maximum principle applies to this representative.

A nonzero nonnegative weak eigenfunction is therefore strictly positive on a connected
domain. This implication needs neither symmetry nor a sign condition on the eigenvalue.
For a symmetric operator on a bounded domain, the variational construction supplies a
normalized first eigenfunction to which the same argument applies.

The coefficient assumptions below are those of the interior Sobolev bootstrap:
globally bounded, globally Lipschitz coefficients and sufficiently many bounded weak
derivatives on the domain. The coefficients also have locally `C¹` representatives,
which identify the classical drift. No boundary regularity is required.
Precisely, the domain coefficients lie in `W^{m+1,∞}(Ω)` with `3 + n / 2 ≤ m + 2`, using
natural number division. These regularity assumptions are stronger than those of the weak
eigenbasis in `PDE.Elliptic.Variational.DirichletSpectrum`, whose coefficients are only
measurable and bounded.
-/

@[expose] public section

open scoped Sobolev

noncomputable section

namespace SobolevSpace.GraphSpace

open MeasureTheory Set
open scoped ENNReal

variable {n : ℕ} {Ω : Set (ℝ^n)}

/-- A nonzero nonnegative interior weak eigenfunction has a strictly positive `C²`
representative on a connected domain. The weak equation supplies its regularity and
pointwise matrix equation. The eigenvalue may have either sign, and no boundary
condition or coefficient symmetry is assumed. -/
theorem IsInteriorWeakDivergenceSolution.exists_pos_eigenfunction_representative
    (hn : 0 < n) (hconn : IsPreconnected Ω)
    (m : ℕ) (hm : 3 + n / 2 ≤ m + 2)
    (A0 : Fin n → Fin n → DerivLp n ∞ univ)
    (a : Fin n → Fin n → ℝ^n → ℝ) (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (hA0 : ∀ i j, (A0 i j : ℝ^n → ℝ) =ᵐ[volume] a i j)
    (haC1 : ∀ i j x, x ∈ Ω → ContDiffAt ℝ 1 (a i j) x)
    {alpha : ℝ} (helliptic : AEUniformlyElliptic (n := n) (Ω := univ) A0 alpha)
    (A : Fin n → Fin n → W^{m + 1,∞}(Ω))
    (hA : ∀ i j, (wkpBaseCoordinateCLM (A i j) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        (restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A0 i j) : ℝ^n → ℝ))
    {lambda : ℝ} {u : H¹(Ω)}
    (hu : IsInteriorWeakDivergenceSolution
      (fun i j ↦ restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A0 i j))
      (lambda • wkpBaseCoordinateCLM u) u)
    (hne : u ≠ 0)
    (hnonneg : ∀ᵐ x ∂domainMeasure n Ω, 0 ≤ (wkpBaseCoordinateCLM u) x) :
    ∃ f : ℝ^n → ℝ,
      (wkpBaseCoordinateCLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f ∧
      (∀ x ∈ Ω, ContDiffAt ℝ 2 f x) ∧
      (∀ x ∈ Ω, EllipticMaximum.matrixOperator (fun y i j ↦ a i j y)
        (fun y ↦ WithLp.toLp 2 (fun j ↦ -(∑ i, (∂[i] (a i j)) y)))
        (fun _ ↦ 0) f x = lambda * f x) ∧
      ∀ x ∈ Ω, 0 < f x := by
  let : Fact (0 < n) := ⟨hn⟩
  obtain ⟨f, hrep, hreg, heq⟩ :=
    hu.exists_classical_eigenfunction_representative m hm A0 a C ha hA0 haC1
      helliptic A hA
  have hcont : ContinuousOn f Ω :=
    fun x hx ↦ (hreg x hx).continuousAt.continuousWithinAt
  have habs : f =ᵐ[domainMeasure n Ω] fun x ↦ |f x| := by
    filter_upwards [hrep, hnonneg] with x hr hx
    rw [← hr, abs_of_nonneg hx]
  have habsOn := Measure.eqOn_open_of_ae_eq (μ := volume) habs hu.isOpen hcont hcont.abs
  have hpointwise (x : ℝ^n) (hx : x ∈ Ω) : 0 ≤ f x := (abs_nonneg _).trans_eq (habsOn hx).symm
  have hpositive : ∃ x ∈ Ω, 0 < f x := by
    by_contra hnone
    push Not at hnone
    have hzero (x : ℝ^n) (hx : x ∈ Ω) : f x = 0 :=
      le_antisymm (hnone x hx) (hpointwise x hx)
    apply hne
    apply WkpSpaceOn.ext_of_base_ae hu.isOpen u 0
    change (wkpBaseCoordinateCLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω]
      (wkpBaseCoordinateCLM (0 : H¹(Ω)) : ℝ^n → ℝ)
    rw [map_zero]
    filter_upwards [hrep, ae_restrict_mem hu.isOpen.measurableSet,
      Lp.coeFn_zero ℝ (2 : ℝ≥0∞) (domainMeasure n Ω)] with x hr hx hz
    rw [hr, hzero x hx, hz]
    rfl
  have htrace : ContinuousOn (fun x ↦ ∑ i : Fin n, a i i x) Ω :=
    continuousOn_finsetSum _ fun i _ ↦ (ha i i).continuous.continuousOn
  have hdrift : ContinuousOn (fun y ↦ WithLp.toLp 2 (fun j ↦ -(∑ i, (∂[i] (a i j)) y))) Ω :=
    (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp_continuousOn <| continuousOn_pi.mpr
      fun j ↦ (continuousOn_finsetSum _ fun i _ x hx ↦
        (PDE.contDiffAt_partialDeriv 0 (haC1 i j x hx) i).continuousAt.continuousWithinAt).neg
  have hglobalrep (i j : Fin n) : (A0 i j : ℝ^n → ℝ)
      =ᵐ[domainMeasure n univ] a i j := by
    simpa only [domainMeasure, Measure.restrict_univ] using hA0 i j
  have hquad := helliptic.le_of_continuousOn isOpen_univ a hglobalrep
    (fun i j ↦ (ha i j).continuous.continuousOn)
  refine ⟨f, hrep, hreg, heq, ?_⟩
  apply EllipticMaximum.pos_of_nonneg_of_matrix_eigenfunction
    hu.isOpen hconn (fun y i j ↦ a i j y)
    (fun y ↦ WithLp.toLp 2 (fun j ↦ -(∑ i, (∂[i] (a i j)) y)))
    htrace hdrift helliptic.1 _ hreg heq hpointwise hpositive
  intro x _ v
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc]
    using hquad x (mem_univ x) (fun i ↦ v i)

/-- A symmetric divergence-form operator with the stated interior coefficient regularity
has a normalized first Dirichlet eigenfunction that is strictly positive in a connected
bounded open domain. Its eigenvalue is the attained least `L²` Rayleigh quotient.
The conclusion concerns interior values; no regularity of the boundary is assumed. -/
theorem exists_pos_first_weakDivergence_eigenfunction
    (hn : 0 < n) (hΩ : IsOpen Ω) (hbounded : Bornology.IsBounded Ω)
    (hconn : IsPreconnected Ω) (hne : Ω.Nonempty)
    (m : ℕ) (hm : 3 + n / 2 ≤ m + 2)
    (A0 : Fin n → Fin n → DerivLp n ∞ univ)
    (a : Fin n → Fin n → ℝ^n → ℝ) (C : Fin n → Fin n → NNReal)
    (ha : ∀ i j, LipschitzWith (C i j) (a i j))
    (hA0 : ∀ i j, (A0 i j : ℝ^n → ℝ) =ᵐ[volume] a i j)
    (haC1 : ∀ i j x, x ∈ Ω → ContDiffAt ℝ 1 (a i j) x)
    {alpha : ℝ} (helliptic : AEUniformlyElliptic (n := n) (Ω := univ) A0 alpha)
    (A : Fin n → Fin n → W^{m + 1,∞}(Ω))
    (hA : ∀ i j, (wkpBaseCoordinateCLM (A i j) : ℝ^n → ℝ)
      =ᵐ[domainMeasure n Ω]
        (restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A0 i j) : ℝ^n → ℝ))
    (hsymm : AESymmetricCoefficient (n := n) (Ω := Ω)
      (fun i j ↦ restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A0 i j))) :
    ∃ (lambda : ℝ) (u : H¹₀(Ω)) (f : ℝ^n → ℝ),
      0 < lambda ∧ ‖baseCoordCLM u‖ = 1 ∧
      IsWeakDivergenceSolution
        (fun i j ↦ restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A0 i j))
        (lambda • baseCoordCLM u) u ∧
      (baseCoordCLM u : ℝ^n → ℝ) =ᵐ[domainMeasure n Ω] f ∧
      (∀ x ∈ Ω, ContDiffAt ℝ 2 f x) ∧
      (∀ x ∈ Ω, EllipticMaximum.matrixOperator (fun y i j ↦ a i j y)
        (fun y ↦ WithLp.toLp 2 (fun j ↦ -(∑ i, (∂[i] (a i j)) y)))
        (fun _ ↦ 0) f x = lambda * f x) ∧
      (∀ x ∈ Ω, 0 < f x) ∧
      IsLeast ((fun v : H¹₀(Ω) ↦
        variableCoeffForm (multiplicationCoefficientOperator
          (fun i j ↦ restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A0 i j)))
          v v / ‖baseCoordCLM v‖ ^ 2) '' {v | v ≠ 0}) lambda := by
  let B : Fin n → Fin n → DerivLp n ∞ Ω :=
    fun i j ↦ restrictDerivLp (n := n) (p := ∞) (subset_univ Ω) (A0 i j)
  have hB : AEUniformlyElliptic B alpha := by
    refine ⟨helliptic.1, ?_⟩
    have hrepAll : ∀ᵐ x ∂domainMeasure n Ω, ∀ i j, B i j x = A0 i j x :=
      ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦
        restrictDerivLp_apply_ae (subset_univ Ω) (A0 i j)
    have hglobal : ∀ᵐ x ∂volume, ∀ ξ : Fin n → ℝ,
        alpha * ∑ i : Fin n, ξ i * ξ i ≤
          ∑ i : Fin n, ∑ j : Fin n, A0 i j x * ξ j * ξ i := by
      simpa only [domainMeasure, Measure.restrict_univ] using helliptic.2
    filter_upwards [ae_restrict_of_ae hglobal, hrepAll] with x hx hr
    simpa only [hr] using hx
  obtain ⟨lambda, u, hpos, hnorm, hnonneg, heig, hweak, hleast⟩ :=
    exists_nonnegative_first_weakDivergence_eigenfunction hn hΩ hbounded hne B hB hsymm
  have hune : h10SubtypeL u ≠ 0 := by
    intro hu
    apply heig.1
    exact Subtype.ext hu
  obtain ⟨f, hrep, hreg, heq, hfpos⟩ :=
    hweak.toInterior.exists_pos_eigenfunction_representative hn hconn m hm
      A0 a C ha hA0 haC1 helliptic A hA hune hnonneg
  exact ⟨lambda, u, f, hpos, hnorm, hweak, hrep, hreg, heq, hfpos, hleast⟩

end SobolevSpace.GraphSpace
